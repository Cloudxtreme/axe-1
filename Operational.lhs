> module Operational where

Imports
=======

> import Instr
> import Data.List
> import qualified Data.Map as M
> import Control.Monad

State
=====

Shared memory:

> type Mem = M.Map Addr Data

Buffer:

> type Buffer = [Instr]

> data State =
>   State {
>     instrs  :: M.Map ThreadId [Instr]
>   , buffers :: M.Map ThreadId Buffer
>   , mem     :: Mem
>   }

Non-deterministic state monad:

> newtype ND a = ND { runND :: State -> [(State, a)] }

> instance Monad ND where
>   return a = ND $ \s -> [(s, a)]
>   m >>= f  = ND $ \s ->
>     concat [ runND (f a) s'
>            | (s', a) <- runND m s ]

> instance MonadPlus ND where
>   mzero       = ND $ \s -> []
>   x `mplus` y = ND $ \s -> runND x s ++ runND y s

Monadic routines:

> getState :: ND State
> getState = ND $ \s -> [(s, s)]

> putState :: State -> ND ()
> putState s = ND $ \_ -> [(s, ())]

> fetchInstr :: ThreadId -> ND Instr
> fetchInstr t =
>   do s <- getState
>      case instrs s M.! t of
>        []   -> mzero
>        i:is -> do putState (s { instrs = M.insert t is (instrs s) })
>                   return i

> getBuffer :: ThreadId -> ND Buffer
> getBuffer t =
>   do s <- getState
>      return (buffers s M.! t)

> setBuffer :: ThreadId -> Buffer -> ND ()
> setBuffer t b =
>   do s <- getState
>      putState (s { buffers = M.insert t b (buffers s) })

> lookupWrite :: Addr -> Buffer -> Maybe Data
> lookupWrite a b =
>   head ([Just (val i) | i <- b, op i == STORE, addr i == a] ++ [Nothing])

> deqBuffer :: ThreadId -> ND Instr
> deqBuffer t =
>   do b <- getBuffer t
>      case reverse b of
>        []     -> mzero
>        w:rest -> setBuffer t (reverse rest) >> return w

> extractBuffer :: ThreadId -> ND Instr
> extractBuffer t =
>   do (pre, x, post) <- extractBuffer' t
>      return x

> extractBuffer' :: ThreadId -> ND ([Instr], Instr, [Instr])
> extractBuffer' t =
>   do b <- getBuffer t
>      (xs, i, ys) <- pick [] (reverse b)
>      let pre  = reverse ys
>      let post = reverse xs
>      setBuffer t (pre ++ post) >> return (pre, i, post)
>   where
>     pick pre []                    = mzero
>     pick pre (x:xs)
>       | op x == STORE &&
>         addr x `elem` map addr pre = pick (pre ++ [x]) xs
>       | otherwise                  = return (pre, x, xs)
>                              `mplus` pick (pre ++ [x]) xs

> contains :: Addr -> Data -> ND ()
> a `contains` d =
>   do s <- getState
>      guard (M.findWithDefault (Data 0) a (mem s) == d)

> writeMem :: (Addr, Data) -> ND ()
> writeMem (a, v) =
>   do s <- getState
>      putState (s { mem = M.insert a v (mem s) })

> anyThreadId :: ND ThreadId
> anyThreadId =
>   do s <- getState
>      let ts = M.keys (buffers s)
>      msum (map return ts)

> whileNotDone :: ND () -> ND ()
> whileNotDone m =
>   do s <- getState
>      let done = all null (M.elems (instrs s))
>              && all null (M.elems (buffers s))
>      if done then return () else m >> whileNotDone m

> run :: ND () -> [[Instr]] -> Bool
> run m trace = not $ null $ runND (whileNotDone m) initialState
>   where
>     instrs       = concat trace
>     tids         = threadIds instrs
>     instrsOf t   = [i | i <- instrs, tid i == t]
>     initialState =
>       State {
>         instrs       = M.fromList [(t, instrsOf t) | t <- tids]
>       , buffers      = M.fromList [(t, []) | t <- tids]
>       , mem          = M.empty
>       }

SC
==

> isSC :: [[Instr]] -> Bool
> isSC = run fetchExecute

> fetchExecute :: ND ()
> fetchExecute =
>   do t <- anyThreadId
>      i <- fetchInstr t
>      case op i of
>        LOAD  -> addr i `contains` val i
>        STORE -> writeMem (addr i, val i)
>        iYNC  -> return ()

TSO
===

> isTSO :: [[Instr]] -> Bool
> isTSO = run (fetchExecuteTSO `mplus` propagateTSO)

> fetchExecuteTSO :: ND ()
> fetchExecuteTSO = 
>   do t <- anyThreadId
>      i <- fetchInstr t
>      b <- getBuffer t
>      case op i of
>        LOAD  -> case lookupWrite (addr i) b of
>                   Nothing -> addr i `contains` val i
>                   Just x  -> guard (x == val i)
>        STORE -> setBuffer t (i:b)
>        SYNC  -> guard (null b)

> propagateTSO :: ND ()
> propagateTSO =
>   do t <- anyThreadId
>      w <- deqBuffer t
>      writeMem (addr w, val w)

PSO
===

> isPSO :: [[Instr]] -> Bool
> isPSO = run (fetchExecuteTSO `mplus` propagatePSO)

> propagatePSO :: ND ()
> propagatePSO =
>   do t <- anyThreadId
>      w <- extractBuffer t
>      writeMem (addr w, val w)

RMO
===

> isRMO :: [[Instr]] -> Bool
> isRMO = run (fetchExecuteRMO `mplus` propagateRMO)

> fetchExecuteRMO :: ND ()
> fetchExecuteRMO = 
>   do t <- anyThreadId
>      i <- fetchInstr t
>      b <- getBuffer t
>      case op i of
>        LOAD  -> setBuffer t (i:b)
>        STORE -> setBuffer t (i:b)
>        SYNC  -> guard (null b)

> propagateRMO :: ND ()
> propagateRMO =
>   do t <- anyThreadId
>      (pre, i, post) <- extractBuffer' t
>      case op i of
>        LOAD  -> case lookupWrite (addr i) post of
>                   Nothing -> addr i `contains` val i
>                   Just x  -> guard (x == val i)
>        STORE -> writeMem (addr i, val i)
