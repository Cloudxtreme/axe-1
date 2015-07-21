Copyright 2015 Matthew Naylor
All rights reserved.

This software was developed by SRI International and the University of
Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-10-C-0237
("CTSRD"), as part of the DARPA CRASH research programme.

This software was developed by SRI International and the University of
Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-11-C-0249
("MRC2"), as part of the DARPA MRC research programme.

@BERI_LICENSE_HEADER_START@

Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
license agreements.  See the NOTICE file distributed with this work for
additional information regarding copyright ownership.  BERI licenses this
file to you under the BERI Hardware-Software License, Version 1.0 (the
"License"); you may not use this file except in compliance with the
License.  You may obtain a copy of the License at:

  http://www.beri-open-systems.org/legal/license-1-0.txt

Unless required by applicable law or agreed to in writing, Work distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.  See the License for the
specific language governing permissions and limitations under the License.

@BERI_LICENSE_HEADER_END@

> module Operational where

Imports
=======

> import Instr
> import Data.List
> import qualified Data.Map as M
> import qualified Data.Set as S
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
>   } deriving (Eq, Ord)

Non-deterministic state monad:

> type Visited = S.Set State

> newtype ND a = ND { runND :: Visited -> State -> (Visited, [(State, a)]) }

> instance Monad ND where
>   return a = ND $ \v s -> (v, [(s, a)])
>   m >>= f  = ND $ \v s ->
>     let (v' , xs) = runND m v s
>         (v'', ys) = mapAccumL (\v (s, a) -> runND (f a) v s) v' xs
>     in  (v'', concat ys)

> instance MonadPlus ND where
>   mzero       = ND $ \v s -> (v, [])
>   x `mplus` y = ND $ \v s -> 
>     let (v' , xs) = runND x v s
>         (v'', ys) = runND y v' s
>     in  (v'', xs ++ ys)

Monadic routines:

> getState :: ND State
> getState = ND $ \v s -> (v, [(s, s)])

> putState :: State -> ND ()
> putState s = ND $ \v _ -> (v, [(s, ())])

> getVisited :: ND Visited
> getVisited = ND $ \v s -> (v, [(s, v)])

> putVisited :: Visited -> ND ()
> putVisited v = ND $ \_ s -> (v, [(s, ())])

> fetchInstr :: ThreadId -> ND Instr
> fetchInstr t =
>   do s <- getState
>      case instrs s M.! t of
>        [] -> mzero
>        ld:st:is
>          | op ld == LOAD  && atomic ld
>         && op st == STORE && atomic st
>         -> do putState (s { instrs = M.insert t is (instrs s) })
>               return (ld { op = LLSC, val2 = val st })
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
>   head ([ Just (if op i == STORE then val i else val2 i)
>         | i <- b, op i == STORE || op i == LLSC
>                 , addr i == a] ++ [Nothing])

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
>       | (op x == STORE || op x == LLSC) &&
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

> load :: (Addr, Data) -> Buffer -> ND ()
> load (a, v) b =
>   do s <- getState
>      case lookupWrite a b of
>        Nothing -> a `contains` v
>        Just x  -> guard (x == v)

> anyThreadId :: ND ThreadId
> anyThreadId =
>   do s <- getState
>      let ts = M.keys (buffers s)
>      msum (map return ts)

> whileNotDone :: ND () -> ND ()
> whileNotDone m =
>   do s <- getState
>      v <- getVisited
>      let done = all null (M.elems (instrs s))
>              && all null (M.elems (buffers s))
>      if done then return () else
>        case s `S.member` v of
>          False -> putVisited (S.insert s v) >> m >> whileNotDone m
>          True  -> mzero

> run :: ND () -> [[Instr]] -> Bool
> run m trace = not $ null $ snd $ runND (whileNotDone m) S.empty initialState
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
>        SYNC  -> return ()
>        LLSC  -> addr i `contains` val i
>              >> writeMem (addr i, val2 i)

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
>        LOAD  -> load (addr i, val i) b
>        STORE -> setBuffer t (i:b)
>        SYNC  -> guard (null b)
>        LLSC  -> do guard (null b)
>                    addr i `contains` val i
>                    writeMem (addr i, val2 i)

> propagateTSO :: ND ()
> propagateTSO =
>   do t <- anyThreadId
>      w <- deqBuffer t
>      writeMem (addr w, val w)

PSO
===

> isPSO :: [[Instr]] -> Bool
> isPSO = run (fetchExecutePSO `mplus` propagatePSO)

> fetchExecutePSO :: ND ()
> fetchExecutePSO = 
>   do t <- anyThreadId
>      i <- fetchInstr t
>      b <- getBuffer t
>      case op i of
>        LOAD  -> load (addr i, val i) b
>        STORE -> setBuffer t (i:b)
>        SYNC  -> guard (null b)
>        LLSC  -> do guard (null [s | s <- b, addr s == addr i])
>                    addr i `contains` val i
>                    writeMem (addr i, val2 i)

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
>        SYNC  -> guard (null b)
>        _     -> setBuffer t (i:b)

> propagateRMO :: ND ()
> propagateRMO =
>   do t <- anyThreadId
>      (pre, i, post) <- extractBuffer' t
>      case op i of
>        LOAD  -> load (addr i, val i) post
>        STORE -> writeMem (addr i, val i)
>        LLSC  -> do addr i `contains` val i
>                    writeMem (addr i, val2 i)
