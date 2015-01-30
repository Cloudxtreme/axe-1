> module Instr where

> import qualified Data.Map as M
> import Test.QuickCheck
> import Data.List
> import Control.Applicative

Syntax of instruction traces
============================

Unique instruction identifiers
------------------------------

> type InstrId = Int

Thread identifiers
------------------

> type ThreadId = Int

Opcodes
-------

> data Opcode =
>     LOAD
>   | STORE
>   | SYNC
>   deriving (Eq, Show)

Addresses
---------

> newtype Addr = Addr Int
>   deriving (Eq, Ord)

Data
----

> newtype Data = Data Int
>   deriving (Eq, Ord)

Memory instructions
-------------------

These are not instructions of a program, but of a trace.  In
particular, LOAD instructions contain the value that was read.
In the case of SYNC, the address and data fields are unused.

> data Instr =
>   Instr {
>     uid  :: InstrId
>   , tid  :: ThreadId
>   , op   :: Opcode
>   , addr :: Addr
>   , val  :: Data
>   }

Pretty printer
==============

> newtype Trace = Trace [[Instr]]

> instance Show Addr where
>   show (Addr a) = show a

> instance Show Data where
>   show (Data d) = show d

> instance Show Instr where
>   show instr = show (tid instr) ++ ": " ++ str ++ "\n"
>     where
>       str =
>         case op instr of
>           LOAD  -> "v" ++ show (addr instr) ++ " == " ++ show (val instr)
>           STORE -> "v" ++ show (addr instr) ++ " := " ++ show (val instr)
>           SYNC  -> "SYNC"

> instance Show Trace where
>   show (Trace t) = helper t
>     where
>       helper [] = ""
>       helper (x:xs) = concatMap show x ++ "\n" ++ helper xs

Functions on sets of instructions 
=================================

For all a find all stores to address a.

> computeStoresTo :: [Instr] -> M.Map Addr [Instr]
> computeStoresTo instrs =
>   case instrs of
>     []     -> M.empty
>     (i:is) -> if   op i == STORE
>               then M.insertWith (++) (addr i) [i] m
>               else m
>       where m = computeStoresTo is

For all (v,a) find store of value v to address a.

> computeStoreOf :: [Instr] -> M.Map (Data, Addr) Instr
> computeStoreOf instrs =
>   case instrs of
>     []     -> M.empty
>     (i:is) -> if   op i == STORE
>               then M.insert (val i, addr i) i m
>               else m
>       where m = computeStoreOf is

Lookup function for above mappings.

> (!) :: (Show a, Ord a) => M.Map a b -> a -> b
> m ! a =
>   case M.lookup a m of
>     Nothing -> error ("Error in '!': no key " ++ show a)
>     Just b  -> b

Given an instruction trace, return all the thread ids

> threadIds :: [Instr] -> [ThreadId]
> threadIds = nub . map tid

Given an instruction trace, return a sub-trace for each thread.

> threads :: [Instr] -> [[Instr]]
> threads trace = [ [i | i <- trace, tid i == t] | t <- threadIds trace]

Instruction trace generators
============================

The desired properties of the generated trace.

> data TraceOptions =
>   TraceOptions {
>     totalInstrs   :: Int
>   , totalThreads  :: Int
>   , maxVals       :: Int
>   , maxAddrs      :: Int
>   , maxSyncs      :: Int
>   , assumeLocalCO :: Bool  -- Assume local coherence order
>   }

The state of the generator is a tuple containing:

  * number of instructions generated so far
  * number of syncs generated so far
  * a mapping from address to values that have been written to that
    address and by which thread
  * a list of instructions generated so far

> type GenState = (Int, Int, M.Map Addr [(ThreadId, Data)], [Instr])

> initialState :: GenState
> initialState = (0, 0, M.empty, [])

Random trace generator.

> genTrace :: TraceOptions -> Gen [[Instr]]
> genTrace opts = threads <$> step initialState
>   where
>     pick xs = oneof (map return xs)
>
>     genLoad threadId (n, nsync, m, instrs) =
>       do a <- Addr <$> choose (0, maxAddrs opts - 1)
>          let stores   = M.findWithDefault [] a m ++ [(threadId, Data 0)]
>          let local    = take 1 [v | (t, v) <- stores, t == threadId]
>          let possible = local ++ [v | (t, v) <- stores, t /= threadId]
>          v <- pick (if assumeLocalCO opts then possible else map snd stores)
>          let instr = Instr {
>                        uid  = n
>                      , tid  = threadId
>                      , op   = LOAD
>                      , addr = a
>                      , val  = v
>                      }
>          return (n+1, nsync, m, instr:instrs)
>       where
>
>     genStore threadId (n, nsync, m, instrs) =
>       do a <- Addr <$> choose (0, maxAddrs opts - 1)
>          let vs = dataVals \\ (map snd $ M.findWithDefault [] a m)
>          case null vs of
>            True -> return Nothing
>            False ->
>              do v <- pick vs
>                 let instr = Instr {
>                               uid  = n
>                             , tid  = threadId
>                             , op   = STORE
>                             , addr = a
>                             , val  = v
>                             }
>                 let m' = M.insertWith (++) a [(threadId, v)] m
>                 return $ Just (n+1, nsync, m', instr:instrs)
>       where
>         dataVals = map Data [1 .. maxVals opts - 1]
>
>     genLoadOrStore threadId state =
>       do load <- genLoad threadId state
>          maybeStore <- genStore threadId state
>          case maybeStore of
>            Nothing -> return load
>            Just s  -> return s
>
>     step state@(n, nsync, m, instrs)
>       | n == totalInstrs opts = return (reverse instrs)
>       | otherwise =
>           do threadId <- choose (0, totalThreads opts - 1)
>              let insertSync = not (null [i | i <- instrs, tid i == threadId])
>                            && nsync < maxSyncs opts
>                            && n+2 <= totalInstrs opts
>              sync <- pick [False, insertSync]
>              let syncInstr = Instr {
>                                uid  = n
>                              , tid  = threadId
>                              , op   = SYNC
>                              , addr = error "addr SYNC = _|_"
>                              , val  = error "val SYNC = _|_"
>                              }
>              let state' = if   sync
>                           then (n+1, nsync+1, m, syncInstr:instrs)
>                           else (n, nsync, m, instrs)
>              genLoadOrStore threadId state' >>= step

Generator for small traces:

> smallTraces :: Gen [[Instr]]
> smallTraces =
>   genTrace $ TraceOptions {
>   --  totalInstrs   = 8
>   --, totalThreads  = 4
>     totalInstrs   = 8
>   , totalThreads  = 2
>   , maxVals       = 3
>   , maxAddrs      = 3
>   , maxSyncs      = 0
>   , assumeLocalCO = True
>   }
