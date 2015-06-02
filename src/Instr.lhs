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

> module Instr where

> import qualified Data.Map as M
> import Test.QuickCheck
> import Data.List
> import Control.Applicative

Syntax of instruction traces
============================

Unique instruction identifiers
------------------------------

> data InstrId = Id Int
>   deriving (Eq, Ord)

Thread identifiers
------------------

> type ThreadId = Int

Opcodes
-------

> data Opcode =
>     LOAD
>   | STORE
>   | SYNC
>   | LLSC
>   deriving (Eq, Show)

Addresses
---------

> data Addr = Addr Int
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
>     uid    :: InstrId
>   , tid    :: ThreadId
>   , op     :: Opcode
>   , addr   :: Addr
>   , val    :: Data
>   , atomic :: Bool
>   , val2   :: Data
>   , stamp  :: Timestamp
>   }

Timestamps
==========

A timestamp is a (start-time,end-time) pair:

> type Timestamp = (Maybe Int, Maybe Int)

> noStamp :: Timestamp
> noStamp = (Nothing, Nothing)

Pretty printer
==============

> newtype Trace = Trace [[Instr]]

> instance Show InstrId where
>   show (Id a) = show a

> instance Show Addr where
>   show (Addr a) = show a

> instance Show Data where
>   show (Data d) = show d

> instance Show Instr where
>   show instr = show (tid instr) ++ ": " ++ str ++ "\n"
>     where
>       str =
>         case op instr of
>           LOAD  -> "v" ++ show (addr instr)
>                 ++ (if atomic instr then " =={LL} " else " == ")
>                 ++ show (val instr)
>           STORE -> "v" ++ show (addr instr)
>                 ++ (if atomic instr then " :={SC} " else " := ")
>                 ++ show (val instr)
>           SYNC  -> "sync"

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

For all load instructions, find the last value stored to that load's
address on that load's thread.

> computePrevLocalStore :: [Instr] -> M.Map InstrId Instr
> computePrevLocalStore instrs = step instrs M.empty
>   where
>     step [] m = M.empty
>     step (instr:instrs) m =
>       case op instr of
>         STORE -> step instrs (M.insert (tid instr, addr instr) instr m)
>         LOAD  -> case M.lookup (tid instr, addr instr) m of
>                    Nothing -> step instrs m
>                    Just i  -> M.insert (uid instr) i (step instrs m)
>         SYNC  -> step instrs m

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

Given an instruction trace, return all addresses used.

> addrs :: [Instr] -> [Addr]
> addrs = nub . map addr

Instruction trace generators
============================

The desired properties of the generated trace.

> data TraceOptions =
>   TraceOptions {
>     totalInstrs     :: Int
>   , totalThreads    :: Int
>   , maxVals         :: Int
>   , maxAddrs        :: Int
>   , maxSyncs        :: Int
>   , maxLLSCs        :: Int
>   , assumeLocalCons :: Bool  -- Assume local consistency
>   , onlySC          :: Bool  -- Only generate sequentially consistent traces
>   }

The state of the generator is a tuple containing:

  * number of instructions generated so far
  * number of syncs generated so far
  * a mapping from address to values that have been written to that
    address and by which thread
  * a list of instructions generated so far

> type GenState = (Int, Int, Int, M.Map Addr [(ThreadId, Data)], [Instr])

> initialState :: GenState
> initialState = (0, 0, 0, M.empty, [])

Random trace generator.

> genTrace :: TraceOptions -> Gen [[Instr]]
> genTrace opts = threads <$> step initialState
>   where
>     pick xs = oneof (map return xs)
>
>     genLoad ll threadId a (n, nsync, nllsc, m, instrs) =
>       do let stores   = M.findWithDefault [] a m ++ initial
>          let local    = take 1 [v | (t, v) <- stores, t == threadId]
>          let possible = local ++ [v | (t, v) <- stores, t /= threadId]
>          v <- pick (if assumeLocalCons opts then possible else map snd stores)
>          let instr = Instr {
>                        uid    = Id n
>                      , tid    = threadId
>                      , op     = LOAD
>                      , addr   = a
>                      , val    = if onlySC opts then snd (head stores) else v
>                      , val2   = error "val2 not defined"
>                      , atomic = ll
>                      , stamp  = noStamp
>                      }
>          let n' = if ll then n else n+1
>          return (n', nsync, if ll then nllsc+1 else nllsc, m, instr:instrs)
>       where
>         initial = [(threadId, Data 0)]
>
>     possibleVals a m = dataVals \\ usedVals
>       where
>         dataVals = map Data [1 .. maxVals opts - 1]
>         usedVals = map snd (M.findWithDefault [] a m)
>
>     genStore sc threadId a (n, nsync, nllsc, m, instrs) =
>       do let vs = possibleVals a m
>          case null vs of
>            True -> return Nothing
>            False ->
>              do v <- pick vs
>                 let instr = Instr {
>                               uid    = Id n
>                             , tid    = threadId
>                             , op     = STORE
>                             , addr   = a
>                             , val    = v
>                             , atomic = sc
>                             , val2   = error "val2 not defined"
>                             , stamp  = noStamp
>                             }
>                 let m' = M.insertWith (++) a [(threadId, v)] m
>                 return $ Just (n+1, nsync, nllsc, m', instr:instrs)
>       where
>         dataVals = map Data [1 .. maxVals opts - 1]
>
>     genLoadOrStore threadId state =
>       do a <- Addr <$> choose (0, maxAddrs opts - 1)
>          load <- genLoad False threadId a state
>          b    <- pick [False, True]
>          case b of
>            True  -> return load
>            False -> do maybeStore <- genStore False threadId a state
>                        case maybeStore of
>                          Nothing -> return load
>                          Just s  -> return s
>
>     step state@(n, nsync, nllsc, m, instrs)
>       | n == totalInstrs opts = return (reverse instrs)
>       | otherwise =
>           do threadId <- choose (0, totalThreads opts - 1)
>
>              -- Insert SYNC?
>              let insertSync = not (null [i | i <- instrs, tid i == threadId])
>                            && nsync < maxSyncs opts
>                            && n+2 <= totalInstrs opts
>              let syncChance = totalInstrs opts `div` (2*(maxSyncs opts + 1))
>              sync <- pick ([insertSync] ++ replicate syncChance False)
>              let syncInstr = Instr {
>                                uid    = Id n
>                              , tid    = threadId
>                              , op     = SYNC
>                              , addr   = error "addr SYNC = _|_"
>                              , val    = error "val SYNC = _|_"
>                              , val2   = error "val2 not defined"
>                              , stamp  = noStamp
>                              , atomic = False
>                              }
>
>              -- Insert LL/SC?
>              a <- Addr <$> choose (0, maxAddrs opts - 1)
>              let insertLLSC = not sync && nllsc < maxLLSCs opts
>                            && n+1 <= totalInstrs opts
>                            && not (null (possibleVals a m))
>              let llscChance = totalInstrs opts `div` (2*(maxLLSCs opts + 1))
>              llsc <- pick ([insertLLSC] ++ replicate llscChance False)
>
>              case llsc of
>                True  ->
>                  genLoad True threadId a state >>=
>                    genStore True threadId a >>=
>                      (\(Just s) -> step s)
>                False ->
>                  let state' = if   sync
>                               then (n+1, nsync+1, nllsc, m, syncInstr:instrs)
>                               else (n, nsync, nllsc, m, instrs)
>                   in genLoadOrStore threadId state' >>= step

Generator for small traces.

> smallTraceOpts = 
>   TraceOptions {
>     totalInstrs     = 7
>   , totalThreads    = 2
>   , maxVals         = 3
>   , maxAddrs        = 3
>   , maxSyncs        = 1
>   , maxLLSCs        = 1
>   , assumeLocalCons = True
>   , onlySC          = False
>   }

> smallTraces :: Gen Trace
> smallTraces = Trace <$> genTrace smallTraceOpts
