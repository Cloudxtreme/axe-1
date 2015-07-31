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

Overview
========

Data-flow analysis that, given a set of "happens-before" constraints
between memory operations, computes, for each operation x, the latest
store on each thread that is known to preceed x.  (Similarly, if
applied in reverse, it can determine the first store on each
thread known to succeed x).

> module DataFlow (
>   PWO,
>   analyseWriteOrder,
>   getUnorderedWrites,
> ) where

Imports
=======

> import Instr
> import Constraint
> import Data.Maybe
> import qualified Data.Map as M
> import qualified Data.Set as S
> import qualified Data.Array as A

Types
=====

The set of "happens-before" constraints can be viewed as a graph, with
memory operations as nodes.  The data that flows between the nodes is
captured by the following type.  It contains the latest (earliest)
store to some address by some thread known to preceed (succeed)
the node.

> type Info = M.Map (ThreadId, Addr) InstrId

The result of the analysis is, for each operation x, the latest
(earliest) store on each thread known to preceed (succeed) x.
Note that this is subset of the information stored in the Info type:
for each node, it contains only preceeding operations involving the
same address as that node.

> type Result = M.Map InstrId (M.Map ThreadId InstrId)

State of the analysis:

> data State =
>   State {
>     nodes    :: S.Set InstrId
>   , tids     :: S.Set ThreadId
>   , outEdges :: M.Map InstrId (S.Set InstrId)
>   , inCount  :: M.Map InstrId Int
>   , countIn  :: S.Set (Int, InstrId)
>   , instrs   :: M.Map InstrId Instr
>   , info     :: M.Map InstrId Info
>   , result   :: Result
>   } deriving Show

A function to determine if an instruction comes after another in
program-order using the instruction identifier.  In this module, we
assume that if two instructions x and y are in program order on the
same thread, then uid x < uid y.

> type LaterThan = InstrId -> InstrId -> Bool

Initial state
=============

Initial state of the analysis.

> initState :: [Constraint] -> State
> initState cs =
>   State {
>     nodes    = allNodes
>   , tids     = threads
>   , outEdges = foldl (\m (x, s) -> M.insertWith S.union x s m) M.empty
>                   [(uid x, S.singleton (uid y)) | (x :-> y) <- cs]
>   , inCount  = M.fromList [(x, S.size s) | (x, s) <- M.toList incoming]
>   , countIn  = S.fromList [(S.size s, x) | (x, s) <- M.toList incoming]
>   , instrs   = M.fromList $ concat
>                  [[(uid x, x), (uid y, y)] | (x :-> y) <- cs]
>   , info     = M.fromList [(x, M.empty) | x <- S.toList allNodes]
>   , result   = M.empty
>   }
>   where
>     incoming = foldl (\m (x, s) -> M.insertWith S.union x s m)
>                      (M.fromList [(x, S.empty) | x <- S.toList allNodes])
>                      [(uid x, S.singleton (uid y)) | (y :-> x) <- cs]
>     allNodes = S.fromList $ concat [[uid x, uid y] | (x :-> y) <- cs]
>     threads  = S.fromList $ concat [[tid x, tid y] | (x :-> y) <- cs]

Step function
=============

> step :: LaterThan -> State -> State
> step laterThan s =
>   decrInEdges (S.toList out) $ s {
>     inCount = M.delete node (inCount s)
>   , countIn = countIn'
>   , info    = M.delete node $ M.unionWith
>                 (mergeInfo laterThan)
>                 (M.fromList [ (x, mergeInfo laterThan info' (info s M.! x))
>                             | x <- S.toList out])
>                 (info s)
>   , result  = addResult (S.toList $ tids s) instr
>                         (info s M.! uid instr) (result s)
>   }
>   where
>     ((_, node), countIn') = S.deleteFindMin (countIn s)
>     instr                 = instrs s M.! node
>     out                   = M.findWithDefault S.empty node (outEdges s)
>     info'                 = addToInfo laterThan instr (info s M.! node)

> decrInEdges :: [InstrId] -> State -> State
> decrInEdges xs s =
>   s {
>     inCount = foldr (M.adjust pred) (inCount s) xs
>   , countIn = foldr decr (countIn s) xs
>   }
>   where
>     decr x
>       | x `M.member` inCount s = S.insert (pred n, x) . S.delete (n, x)
>       | otherwise = id
>       where n = inCount s M.! x

> addToInfo :: LaterThan -> Instr -> Info -> Info
> addToInfo laterThan instr info
>   | op instr == STORE =
>       case M.lookup (tid instr, addr instr) info of
>         Nothing -> addTo info
>         Just x  -> if uid instr `laterThan` x then addTo info else info
>   | otherwise = info
>   where
>     addTo = M.insert (tid instr, addr instr) (uid instr)

> mergeInfo :: LaterThan -> Info -> Info -> Info
> mergeInfo laterThan = M.unionWith merge
>   where merge a b = if a `laterThan` b then a else b

> addResult :: [ThreadId] -> Instr -> Info -> Result -> Result
> addResult tids instr info r
>   | op instr /= SYNC = M.insert (uid instr) m r
>   | otherwise        = r
>   where m = M.fromList [ (t, info M.! (t, addr instr))
>                        | t <- tids, M.member (t, addr instr) info ]

Analysis
========

> analyse :: LaterThan -> [Constraint] -> Result
> analyse laterThan cs = run (initState cs)
>   where
>     run s = if S.null (countIn s) then result s
>             else run (step laterThan s)

Interface
=========

Partial write order.

> data PWO =
>   PWO {
>     instrMap  :: M.Map InstrId Instr
>   , thids     :: [ThreadId]
>   , indexMap  :: M.Map InstrId Int
>   , uidArrays :: M.Map ThreadId (A.Array Int InstrId)
>   , preceeds  :: Result
>   , succeeds  :: Result
>   }

> analyseWriteOrder :: [Constraint] -> PWO
> analyseWriteOrder cs =
>   PWO {
>     instrMap  = instrs
>   , thids     = tids
>   , indexMap  = indexes
>   , uidArrays = arrays
>   , preceeds  = analyse (>) cs
>   , succeeds  = analyse (<) [y :-> x | (x :-> y) <- cs]
>   }
>   where
>     instrs     = M.fromList $
>                    concat [[(uid x, x), (uid y, y)] | (x :-> y) <- cs]
>     tids       = S.toList $ S.fromList $ map tid $ M.elems instrs
>     uidsOn t   = toArray $ S.toAscList $
>                    S.fromList [uid i | i <- M.elems instrs
>                                      , tid i == t, op i == STORE || atomic i]
>     toArray xs = A.array (0, length xs - 1) (zipWith (,) [0..] xs)
>     arrays     = M.fromList [(t, uidsOn t) | t <- tids]
>     indexes    = M.fromList [(id, index) |
>                                ar <- M.elems arrays,
>                                (index, id) <- A.assocs ar]

> getUnorderedWrites :: PWO -> Instr -> Instr -> [Instr]
> getUnorderedWrites pwo write read = 
>   concat [ extract t (latest t) (earliest t)
>          | t <- thids pwo ]
>   where
>     loBound t = fst $ A.bounds (uidArrays pwo M.! t)
>     hiBound t = snd $ A.bounds (uidArrays pwo M.! t)
>  
>     latest t = fromMaybe (loBound t) $
>       do m <- M.lookup (uid write) (preceeds pwo)
>          i <- M.lookup t m
>          return $ (indexMap pwo M.! i) + 1
>
>     earliest t = fromMaybe (hiBound t) $
>       do m <- M.lookup (uid read) (succeeds pwo)
>          i <- M.lookup t m
>          return $ (indexMap pwo M.! i) - 1
>
>     extract t lo hi = [i | index <- [lo..hi]
>                          , let id = ar A.! index
>                          , let i = instrMap pwo M.! id
>                          , addr i == addr write
>                          , op i == STORE || atomic i ]
>       where ar = uidArrays pwo M.! t
