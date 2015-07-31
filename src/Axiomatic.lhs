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

> module Axiomatic where

> import Instr
> import Constraint
> import qualified LocalOrder as PO
> import qualified Data.Map as M
> import Data.Maybe
> import DataFlow

Solvers
=======

> isSC :: [[Instr]] -> Bool
> isSC = yices . constraintsSC

> isTSO :: [[Instr]] -> Bool
> isTSO = yices . constraintsTSO

> isPSO :: [[Instr]] -> Bool
> isPSO = yices . constraintsPSO

> isRMO :: [[Instr]] -> Bool
> isRMO = yices . constraintsRMO

Reads-from and write-order edges (version 1)
============================================

> rfwo :: [[Instr]] -> [Constraint]
> rfwo trace = concatMap cons loads
>   where
>     loads = filter (\x -> op x == LOAD) t
>
>     cons x
>       | val x == Data 0 = [ x :-> s' | s' <- others ]
>       | otherwise       = [ s :-> x  | tid s /= tid x ]
>                        ++ [ p :-> s  | p <- prev, tid s /= tid x ]
>                        ++ [ x :-> n  | n <- next, tid n /= tid x ]
>                        ++ [ (s' :-> s) :|:
>                             (x  :-> s')
>                           | s' <- others, uid s /= uid s',
>                                           tid s /= tid s' ]
>       where
>         s      = storeOf ! (val x, addr x)
>         stores = M.findWithDefault [] (addr x) storesTo
>         others = [ s' | s' <- stores, tid x /= tid s' ]
>         prev   = maybeToList $ M.lookup (uid x) prevLocalStore
>         next   = maybeToList $ M.lookup (uid s) nextLocalStore
>
>     t              = concat trace
>     storesTo       = computeStoresTo t
>     storeOf        = computeStoreOf t
>     prevLocalStore = computePrevLocalStore t
>     nextLocalStore = computeNextLocalStore t

Reads-from and write-order edges (version 2)
============================================

> rf :: [[Instr]] -> [Constraint]
> rf trace = concatMap cons loads
>   where
>     loads = filter (\x -> op x == LOAD) t
>
>     cons x
>       | val x == Data 0 = [ x :-> s' | s' <- others ]
>       | otherwise       = [ s :-> x  | tid s /= tid x ]
>                        ++ [ p :-> s  | p <- prev, tid s /= tid x ]
>                        ++ [ x :-> n  | n <- next, tid n /= tid x ]
>       where
>         s      = storeOf ! (val x, addr x)
>         stores = M.findWithDefault [] (addr x) storesTo
>         others = [ s' | s' <- stores, tid x /= tid s' ]
>         prev   = maybeToList $ M.lookup (uid x) prevLocalStore
>         next   = maybeToList $ M.lookup (uid s) nextLocalStore
>
>     t              = concat trace
>     storesTo       = computeFirstStoresTo t
>     storeOf        = computeStoreOf t
>     prevLocalStore = computePrevLocalStore t
>     nextLocalStore = computeNextLocalStore t

> rfwo2 :: ([[Instr]] -> [Constraint]) -> [[Instr]] -> [Constraint]
> rfwo2 po trace = cs ++ concatMap cons loads
>   where
>     cs    = po trace ++ rf trace
>     loads = filter (\x -> op x == LOAD) t
>
>     cons x
>       | val x == Data 0 = []
>       | otherwise       = [ (s' :-> s) :|: (x :-> s')
>                           | s' <- stores, uid s /= uid s',
>                             tid s /= tid s', tid s' /= tid x ]
>       where
>         s      = storeOf ! (val x, addr x)
>         stores = getUnorderedWrites pwo s x
>
>     pwo      = analyseWriteOrder cs
>     t        = concat trace
>     storeOf  = computeStoreOf t
>     storesTo = computeStoresTo t

SC constraints
==============

Given a trace, generate constraints for sequential consistency.

> constraintsSC :: [[Instr]] -> [Constraint]
> constraintsSC = rfwo2 PO.poSC
> --constraintsSC = PO.poSC \/ rfwo

TSO constraints
===============

Given a trace, generate constraints for TSO.

> constraintsTSO :: [[Instr]] -> [Constraint]
> constraintsTSO = rfwo2 PO.poTSO
> --constraintsTSO = PO.poTSO \/ rfwo

PSO constraints
===============

Given a trace, generate constraints for PSO.

> constraintsPSO :: [[Instr]] -> [Constraint]
> constraintsPSO = rfwo2 PO.poPSO
> --constraintsPSO = PO.poPSO \/ rfwo 

RMO constraints
===============

Given a trace, generate constraints for PSO.

> constraintsRMO :: [[Instr]] -> [Constraint]
> constraintsRMO = rfwo2 PO.poRMO
> --constraintsRMO = PO.poRMO \/ rfwo
