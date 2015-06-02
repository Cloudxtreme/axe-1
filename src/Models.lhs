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

> module Models where

Imports
=======

> import Instr
> import qualified Axiomatic
> import qualified Data.Map as M
> import qualified Spec as Spec
> import qualified Operational
> import Data.Char

Models
======

Each model has a Store Atomic and Non Store Atomic variant.

> data Model =
>     SC
>   | TSO
>   | PSO
>   | RMO

Function to display a model:

> instance Show Model where
>   show SC  = "sc"
>   show TSO = "tso"
>   show PSO = "pso"
>   show RMO = "rmo"

Function to parse a model.

> stringToModel :: String -> Model
> stringToModel s =
>   case map toLower s of
>     "sc"     -> SC
>     "tso"    -> TSO
>     "pso"    -> PSO
>     "rmo"    -> RMO
>     other    -> error $ "Unknown model '" ++ s ++ "'"

Check if a trace satisfies a given constraint model.

> satisfies :: [[Instr]] -> Model -> Bool
> satisfies trace model = locallyConsistent trace && ok
>   where
>     ok = case model of
>            SC  -> Axiomatic.isSC trace
>            TSO -> Axiomatic.isTSO trace
>            PSO -> Axiomatic.isPSO trace
>            RMO -> Axiomatic.isRMO trace

Check if a trace satisfies a given operational model.

> satisfiesOperational :: [[Instr]] -> Model -> Bool
> satisfiesOperational trace model = locallyConsistent trace && ok
>   where
>     ok = case model of
>            SC  -> Operational.isSC trace
>            TSO -> Operational.isTSO trace
>            PSO -> Operational.isPSO trace
>            RMO -> Operational.isRMO trace

Local-consistency
=================

There are some properties that traces must satisfy under any memory
model:

  * If a variable is not shared then any reads of that variable must
    read the latest value written locally.

  * If a read does not return the latest value written locally, there
    must exist a write of that value on another thread.

Together, these properties are referred to as "local consistency".
Traces from the random trace generator are always locally consistent,
however externally-read traces may not be.

> locallyConsistent :: [[Instr]] -> Bool
> locallyConsistent trace = all (lc M.empty) trace
>   where
>     storesTo = computeStoresTo (concat trace)
> 
>     lc m [] = True
>     lc m (instr:instrs) =
>       case op instr of
>         LOAD  -> (  M.findWithDefault (Data 0) (addr instr) m == val instr
>                  || val instr `elem` external )
>               && lc m instrs
>         STORE -> lc (M.insert (addr instr) (val instr) m) instrs
>         SYNC  -> lc m instrs
>       where
>         external = [val i | i <- M.findWithDefault [] (addr instr) storesTo
>                           , tid i /= tid instr]
