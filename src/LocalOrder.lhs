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

> module LocalOrder where

Imports
=======

> import Instr
> import Constraint
> import qualified Data.Map as M

Program Order edges
===================

Sequential Consistency.

> poSC :: [[Instr]] -> [Constraint]
> poSC trace = concatMap thread trace
>   where
>     thread []       = []
>     thread [x]      = []
>     thread (x:y:zs) = [x :-> y | uid x /= uid y]  ++ thread (y:zs)

Total Store Order.

> poTSO :: [[Instr]] -> [Constraint]
> poTSO trace = concatMap (thread [] [] []) trace
>   where
>     thread store load sync instrs =
>       case instrs of
>         []        -> []
>         me:instrs ->
>             case op me of
>               LOAD  -> [s :-> me | s <- sync, null load]
>                     ++ [l :-> me | l <- load]
>                     ++ thread store [me] sync instrs
>               STORE -> [s :-> me | s <- sync, null load && null store]
>                     ++ [l :-> me | l <- load, uid l /= uid me]
>                     ++ [s :-> me | s <- store]
>                     ++ thread [me] load sync instrs
>               SYNC  -> [s :-> me | s <- sync, null load && null store]
>                     ++ [l :-> me | l <- load]
>                     ++ [s :-> me | s <- store]
>                     ++ thread [] [] [me] instrs

Partial Store Order.

> poPSO :: [[Instr]] -> [Constraint]
> poPSO trace = concatMap (thread M.empty [] []) trace
>   where
>     thread stores load sync instrs =
>       case instrs of
>         []        -> []
>         me:instrs ->
>             case op me of
>               LOAD  -> [s :-> me | s <- sync, null load]
>                     ++ [l :-> me | l <- load]
>                     ++ thread stores [me] [] instrs
>               STORE -> [s :-> me | s <- sync, null load && null prev]
>                     ++ [l :-> me | l <- load, uid l /= uid me]
>                     ++ [s :-> me | s <- prev]
>                     ++ thread stores' load sync instrs
>                        where
>                          prev    = M.findWithDefault [] (addr me) stores
>                          stores' = M.insert (addr me) [me] stores
>               SYNC  -> [s :-> me | s <- sync, null load]
>                     ++ [l :-> me | l <- load]
>                     ++ [s :-> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty [] [me] instrs

Relaxed Memory Order.

> poRMO :: [[Instr]] -> [Constraint]
> poRMO trace = concatMap (thread M.empty M.empty []) trace
>  where
>     thread stores loads sync instrs =
>       case instrs of
>         []        -> []
>         me:instrs ->
>             case op me of
>               LOAD  -> [s :-> me | s <- sync]
>                     ++ thread stores loads' sync instrs
>                     where
>                        loads' = M.insertWith (++) (addr me) [me] loads
>               STORE -> [s :-> me | s <- sync, null prevS]
>                     ++ [l :-> me | l <- prevL, uid l /= uid me]
>                     ++ [s :-> me | s <- prevS]
>                     ++ thread stores' loads' sync instrs
>                     where
>                        prevS   = M.findWithDefault [] (addr me) stores
>                        prevL   = M.findWithDefault [] (addr me) loads
>                        stores' = M.insert (addr me) [me] stores
>                        loads'  = M.insert (addr me) [] loads
>               SYNC  -> [s :-> me | s <- sync]
>                     ++ [l :-> me | l <- concat (M.elems loads)]
>                     ++ [s :-> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty M.empty [me] instrs
