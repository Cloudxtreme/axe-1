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

> module Test where

Local imports
=============

> import Instr
> import qualified Axiomatic
> import qualified Operational

Haskell platform imports
========================

> import Test.QuickCheck
> import Control.Applicative
> import Models

Equivalance tests between axiomatic and operational models
==========================================================

> withNumTests :: Int -> Args
> withNumTests n = stdArgs { maxSuccess = n }

> testEquiv f g =
>   forAll smallTraces $ \(Trace t) ->
>     let a = f t
>         b = g t
>     in  classify a "true" $ a == b

> test model =
>   case model of
>     SC  -> testEquiv Axiomatic.isSC
>                      Operational.isSC
>     TSO -> testEquiv Axiomatic.isTSO
>                      Operational.isTSO
>     PSO -> testEquiv Axiomatic.isPSO
>                      Operational.isPSO
>     RMO -> testEquiv Axiomatic.isRMO
>                      Operational.isRMO
