> module Test where

Local imports
=============

> import Instr
> import qualified Interleaving
> import qualified Spec
> import qualified Axiomatic.SC
> import qualified Axiomatic.TSO
> import qualified Axiomatic.PSO
> import qualified Axiomatic.RMO
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
>     SA SC     -> testEquiv Axiomatic.SC.isSC
>                            Operational.isSC
>     NonSA SC  -> testEquiv Axiomatic.SC.isSCMinusSA
>                            Interleaving.isSCMinusSA
>     SA TSO    -> testEquiv Axiomatic.TSO.isTSO
>                            Operational.isTSO
>     NonSA TSO -> testEquiv Axiomatic.TSO.isTSOMinusSA
>                            Interleaving.isTSOMinusSA
>     SA PSO    -> testEquiv Axiomatic.PSO.isPSO
>                            Operational.isPSO
>     NonSA PSO -> testEquiv Axiomatic.PSO.isPSOMinusSA
>                            Interleaving.isPSOMinusSA
>     SA RMO    -> testEquiv Axiomatic.RMO.isRMO
>                            Operational.isRMO
>     NonSA RMO -> testEquiv Axiomatic.RMO.isRMOMinusSA
>                            Interleaving.isRMOMinusSA
