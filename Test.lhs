> module Test where

Local imports
=============

> import Instr
> import qualified Interleaving
> import qualified Axiomatic.SC
> import qualified Axiomatic.TSO
> import qualified Axiomatic.PSO

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
>                            Interleaving.isSC
>     NonSA SC  -> testEquiv Axiomatic.SC.isSCMinusSA
>                            Interleaving.isSCMinusSA
>     SA TSO    -> testEquiv Axiomatic.TSO.isTSO
>                            Interleaving.isTSO
>     NonSA TSO -> testEquiv Axiomatic.TSO.isTSOMinusSA
>                            Interleaving.isTSOMinusSA
>     SA PSO    -> testEquiv Axiomatic.PSO.isPSO
>                            Interleaving.isPSO
>     NonSA PSO -> testEquiv Axiomatic.PSO.isPSOMinusSA
>                            Interleaving.isPSOMinusSA
