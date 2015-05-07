> module Test where

Local imports
=============

> import Instr
> import qualified Spec
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
