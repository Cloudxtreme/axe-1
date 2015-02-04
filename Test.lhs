> module Test where

Local imports
=============

> import Instr
> import qualified Interleaving
> import qualified Axiomatic.SC
> import qualified Axiomatic.TSO

Haskell platform imports
========================

> import Test.QuickCheck
> import Control.Applicative
> import Debug.Trace

Equivalance tests between axiomatic and operational models
==========================================================

> withNumTests :: Int -> Args
> withNumTests n = stdArgs { maxSuccess = n }

> testEquiv f g =
>   forAll smallTraces $ \(Trace t) ->
>     let a = f t
>         b = g t
>     in  classify a "true" $ a == b

> testSC =
>   testEquiv Axiomatic.SC.isSC
>             Interleaving.isSC

> testSCMinusSA =
>   testEquiv Axiomatic.SC.isSCMinusSA
>             Interleaving.isSCMinusSA

> testTSO =
>   testEquiv Axiomatic.TSO.isTSO
>             Interleaving.isTSO

> testTSOMinusSA =
>   testEquiv Axiomatic.TSO.isTSOMinusSA
>             Interleaving.isTSOMinusSA
