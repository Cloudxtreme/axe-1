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

Tests
=====

> numTestsIs :: Int -> Args
> numTestsIs n = stdArgs { maxSuccess = n }

> testSC =
>   forAll smallTraces $ \t ->
>     let a = Axiomatic.SC.isSC t
>         b = Interleaving.isSC t
>     in classify a "true" $ a == b

> testTSO =
>   forAll (Trace <$> smallTraces) $ \(Trace t) ->
>     let a = Axiomatic.TSO.isTSO t
>         b = Interleaving.isTSO t
>     in classify a "true" $ a == a
