> module Main where

> import Test
> import Test.QuickCheck

> import Interleaving

> main :: IO ()
> main = quickCheckWith (withNumTests 1000000) testTSOMinusSA
