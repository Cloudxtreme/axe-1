> module Main where

> import Test
> import Test.QuickCheck

> main :: IO ()
> main = quickCheckWith (numTestsIs 1000000) testTSO
