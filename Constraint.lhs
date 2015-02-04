> module Constraint where

> import Instr
> import Data.List
> import System.Process
> import System.IO.Unsafe
> import Debug.Trace

Types
=====

> data Constraint =
>     InstrId :-> InstrId
>   | Constraint :|: Constraint
>   | Constraint :<=> Constraint
>   | Fail

Combinators
===========

Union two list generators, useful for unioning constraint sets.

> (\/) :: (a -> [b]) -> (a -> [b]) -> (a -> [b])
> (f \/ g) x = f x ++ g x

Yices backend
=============

Convert constraint to Yices format.

> toYices :: [Constraint] -> String
> toYices cs =
>      varDecls
>   ++ unlines (map assert cs)
>   ++ "(check)\n"
>   where
>     var v = "v" ++ show v
>
>     vars (x :-> y)  = [var x, var y]
>     vars (c :|: d)  = vars c ++ vars d
>     vars (c :<=> d) = vars c ++ vars d
>     vars Fail       = []
>
>     translate (x :-> y) = "(< " ++ var x ++ " " ++ var y ++ ")"
>     translate (c :|: d) =
>       "(or " ++ translate c ++ " " ++ translate d ++ ")"
>     translate (c :<=> d) =
>       "(= " ++ translate c ++ " " ++ translate d ++ ")"
>     translate Fail = "false"
>
>     assert c = "(assert " ++ translate c ++ ")"
>
>     varDecls = unlines [ "(define " ++ v ++ " :: int)"
>                        | v <- nub (concatMap vars cs) ]

Check constraints using Yices.

> yicesCheck :: [Constraint] -> IO Bool
> yicesCheck cs =
>   do out <- readProcess "yices" [] (toYices cs)
>      return $ if   take 3 out == "sat"
>               then True
>               else (if   take 5 out == "unsat"
>                     then False
>                     else error "Error communicating with yices")

Pure vesion of the above for convenience in property-testing.

> {-# NOINLINE yices #-} 
> yices :: [Constraint] -> Bool
> yices cs = unsafePerformIO (yicesCheck cs)
