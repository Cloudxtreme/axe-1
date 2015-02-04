> module Axiomatic.SC where

> import Instr
> import Constraint
> import Axiomatic.RelaxSA
> import qualified Data.Map as M

Program-order edges
===================

> po :: [[Instr]] -> [Constraint]
> po = concatMap thread
>   where
>     thread []       = []
>     thread [x]      = []
>     thread (x:y:zs) = (uid x :-> uid y) : thread (y:zs)

Reads-from and write-order edges
================================

> rfwo :: [[Instr]] -> [Constraint]
> rfwo trace = concatMap cons loads
>   where
>     loads = filter (\x -> op x == LOAD) (concat trace)
> 
>     cons x
>       | val x == Data 0 = [ uid x :-> uid s' | s' <- stores ]
>       | otherwise       = [ uid s :-> uid x ]
>                        ++ [ (uid s' :-> uid s) :|:
>                             (uid x  :-> uid s')
>                           | s' <- others ]
>       where
>         s      = storeOf ! (val x, addr x)
>         stores = [ s' | s' <- M.findWithDefault [] (addr x) storesTo ]
>         others = [ s' | s' <- stores, uid s /= uid s' ]
>
>     storesTo = computeStoresTo (concat trace)
>     storeOf  = computeStoreOf (concat trace)

SC constraints
==============

Given a trace, generate constraints for sequential consistency.

> constraintsSC :: [[Instr]] -> [Constraint]
> constraintsSC = po \/ rfwo

> constraintsSCMinusSA :: [[Instr]] -> [Constraint]
> constraintsSCMinusSA = relaxSA po rfwo

Solvers
=======

> isSC :: [[Instr]] -> Bool
> isSC = yices . constraintsSC

> isSCMinusSA :: [[Instr]] -> Bool
> isSCMinusSA = yices . constraintsSCMinusSA
