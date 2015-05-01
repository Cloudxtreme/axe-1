> module Axiomatic.SC where

> import Instr
> import Constraint
> import Axiomatic.RelaxSA
> import qualified Data.Map as M

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

Program-order edges
===================

> po :: [[Instr]] -> [Constraint]
> po = concatMap thread
>   where
>     thread []       = []
>     thread [x]      = []
>     thread (x:y:zs) = (x --> y) : thread (y:zs)

Reads-from and write-order edges
================================

> rfwo :: [[Instr]] -> [Constraint]
> rfwo trace = concatMap cons loads
>   where
>     loads = filter (\x -> op x == LOAD) (concat trace)
> 
>     cons me
>       | val me == Data 0 = [ me --> s' | s' <- stores ]
>       | otherwise        = [ s --> me ]
>                         ++ [ (s' --> s ) :|:
>                              (me --> s')
>                            | s' <- others ]
>       where
>         s      = storeOf ! (val me, addr me)
>         stores = M.findWithDefault [] (addr me) storesTo
>         others = [ s' | s' <- stores, uid s /= uid s' ]
>
>     storesTo = computeStoresTo (concat trace)
>     storeOf  = computeStoreOf (concat trace)
