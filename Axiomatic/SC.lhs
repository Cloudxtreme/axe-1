> module Axiomatic.SC where

> import Instr
> import Constraint
> import qualified Data.Map as M

Program-order edges
===================

> po :: [[Instr]] -> [Constraint]
> po = concatMap thread
>   where
>     thread []       = []
>     thread [x]      = []
>     thread (x:y:zs) = (uid x :-> uid y) : thread (y:zs)

Reads-from and coherence edges
==============================

> rfco :: [[Instr]] -> [Constraint]
> rfco trace = concatMap cons loads
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
> constraintsSC = po \/ rfco

Solver
======

> isSC :: [[Instr]] -> Bool
> isSC = yices . constraintsSC
