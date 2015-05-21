> module Axiomatic where

> import Instr
> import Constraint
> import qualified ProgramOrder as PO
> import qualified Data.Map as M

Solvers
=======

> isSC :: [[Instr]] -> Bool
> isSC = yices . constraintsSC

> isTSO :: [[Instr]] -> Bool
> isTSO = yices . constraintsTSO

> isPSO :: [[Instr]] -> Bool
> isPSO = yices . constraintsPSO

> isRMO :: [[Instr]] -> Bool
> isRMO = yices . constraintsRMO

Reads-from and write-order edges
================================

> rfwo :: [[Instr]] -> [Constraint]
> rfwo trace = concatMap cons loads
>   where
>     loads = filter (\x -> op x == LOAD) (concat trace)
>
>     cons x
>       | val x == Data 0 = [ x --> s' | s' <- others ]
>                        ++ if not (null prev) then [ Fail ] else []
>       | otherwise       = [ s --> x  | tid s /= tid x ]
>                        ++ [ p --> s  | p <- prev, tid s /= tid x ]
>                        ++ [ (s' --> s) :|:
>                             (x  --> s')
>                           | s' <- others, uid s /= uid s' ]
>       where
>         s      = storeOf ! (val x, addr x)
>         stores = M.findWithDefault [] (addr x) storesTo
>         others = [ s' | s' <- stores, tid x /= tid s' ]
>         prev   = case M.lookup (uid x) prevLocalStore of
>                    Nothing -> []
>                    Just p  -> [p]
>
>     storesTo       = computeStoresTo (concat trace)
>     storeOf        = computeStoreOf (concat trace)
>     prevLocalStore = computePrevLocalStore (concat trace)

SC constraints
==============

Given a trace, generate constraints for sequential consistency.

> constraintsSC :: [[Instr]] -> [Constraint]
> constraintsSC = poSC \/ rfwo

Program-order edges.

> poSC :: [[Instr]] -> [Constraint]
> poSC = map constraint . PO.poSC

TSO constraints
===============

Given a trace, generate constraints for TSO.

> constraintsTSO :: [[Instr]] -> [Constraint]
> constraintsTSO = poTSO \/ rfwo

Program-order edges.

> poTSO :: [[Instr]] -> [Constraint]
> poTSO = map constraint . PO.poTSO

PSO constraints
===============

Given a trace, generate constraints for PSO.

> constraintsPSO :: [[Instr]] -> [Constraint]
> constraintsPSO = poPSO \/ rfwo 

Program-order edges.

> poPSO :: [[Instr]] -> [Constraint]
> poPSO = map constraint . PO.poPSO

RMO constraints
===============

Given a trace, generate constraints for PSO.

> constraintsRMO :: [[Instr]] -> [Constraint]
> constraintsRMO = poRMO \/ rfwo

Program-order edges.

> poRMO :: [[Instr]] -> [Constraint]
> poRMO = map constraint . PO.poRMO

Convert edges to constraints
============================

> constraint :: PO.Edge -> Constraint
> constraint (a, b) = uid a :-> uid b
