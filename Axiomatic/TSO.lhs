> module Axiomatic.TSO where

> import Instr
> import Constraint
> import Axiomatic.RelaxSA
> import qualified Data.Map as M

Program-order edges
===================

> po :: [[Instr]] -> [Constraint]
> po = concatMap (thread [] [] [])
>   where
>     thread store load sync instrs =
>       case instrs of
>         []           -> []
>         instr:instrs ->
>           let me = uid instr in
>             case op instr of
>               LOAD  -> [uid s :-> me | s <- sync]
>                     ++ [uid l :-> me | l <- load]
>                     ++ thread store [instr] [] instrs
>               STORE -> [uid s :-> me | s <- sync]
>                     ++ [uid l :-> me | l <- load]
>                     ++ [uid s :-> me | s <- store]
>                     ++ thread [instr] load sync instrs
>               SYNC  -> [uid s :-> me | s <- sync]
>                     ++ [uid l :-> me | l <- load]
>                     ++ [uid s :-> me | s <- store]
>                     ++ thread [] [] [instr] instrs

Reads-from and write-order edges
================================

> rfwo :: [[Instr]] -> [Constraint]
> rfwo trace = concatMap cons loads
>   where
>     loads = filter (\x -> op x == LOAD) (concat trace)
>
>     cons x
>       | val x == Data 0 = [ uid x :-> uid s' | s' <- others ]
>                        ++ if not (null prev) then [ Fail ] else []
>       | otherwise       = [ uid s :-> uid x  | tid s /= tid x ]
>                        ++ [ p :-> uid s | p <- prev, tid s /= tid x ]
>                        ++ [ (uid s' :-> uid s) :|:
>                             (uid x  :-> uid s')
>                           | s' <- others, uid s /= uid s' ]
>       where
>         s      = storeOf ! (val x, addr x)
>         stores = [ s' | s' <- M.findWithDefault [] (addr x) storesTo]
>         others = [ s' | s' <- stores, tid x /= tid s' ]
>         prev   = case M.lookup (uid x) localRF of
>                    Nothing -> []
>                    Just p  -> [uid p]
>
>     storesTo = computeStoresTo (concat trace)
>     storeOf  = computeStoreOf (concat trace)
>     localRF  = computeLocalReadsFrom (concat trace)

TSO constraints
===============

Given a trace, generate constraints for TSO.

> constraintsTSO :: [[Instr]] -> [Constraint]
> constraintsTSO = po \/ rfwo

> constraintsTSOMinusSA :: [[Instr]] -> [Constraint]
> constraintsTSOMinusSA = relaxSA po rfwo

Solver
======

> isTSO :: [[Instr]] -> Bool
> isTSO = yices . constraintsTSO

> isTSOMinusSA :: [[Instr]] -> Bool
> isTSOMinusSA = yices . constraintsTSOMinusSA
