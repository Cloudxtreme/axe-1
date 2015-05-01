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
>         []        -> []
>         me:instrs ->
>             case op me of
>               LOAD  -> [s --> me | s <- sync, null load]
>                     ++ [l --> me | l <- load]
>                     ++ thread store [me] sync instrs
>               STORE -> [s --> me | s <- sync, null load && null store]
>                     ++ [l --> me | l <- load]
>                     ++ [s --> me | s <- store]
>                     ++ thread [me] load sync instrs
>               SYNC  -> [s --> me | s <- sync, null load && null store]
>                     ++ [l --> me | l <- load]
>                     ++ [s --> me | s <- store]
>                     ++ thread [] [] [me] instrs

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
>         prev   = case M.lookup (uid x) localRF of
>                    Nothing -> []
>                    Just p  -> [p]
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
