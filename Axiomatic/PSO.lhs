> module Axiomatic.PSO where

> import Instr
> import Constraint
> import Axiomatic.RelaxSA
> import qualified Data.Map as M

Program-order edges
===================

> po :: [[Instr]] -> [Constraint]
> po = concatMap (thread M.empty [] [])
>   where
>     thread stores load sync instrs =
>       case instrs of
>         []        -> []
>         me:instrs ->
>             case op me of
>               LOAD  -> [s --> me | s <- sync, null load]
>                     ++ [l --> me | l <- load]
>                     ++ thread stores [me] [] instrs
>               STORE -> [s --> me | s <- sync, null load && null prev]
>                     ++ [l --> me | l <- load]
>                     ++ [s --> me | s <- prev]
>                     ++ thread stores' load sync instrs
>                        where
>                          prev    = M.findWithDefault [] (addr me) stores
>                          stores' = M.insert (addr me) [me] stores
>               SYNC  -> [s --> me | s <- sync, null load]
>                     ++ [l --> me | l <- load]
>                     ++ [s --> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty [] [me] instrs

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
>                        ++ [ p --> s | p <- prev, tid s /= tid x ]
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

PSO constraints
===============

Given a trace, generate constraints for PSO.

> constraintsPSO :: [[Instr]] -> [Constraint]
> constraintsPSO = po \/ rfwo

> constraintsPSOMinusSA :: [[Instr]] -> [Constraint]
> constraintsPSOMinusSA = relaxSA po rfwo

Solver
======

> isPSO :: [[Instr]] -> Bool
> isPSO = yices . constraintsPSO

> isPSOMinusSA :: [[Instr]] -> Bool
> isPSOMinusSA = yices . constraintsPSOMinusSA
