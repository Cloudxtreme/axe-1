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
>         []           -> []
>         instr:instrs ->
>           let me = uid instr in
>             case op instr of
>               LOAD  -> [uid s :-> me | s <- sync]
>                     ++ [uid l :-> me | l <- load]
>                     ++ thread stores [instr] [] instrs
>               STORE -> [uid s :-> me | s <- sync, null prev]
>                     ++ [uid l :-> me | l <- load]
>                     ++ [uid s :-> me | s <- prev]
>                     ++ thread stores' load sync instrs
>                        where
>                          prev    = M.findWithDefault [] (addr instr) stores
>                          stores' = M.insert (addr instr) [instr] stores
>               SYNC  -> [uid s :-> me | s <- sync]
>                     ++ [uid l :-> me | l <- load]
>                     ++ [uid s :-> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty [] [instr] instrs

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
