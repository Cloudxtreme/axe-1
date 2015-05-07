> module Axiomatic.RMO where

> import Instr
> import Constraint
> import Axiomatic.RelaxSA
> import qualified Data.Map as M

Program-order edges
===================

> po :: [[Instr]] -> [Constraint]
> po = concatMap (thread M.empty M.empty [])
>   where
>     thread stores loads sync instrs =
>       case instrs of
>         []        -> []
>         me:instrs ->
>             case op me of
>               LOAD  -> [s --> me | s <- sync]
>                     ++ thread stores loads' sync instrs
>                     where
>                        loads' = M.insertWith (++) (addr me) [me] loads
>               STORE -> [s --> me | s <- sync, null prevS]
>                     ++ [l --> me | l <- prevL]
>                     ++ [s --> me | s <- prevS]
>                     ++ thread stores' loads' sync instrs
>                     where
>                        prevS   = M.findWithDefault [] (addr me) stores
>                        prevL   = M.findWithDefault [] (addr me) loads
>                        stores' = M.insert (addr me) [me] stores
>                        loads'  = M.insert (addr me) [] loads
>               SYNC  -> [s --> me | s <- sync]
>                     ++ [l --> me | l <- concat (M.elems loads)]
>                     ++ [s --> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty M.empty [me] instrs

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

RMO constraints
===============

Given a trace, generate constraints for RMO.

> constraintsRMO :: [[Instr]] -> [Constraint]
> constraintsRMO = po \/ rfwo

> constraintsRMOMinusSA :: [[Instr]] -> [Constraint]
> constraintsRMOMinusSA = relaxSA po rfwo

Solver
======

> isRMO :: [[Instr]] -> Bool
> isRMO = yices . constraintsRMO

> isRMOMinusSA :: [[Instr]] -> Bool
> isRMOMinusSA = yices . constraintsRMOMinusSA
