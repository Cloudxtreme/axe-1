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
>         []           -> []
>         instr:instrs ->
>           let me = uid instr in
>             case op instr of
>               LOAD  -> [uid s :-> me | s <- sync]
>                     ++ thread stores loads' sync instrs
>                     where
>                        loads' = M.insertWith (++) (addr instr) [instr] loads
>               STORE -> [uid s :-> me | s <- sync, null prevS]
>                     ++ [uid l :-> me | l <- prevL]
>                     ++ [uid s :-> me | s <- prevS]
>                     ++ thread stores' loads' sync instrs
>                     where
>                        prevS   = M.findWithDefault [] (addr instr) stores
>                        prevL   = M.findWithDefault [] (addr instr) loads
>                        stores' = M.insert (addr instr) [instr] stores
>                        loads'  = M.insert (addr instr) [] loads
>               SYNC  -> [uid s :-> me | s <- sync]
>                     ++ [uid l :-> me | l <- concat (M.elems loads)]
>                     ++ [uid s :-> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty M.empty [instr] instrs

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
