> module Axiomatic.TSO where

> import Instr
> import Constraint
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

Reads-from and coherence edges
==============================

> rfco :: [[Instr]] -> [Constraint]
> rfco trace = concatMap cons loads
>   where
>     loads = filter (\x -> op x == LOAD) (concat trace)
> 
>     cons x
>       | val x == Data 0 = [ uid x :-> uid s' | s' <- others ]
>       | otherwise       = [ uid s :-> uid x  | s <- extStore ]
>                        ++ [ p :-> uid s | p <- prev ]
>                        ++ [ (uid s' :-> uid s) :|:
>                             (uid x  :-> uid s')
>                           | s' <- others, uid s /= uid s' ]
>                        --   | s <- extStore, s' <- others, uid s /= uid s' ]
>       where
>         s        = storeOf ! (val x, addr x)
>         extStore = [ s  | tid s /= tid x ]
>         stores   = [ s' | s' <- M.findWithDefault [] (addr x) storesTo ]
>         others   = [ s' | s' <- stores, tid s' /= tid x ]
>         prev     = case [ uid s' | s' <- stores
>                                  , tid s' == tid x
>                                  , uid s' < uid x
>                                  , uid s' /= uid s ] of
>                      [] -> []
>                      xs -> [maximum xs]
>
>     storesTo = computeStoresTo (concat trace)
>     storeOf  = computeStoreOf (concat trace)

TSO constraints
===============

Given a trace, generate constraints for TSO.

> constraintsTSO :: [[Instr]] -> [Constraint]
> constraintsTSO = po \/ rfco

Solver
======

> isTSO :: [[Instr]] -> Bool
> isTSO = yices . constraintsTSO
