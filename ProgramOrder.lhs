> module ProgramOrder where

Imports
=======

> import Instr
> import qualified Data.Map as M

Program Order edges
===================

Happens before edges

> type Edge = (Instr, Instr)

> (-->) :: Instr -> Instr -> Edge
> a --> b = (a, b)

Sequential Consistency.

> poSC :: [[Instr]] -> [Edge]
> poSC trace = concatMap thread trace
>   where
>     thread []       = []
>     thread [x]      = []
>     thread (x:y:zs) = (x --> y) : thread (y:zs)

Total Store Order.

> poTSO :: [[Instr]] -> [Edge]
> poTSO trace = concatMap (thread [] [] []) trace
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
>                     ++ [l --> me | l <- load, uid l /= uid me]
>                     ++ [s --> me | s <- store]
>                     ++ thread [me] load sync instrs
>               SYNC  -> [s --> me | s <- sync, null load && null store]
>                     ++ [l --> me | l <- load]
>                     ++ [s --> me | s <- store]
>                     ++ thread [] [] [me] instrs

Partial Store Order.

> poPSO :: [[Instr]] -> [Edge]
> poPSO trace = concatMap (thread M.empty [] []) trace
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
>                     ++ [l --> me | l <- load, uid l /= uid me]
>                     ++ [s --> me | s <- prev]
>                     ++ thread stores' load sync instrs
>                        where
>                          prev    = M.findWithDefault [] (addr me) stores
>                          stores' = M.insert (addr me) [me] stores
>               SYNC  -> [s --> me | s <- sync, null load]
>                     ++ [l --> me | l <- load]
>                     ++ [s --> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty [] [me] instrs

Relaxed Memory Order.

> poRMO :: [[Instr]] -> [Edge]
> poRMO trace = concatMap (thread M.empty M.empty []) trace
>  where
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
>                     ++ [l --> me | l <- prevL, uid l /= uid me]
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
