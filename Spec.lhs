Specifications of each memory model

> module Spec where

> import Instr
> import qualified Data.Map as M
> import qualified Data.Set as S
> import Data.List (union)
> import Data.Maybe

Intruction dependence graphs
============================

Instruction dependence graphs.

> type Graph = ([Instr], Edges InstrId)

Keep track of incoming and outgoing edges of each instruction.

> data Edges a =
>   Edges {
>     incoming :: M.Map a [a]
>   , outgoing :: M.Map a [a]
>   }
>   deriving Show

Empty set of edges.

> noEdges :: Edges a
> noEdges =
>   Edges {
>      incoming = M.empty
>    , outgoing = M.empty
>    }

All desitinations from a vertex.

> from :: Ord a => a -> Edges a -> [a]
> from x es = M.findWithDefault [] x (outgoing es)

All sources to a vertex.

> to :: Ord a => a -> Edges a -> [a]
> to x es = M.findWithDefault [] x (incoming es)

Insert an edge.

> insert :: Ord a => (a, a) -> Edges a -> Edges a
> insert (src, dst) es =
>   Edges {
>     incoming = M.insertWith union dst [src] (incoming es)
>   , outgoing = M.insertWith union src [dst] (outgoing es)
>   }

Remove an edge.

> remove :: Ord a => (a, a) -> Edges a -> Edges a
> remove (src, dst) es =
>   Edges {
>     incoming = let vs = [v | v <- to dst es, v /= src]
>                in  M.insert dst vs (incoming es)
>   , outgoing = let vs = [v | v <- from src es, v /= dst]
>                in  M.insert src vs (outgoing es)
>   }

Return all edges.

> edges :: Ord a => Edges a -> [(a, a)]
> edges es = concat [[(x, y) | y <- ys] | (x, ys) <- M.assocs (outgoing es)]

Find all vertices with no incoming edges.

> noIncoming :: Graph -> [Instr]
> noIncoming (vs, es) =
>   [v | v <- vs, null (to (uid v) es)]

Convert a trace and a set of dependencies to a graph.

> graph :: [[Instr]] -> [(InstrId, InstrId)] -> Graph
> graph trace es = (concat trace, foldr insert noEdges es)

Topilogical sort
================

Find all topological sorts.  Returns [] if graph contains cycles.

> sorts :: Graph -> [[Instr]]
> sorts g@(vs, es) = findAll (noIncoming g, es)
>   where
>     instrs = M.fromList [(uid v, v) | v <- vs]
>
>     findAll (s, es)
>       | null s    = if null (edges es) then [[]] else []
>       | otherwise =
>         [ v:rest
>         | (v, s') <- extract s
>         , rest <- findAll $ update v (from (uid v) es) (s', es)
>         ]
> 
>     update v dests (s, es) =
>       case dests of
>         []   -> (s, es)
>         d:ds -> let es' = remove (uid v, d) es
>                     s'  = [instrs M.! d | null (to d es')] ++ s
>                 in update v ds (s', es')

Extract an element from a list non-deterministically.

> extract :: [a] -> [(a, [a])]
> extract xs = ex [] xs
>   where
>     ex acc xs =
>       case xs of
>         []   -> []
>         x:ys -> (x, reverse acc ++ ys) : ex (x:acc) ys

Program Order edges
===================

> (-->) :: a -> b -> (a, b)
> a --> b = (a, b)

Sequential Consistency.

> poSC :: [[Instr]] -> Graph
> poSC trace = graph trace (concatMap thread trace)
>   where
>     thread []       = []
>     thread [x]      = []
>     thread (x:y:zs) = (uid x, uid y) : thread (y:zs)

Total Store Order.

> poTSO :: [[Instr]] -> Graph
> poTSO trace =
>   graph trace (concatMap (thread [] [] []) trace)
>   where
>     thread store load sync instrs =
>       case instrs of
>         []           -> []
>         instr:instrs ->
>           let me = uid instr in
>             case op instr of
>               LOAD  -> [uid s --> me | s <- sync, null load]
>                     ++ [uid l --> me | l <- load]
>                     ++ thread store [instr] sync instrs
>               STORE -> [uid s --> me | s <- sync, null load && null store]
>                     ++ [uid l --> me | l <- load]
>                     ++ [uid s --> me | s <- store]
>                     ++ thread [instr] load sync instrs
>               SYNC  -> [uid s --> me | s <- sync, null load && null store]
>                     ++ [uid l --> me | l <- load]
>                     ++ [uid s --> me | s <- store]
>                     ++ thread [] [] [instr] instrs

Partial Store Order.

> poPSO :: [[Instr]] -> Graph
> poPSO trace =
>   graph trace (concatMap (thread M.empty [] []) trace)
>   where
>     thread stores load sync instrs =
>       case instrs of
>         []           -> []
>         instr:instrs ->
>           let me = uid instr in
>             case op instr of
>               LOAD  -> [uid s --> me | s <- sync, null load]
>                     ++ [uid l --> me | l <- load]
>                     ++ thread stores [instr] sync instrs
>               STORE -> [uid s --> me | s <- sync, null load && null prev]
>                     ++ [uid l --> me | l <- load]
>                     ++ [uid s --> me | s <- prev]
>                     ++ thread stores' load sync instrs
>                        where
>                          prev    = M.findWithDefault [] (addr instr) stores
>                          stores' = M.insert (addr instr) [instr] stores
>               SYNC  -> [uid s --> me | s <- sync, null load]
>                     ++ [uid l --> me | l <- load]
>                     ++ [uid s --> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty [] [instr] instrs

Relaxed Memory Order.

> poRMO :: [[Instr]] -> Graph
> poRMO trace =
>   graph trace (concatMap (thread M.empty M.empty []) trace)
>   where
>     thread stores loads sync instrs =
>       case instrs of
>         []           -> []
>         instr:instrs ->
>           let me = uid instr in
>             case op instr of
>               LOAD  -> [uid s --> me | s <- sync]
>                     ++ thread stores loads' sync instrs
>                     where
>                        loads' = M.insertWith (++) (addr instr) [instr] loads
>               STORE -> [uid s --> me | s <- sync, null prevS]
>                     ++ [uid l --> me | l <- prevL]
>                     ++ [uid s --> me | s <- prevS]
>                     ++ thread stores' loads' sync instrs
>                     where
>                        prevS   = M.findWithDefault [] (addr instr) stores
>                        prevL   = M.findWithDefault [] (addr instr) loads
>                        stores' = M.insert (addr instr) [instr] stores
>                        loads'  = M.insert (addr instr) [] loads
>               SYNC  -> [uid s --> me | s <- sync]
>                     ++ [uid l --> me | l <- concat (M.elems loads)]
>                     ++ [uid s --> me | s <- concat (M.elems stores)]
>                     ++ thread M.empty M.empty [instr] instrs

Store buffer edges.  For each load, find the previous store to the
same address in program order.  If the value stored differs from the
value loaded, the store must preceed the load in memory order.  (If we
don't read from the store buffer, the store must have been flushed.)

> sbEdges :: [[Instr]] -> [(InstrId, InstrId)]
> sbEdges = concatMap (thread M.empty)
>   where
>     thread m []     = []
>     thread m (i:is) =
>       case op i of
>         LOAD  -> [uid s --> uid i | s <- p] ++ thread m is
>         STORE -> thread (M.insert (addr i) [i] m) is
>         SYNC  -> thread M.empty is
>       where
>         p = [s | s <- M.findWithDefault [] (addr i) m, val s /= val i]

Valid Executions
================

The SPARC V9 spec states that the store read by each load is:

  * the most recent store to the same address in memory order, or

  * the latest store to the same address that preceeds the load
    in program order.

The choice of which store to read from is decided by taking the one
which comes later in the memory order.

For all load instructions, the following structure contains the last
store read by that load in program order.

> type LocalRF = M.Map InstrId Instr

Now for the valid predicate.

> valid :: Maybe LocalRF -> [Instr] -> Bool
> valid maybeLocalRF instrs = step instrs M.empty S.empty
>   where
>     step [] m s = True
>     step (instr:instrs) m s =
>       case op instr of
>         LOAD  -> 
>           case maybeLocalRF of
>             Nothing -> global && step instrs m s
>             Just rf ->
>               case M.lookup (uid instr) rf of
>                 Nothing    -> global && step instrs m s
>                 Just store ->
>                   -- Has store happened yet globally?
>                   if   S.member (uid store) s
>                   then global && step instrs m s
>                   else val store == val instr && step instrs m s
>           where
>             global = M.findWithDefault (Data 0) (addr instr) m == val instr
>         STORE -> step instrs (M.insert (addr instr) (val instr) m)
>                              (S.insert (uid instr) s)
>         SYNC  -> step instrs m s

Memory Models
=============

> isSC :: [[Instr]] -> Bool
> isSC = any (valid Nothing) . sorts . poSC

> relaxed :: ([[Instr]] -> Graph) -> [[Instr]] -> Bool
> relaxed po trace = any (valid (Just localRF)) $ sorts $ po trace
>   where localRF = computeLocalReadsFrom (concat trace)

> isTSO :: [[Instr]] -> Bool
> isTSO = relaxed poTSO

> isPSO :: [[Instr]] -> Bool
> isPSO = relaxed poPSO

> isRMO :: [[Instr]] -> Bool
> isRMO = relaxed poRMO
