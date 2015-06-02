Copyright 2015 Matthew Naylor
All rights reserved.

This software was developed by SRI International and the University of
Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-10-C-0237
("CTSRD"), as part of the DARPA CRASH research programme.

This software was developed by SRI International and the University of
Cambridge Computer Laboratory under DARPA/AFRL contract FA8750-11-C-0249
("MRC2"), as part of the DARPA MRC research programme.

@BERI_LICENSE_HEADER_START@

Licensed to BERI Open Systems C.I.C. (BERI) under one or more contributor
license agreements.  See the NOTICE file distributed with this work for
additional information regarding copyright ownership.  BERI licenses this
file to you under the BERI Hardware-Software License, Version 1.0 (the
"License"); you may not use this file except in compliance with the
License.  You may obtain a copy of the License at:

  http://www.beri-open-systems.org/legal/license-1-0.txt

Unless required by applicable law or agreed to in writing, Work distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.  See the License for the
specific language governing permissions and limitations under the License.

@BERI_LICENSE_HEADER_END@

Specifications of each memory model from the SPARC manual.  (This
module is currently unused and slightly outdated, e.g. it does not
support atomic read-modify-write instructions.)

> module Spec where

> import Instr
> import qualified Data.Map as M
> import qualified Data.Set as S
> import Data.List (union)
> import Data.Maybe
> import qualified LocalOrder as PO

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

All destinations from a vertex.

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

> edge (x, y) = uid x --> uid y

Sequential Consistency.

> poSC :: [[Instr]] -> Graph
> poSC trace = graph trace (map edge $ PO.poSC trace)

Total Store Order.

> poTSO :: [[Instr]] -> Graph
> poTSO trace = graph trace (map edge $ PO.poTSO trace)

Partial Store Order.

> poPSO :: [[Instr]] -> Graph
> poPSO trace =  graph trace (map edge $ PO.poPSO trace)

Relaxed Memory Order.

> poRMO :: [[Instr]] -> Graph
> poRMO trace = graph trace (map edge $ PO.poRMO trace)

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
> relaxed po trace = any (valid (Just localStores)) $ sorts $ po trace
>   where localStores = computePrevLocalStore (concat trace)

> isTSO :: [[Instr]] -> Bool
> isTSO = relaxed poTSO

> isPSO :: [[Instr]] -> Bool
> isPSO = relaxed poPSO

> isRMO :: [[Instr]] -> Bool
> isRMO = relaxed poRMO
