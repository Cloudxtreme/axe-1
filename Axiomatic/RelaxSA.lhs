> module Axiomatic.RelaxSA where

> import Instr
> import Constraint
> import qualified Data.Map as M

Coherence order
===============

Assert that, for all writes to some location (a list of instruction
ids), each thread sees the writes in the same order.

> coherent :: [ThreadId] -> [InstrId] -> [Constraint]
> coherent tids stores =
>     concat [ [      ((x # first) :-> (y # first))
>                :<=> ((x # other) :-> (y # other))
>              | first <- take 1 tids, other <- tids, first /= other ]
>            | (x, y) <- pairs stores ]
>   where
>     pairs []     = []
>     pairs (x:ys) = [(x, y) | y <- ys] ++ pairs ys

Relaxation of Store Atomicity
=============================

Modify a trace to account for absence of store atomicity, where each
thread may have a different (but still coherent) view of memory.  The
set of input constraints is the set of program-order constraints,
which also gets modified slightly.

> relax :: ([[Instr]], [Constraint]) -> ([[Instr]], [Constraint])
> relax (trace, cs) = (trace', cs' ++ forkJoin ++ co)
>   where
>     instrs   = concat trace
>     tids     = threadIds instrs
>
>     trace'   = [ concat [ if   op i == STORE
>                           then [ i { uid  = (uid i # t)
>                                    , addr = addr i :@ t }
>                                | t <- tids ]
>                           else [ i { addr = addr i :@ tid i } ]
>                         | i <- is ]
>                | is <- trace ]
>
>     stores   = M.fromList [ (uid instr, instr)
>                           | instr <- instrs
>                           , op instr == STORE]
>
>     cs'      = [ if   M.member to stores
>                  then (from :-> (to # 0 # 0))
>                  else (from :-> to)
>                | (from :-> to) <- cs ]
> 
>     forkJoin = concat [ concat [ [ (uid s # 0 # 0) :-> (uid s # t)
>                                  , (uid s # t)     :-> uid s ]
>                                | t <- tids ]
>                       | s <- M.elems stores ]
>
>     storesTo = computeStoresTo instrs
>     co       = concat [ coherent tids (map uid ss)
>                       | ss <- M.elems storesTo ]

Top-level
=========

> type CG = [[Instr]] -> [Constraint]

Given:

  * a PO (program-order) constraint generator;
  * a RFWO (reads-from and write-order) constraint generator;

generate constraints with store atomicity relaxed.

> relaxSA :: CG -> CG -> CG
> relaxSA po rfwo trace = cs ++ rfwo trace'
>  where (trace', cs) = relax (trace, po trace)
