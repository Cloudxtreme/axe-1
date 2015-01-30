> module Interleaving where

Imports
=======

> import Instr
> import qualified Data.Map as M

Interleaving
============

Functions for interleaving N lists.  The choice of which element to
take next from a sub-list is parameterised by a function.  Given a
list, this 'next' function returns zero or more possible extractions
of an element from this list.  It may assume that the input list is
non-empty.

> type Next a = [a] -> [(a, [a])]

For example, to generate all interleavings of N lists:

> interleave :: [[a]] -> [[a]]
> interleave = ilv next
>   where next (x:xs) = [(x, xs)]

Now for the ilv function:

> ilv :: Next a -> [[a]] -> [[a]]
> ilv next xss
>   | all null xss = [[]]
>   | otherwise    = [y:zss | (y, yss) <- pick next xss, zss <- ilv next yss]

> pick :: Next a -> [[a]] -> [(a, [[a]])]
> pick next [] = []
> pick next (xs:xss)
>   | null xs   = pick next xss
>   | otherwise = [(h, t:xss)  | (h, t) <- next xs]
>              ++ [(y, xs:yss) | (y, yss) <- pick next xss]

Valid executions
================

Is given interleaving of instructions valid?

> valid :: [Instr] -> Bool
> valid instrs = step instrs M.empty
>   where
>     step [] m = True
>     step (instr:instrs) m =
>       case op instr of
>         LOAD  -> M.findWithDefault (Data 0) (addr instr) m == val instr
>               && step instrs m
>         STORE -> step instrs (M.insert (addr instr) (val instr) m)
>         SYNC  -> step instrs m

Sequential consistency (SC)
===========================

Is any interleaving valid?

> isSC :: [[Instr]] -> Bool
> isSC = any valid . interleave

Total Store Order (TSO)
=======================

> isTSO :: [[Instr]] -> Bool
> isTSO = any valid . ilv next
>   where
>     next (x:xs)  = [(x, xs)]
>                 ++ if op x == STORE then next' [x] xs else []
>
>     next' stores []     = []
>     next' stores (x:xs) =
>       case op x of
>         STORE -> next' (x:stores) xs
>         LOAD  -> if   not seen
>                  then [(x, reverse stores ++ xs)]
>                  else if   prev == [val x]
>                       then next' stores xs
>                       else []
>         SYNC  -> []
>       where
>         seen = addr x `elem` map addr stores
>         prev = take 1 [val s | s <- stores, addr s == addr x]
