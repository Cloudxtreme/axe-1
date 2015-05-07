> module Interleaving where

Imports
=======

> import Instr
> import Data.List
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

Sequential Consistency (SC)
===========================

Is any interleaving valid?

> isSC :: [[Instr]] -> Bool
> isSC = any valid . ilv scNext

> scNext :: Next Instr
> scNext (x:xs) = [(x, xs)]

Total Store Order (TSO)
=======================

> isTSO :: [[Instr]] -> Bool
> isTSO = any valid . ilv tsoNext

> tsoNext :: Next Instr
> tsoNext (x:xs) = [(x, xs)] ++ if op x == STORE then next [x] xs else []
>   where
>     next stores []     = []
>     next stores (x:xs) =
>       case op x of
>         STORE -> next (x:stores) xs
>         LOAD  -> if   null prev
>                  then [(x, reverse stores ++ xs)]
>                  else if   prev == [val x]
>                       then next stores xs
>                       else []
>         SYNC  -> []
>       where
>         prev = take 1 [val s | s <- stores, addr s == addr x]

Partial Store Order (PSO)
========================

> isPSO :: [[Instr]] -> Bool
> isPSO = any valid . ilv psoNext

> psoNext :: Next Instr
> psoNext (x:xs) = [(x, xs)] ++ if op x == STORE then next [x] xs else []
>   where
>     next stores []     = []
>     next stores (x:xs) =
>       case op x of
>         STORE -> [(x, reverse stores ++ xs) | null prev]
>               ++ next (x:stores) xs
>         LOAD  -> if   null prev
>                  then [(x, reverse stores ++ xs)]
>                  else if   prev == [val x]
>                       then next stores xs
>                       else []
>         SYNC  -> []
>       where
>         prev = take 1 [val s | s <- stores, addr s == addr x]

Relaxed Memory Order (RMO)
==========================

> isRMO :: [[Instr]] -> Bool
> isRMO = any valid . ilv rmoNext

> rmoNext :: Next Instr
> rmoNext (x:xs) = [(x, xs)] ++ if op x /= SYNC then next [x] xs else []
>   where
>     next instrs []     = []
>     next instrs (x:xs) =
>       case op x of
>         STORE -> [(x, reverse instrs ++ xs) | null prevS && null prevL]
>               ++ next (x:instrs) xs
>         LOAD  -> if   null prevS
>                  then [(x, reverse instrs ++ xs)] ++ next (x:instrs) xs
>                  else if   prevS == [val x]
>                       then next instrs xs
>                       else next (x:instrs) xs
>         SYNC  -> []
>       where
>         prevS = take 1 [val i | i <- instrs, op i == STORE, addr i == addr x]
>         prevL = take 1 [val i | i <- instrs, op i == LOAD, addr i == addr x]

Relax Store-Atomicity
=====================

> relaxSA :: Next Instr -> [[Instr]] -> Bool
> relaxSA next = any coherent . filter valid . ilv (propagate . next)

> propagate :: [(Instr, [Instr])] -> [(Instr, [Instr])]
> propagate = concatMap prop
>   where
>     prop (x, xs)
>       | op x == STORE = 
>           -- This is a slight optimisation: only the else case is needed
>           if   tid x `elem` propTo x
>           then [(x `on` tid x, (x `seenBy` tid x) ++ xs)]
>           else [(x `on` t, (x `seenBy` t) ++ xs) | t <- propTo x]
>       | otherwise     = [(x `on` tid x, xs)]

> on :: Instr -> ThreadId -> Instr
> instr `on` t =
>   instr { addr = addr instr :@ t }

> seenBy :: Instr -> ThreadId -> [Instr]
> instr `seenBy` t
>   | null propTo' = []
>   | otherwise    = [instr { propTo = propTo' }]
>   where propTo'  = delete t (propTo instr)

> coherent :: [Instr] -> Bool
> coherent instrs = noCycles (step instrs M.empty)
>   where
>     step [] m = M.empty
>     step (instr:instrs) m =
>       case op instr of
>         STORE -> let p  = M.findWithDefault (Data 0) (addr instr) m
>                      m' = M.insert (addr instr) (val instr) m
>                      g  = step instrs m'
>                  in  M.insertWith union (a, p) [val instr] g
>         other -> step instrs m
>       where
>         (a :@ t) = addr instr
>
>     noCycles g = and [noc [] a (Data 0) g | a :@ t <- addrs instrs]
>       where
>         noc seen a root g
>           | root `elem` seen = False
>           | otherwise =
>               case M.lookup (a, root) g of
>                 Nothing -> True
>                 Just xs -> and [noc (root:seen) a x g | x <- xs]

Sequential Consistency minus Store Atomicity (SC-SA)
====================================================

> isSCMinusSA :: [[Instr]] -> Bool
> isSCMinusSA = relaxSA scNext

Total Store Order minus Store Atomicity (TSO-SA)
================================================

> isTSOMinusSA :: [[Instr]] -> Bool
> isTSOMinusSA = relaxSA tsoNext

Partial Store Order minus Store Atomicity (PSO-SA)
==================================================

> isPSOMinusSA :: [[Instr]] -> Bool
> isPSOMinusSA = relaxSA psoNext

Relaxed Memory Order minus Store Atomicity (RMO-SA)
===================================================

> isRMOMinusSA :: [[Instr]] -> Bool
> isRMOMinusSA = relaxSA rmoNext
