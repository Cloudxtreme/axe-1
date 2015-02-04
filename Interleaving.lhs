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
>         LOAD  -> if   not seen
>                  then [(x, reverse stores ++ xs)]
>                  else if   prev == [val x]
>                       then next stores xs
>                       else []
>         SYNC  -> []
>       where
>         seen = addr x `elem` map addr stores
>         prev = take 1 [val s | s <- stores, addr s == addr x]

Non Store-Atomic (-SA)
======================

> notSA :: Next Instr -> [[Instr]] -> Bool
> notSA next = any coherent . filter valid . ilv (propagate . next)

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
> isSCMinusSA = notSA scNext

Total Store Order minus Store Atomicity (TSO-SA)
================================================

> isTSOMinusSA :: [[Instr]] -> Bool
> isTSOMinusSA = notSA tsoNext




===
Old
===

> {-
> isTSOMinusSA :: [[Instr]] -> Bool
> isTSOMinusSA = any valid . ilv tsoNextNonSA
>
> tsoNextNonSA :: Next Instr
> tsoNextNonSA (x:xs)
>   | op x == STORE = [(x `on` t, (x `seenBy` t) ++ xs) | t <- propTo x]
>                --  ++ next [x] xs
>   | otherwise     = [(x `on` tid x, xs)]
>   where
>     next stores []     = []
>     next stores (x:xs) =
>       case op x of
>         STORE -> next (x:stores) xs
>         LOAD  -> if   not seen
>                  then [(x `on` tid x, reverse stores ++ xs)]
>                  else if   prev == [val x]
>                       then next stores xs
>                       else []
>         SYNC  -> []
>       where
>         seen = addr x `elem` map addr stores
>         prev = take 1 [val s | s <- stores, addr s == addr x]
>
> instr `on` t =
>   instr { addr = case addr instr of Addr a -> a :@ t }
>
> instr `seenBy` t
>   | null propTo' = []
>   | otherwise    = [instr { propTo = propTo' }]
>   where propTo'  = delete t (propTo instr)
> -}



Validity in the absence of Store Atomicity.

> {-
> validNonSA :: [Instr] -> Bool
> validNonSA instrs = step instrs visibleTo
>   where
>     tids      = threadIds instrs
>     as        = addrs instrs
>     visibleTo = M.fromList [ (t, [(a, Data 0) | a <- as]) | t <- tids ]
>
>     step [] vis = True
>     step (instr:instrs) vis =
>       let (t, a, v) = (tid instr, addr instr, val instr) in
>         case op instr of
>           LOAD ->
>             if   lookup a (vis ! t) == Just v
>             then step instrs vis
>             else let vis' = propagate (a, v) t vis
>                  in  if   lookup a (vis' ! t) == Just v
>                      then step instrs vis'
>                      else False
>           STORE ->
>             let vis' = M.insertWith (++) t [(a, v)] vis
>             in  step instrs vis'
>           SYNC  -> step instrs vis -- TODO: more
>
>     prop (a, v) from to vis =
>       case break (== (a, v)) (vis ! from) of
>         (pre, w:post) -> takeWhile (`notElem` (vis ! to)) (w:post)
>         other         -> []
>
>     propagate (a, v) to vis = M.insertWith (++) to new vis
>       where
>         new = concat [ prop (a, v) from to vis
>                      | from <- tids, from /= to]
> -}

> {-
> validNonSA :: [Instr] -> Bool
> validNonSA instrs = step instrs writesBy visibleTo
>   where
>     tids      = threadIds instrs
>     as        = addrs instrs
>     writesBy  = M.fromList [ (t, []) | t <- tids ]
>     visibleTo = M.fromList [ (t, [(a, Data 0) | a <- as]) | t <- tids ]
>
>     step [] ws vis = True
>     step (instr:instrs) ws vis =
>       let (t, a, v) = (tid instr, addr instr, val instr) in
>         case op instr of
>           LOAD ->
>             if   lookup a (vis ! t) == Just v
>             then step instrs ws vis
>             else let vis' = propagate (a, v) t ws vis
>                  in  if   lookup a (vis' ! t) == Just v
>                      then step instrs ws vis'
>                      else False
>           STORE ->
>             let ws'  = M.insertWith (++) t [(a, v)] ws
>                 vis' = M.insertWith (++) t [(a, v)] vis
>             in  step instrs ws' vis'
>           SYNC  -> step instrs ws vis -- TODO: more
>
>     prop (a, v) from to ws vis =
>       case break (== (a, v)) (ws ! from) of
>         (pre, w:post) -> takeWhile (`notElem` (vis ! to)) (w:post)
>         other         -> []
>
>     propagate (a, v) to ws vis = M.insertWith (++) to new vis
>       where
>         new = concat [ prop (a, v) from to ws vis
>                      | from <- tids, from /= to]
> -}


