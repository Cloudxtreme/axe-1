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

> module Constraint where

> import Instr
> import Data.List
> import System.Process
> import System.IO
> import System.IO.Unsafe
> import Data.IORef
> import Logger
> import qualified Data.Map as M
> import qualified Data.Set as S

Types
=====

> data Constraint =
>     Instr :-> Instr
>   | Constraint :|: Constraint
>   | Fail

Combinators
===========

Union two list generators, useful for unioning constraint sets.

> (\/) :: (a -> [b]) -> (a -> [b]) -> (a -> [b])
> (f \/ g) x = f x ++ g x

Yices backend
=============

Convert constraint to Yices format.

> toYices :: [Constraint] -> String
> toYices cs =
>      varDecls
>   ++ unlines (map assert cs)
>   ++ "(check)\n"
>   ++ "(exit)\n"
>   where
>     var i = "v" ++ show (uid i)
>
>     vars (x :-> y)  = [var x, var y]
>     vars (c :|: d)  = vars c ++ vars d
>     vars Fail       = []
>
>     translate (x :-> y) = "(< " ++ var x ++ " " ++ var y ++ ")"
>     translate (c :|: d) =
>       "(or " ++ translate c ++ " " ++ translate d ++ ")"
>     translate Fail = "false"
>
>     assert c = "(assert " ++ translate c ++ ")"
>
>     varDecls = unlines [ "(define " ++ v ++ " :: int)"
>                        | v <- S.toList $ S.fromList (concatMap vars cs) ]

Check constraints using Yices.

> yicesCheck :: [Constraint] -> IO Bool
> yicesCheck cs =
>   do v <- readIORef verboseMode
>      let s = toYices cs
>      if v then putStrLn s else return ()
>      out <- myReadProcess "yices" ["--logic=QF_LIA"] s
>      return $ if   take 3 out == "sat"
>               then True
>               else (if   take 5 out == "unsat"
>                     then False
>                     else error "Error communicating with yices")

Pure vesion of the above for convenience in property-testing.

> {-# NOINLINE yices #-} 
> yices :: [Constraint] -> Bool
> yices cs = unsafePerformIO (logger (yicesCheck cs))

Customised version of 'System.Process.readProcess'
==================================================

This one doesn't echo standard error.

> myReadProcess :: FilePath -> [String] -> String -> IO String
> myReadProcess name args input =
>   do null <- openFile "/dev/null" AppendMode
>      let p = CreateProcess {
>                cmdspec       = RawCommand name args
>              , cwd           = Nothing
>              , env           = Nothing
>              , std_in        = CreatePipe
>              , std_out       = CreatePipe
>              , std_err       = UseHandle null
>              , close_fds     = True
>              , create_group  = False
>              --, delegate_ctlc = True
>              }
>      (Just stdIn, Just stdOut, _, h) <- createProcess p
>      code <- getProcessExitCode h
>      case code of
>        Nothing -> return ()
>        other   -> error "Command 'yices' not in PATH"
>      hSetBuffering stdIn NoBuffering
>      hSetBuffering stdOut NoBuffering
>      hPutStr stdIn input
>      line <- hGetLine stdOut
>      hClose stdIn
>      hClose stdOut
>      waitForProcess h
>      return line

Global variable controlling verbosity
=====================================

> {-# NOINLINE verboseMode #-} 
> verboseMode :: IORef Bool
> verboseMode = unsafePerformIO (newIORef False)

Constraint simplifier
=====================

The following constraint simplifier is no longer used.

> type Graph = M.Map InstrId (S.Set InstrId)

> graph :: [(InstrId, InstrId)] -> Graph
> graph [] = M.empty
> graph ((x, y):es) = M.insertWith S.union x (S.singleton y) (graph es)

> type SeqPoint = (S.Set InstrId, S.Set InstrId)

> reachable :: Graph -> InstrId -> S.Set InstrId
> reachable g x = r S.empty [x]
>   where
>     r v [] = v
>     r v (x:xs)
>       | x `S.member` v = r v xs
>       | otherwise      = r (S.insert x v) (S.toList succs ++ xs)
>       where succs      = M.findWithDefault S.empty x g

> seqPoint :: Graph -> Graph -> InstrId -> SeqPoint
> seqPoint forward backward x =
>   (reachable backward x, reachable forward x)

> path :: [SeqPoint] -> InstrId -> InstrId -> Bool
> path sps x y = any f sps
>   where f (before, after) = x `S.member` before && y `S.member` after

> someVertices :: Int -> [Constraint] -> [InstrId]
> someVertices n cs = nub $ every (length cs `div` n) cs
>   where
>     every m cs =
>       case splitAt m cs of
>         (pre, (x :-> y):post) -> uid x : every m post
>         other                 -> []

> simplify :: [Constraint] -> [Constraint]
> simplify cs = reverse (cs0 ++ concatMap prune cs1)
>   where
>     -- Partition constraints
>     cs0 = [(x :-> y) | (x :-> y) <- cs]
>     cs1 = [(x :|: y) | (x :|: y) <- cs]
> 
>     -- Graphs (forward and backward edge variants)
>     forward  = graph [(uid x, uid y) | (x :-> y) <- cs0]
>     backward = graph [(uid y, uid x) | (x :-> y) <- cs0]
> 
>     -- Sequencing points
>     sps     = [seqPoint forward backward i | i <- someVertices 50 cs0]
> 
>     prune c@((x :-> y) :|: (v :-> w))
>       | path sps (uid x) (uid y) = []
>       | path sps (uid v) (uid w) = []
>       | otherwise                = [c]
