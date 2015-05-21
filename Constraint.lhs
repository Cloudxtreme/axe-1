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
>     InstrId :-> InstrId
>   | InstrId :== InstrId
>   | Constraint :|: Constraint
>   | Constraint :<=> Constraint
>   | Fail

Combinators
===========

Construct happens-before constraint between two instructions.

> (-->) :: Instr -> Instr -> Constraint
> x --> y = uid x :-> uid y

Happen at same time:

> (===) :: Instr -> Instr -> Constraint
> x === y = uid x :== uid y

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
>     var v = "v" ++ show v
>
>     vars (x :-> y)  = [var x, var y]
>     vars (x :== y)  = [var x, var y]
>     vars (c :|: d)  = vars c ++ vars d
>     vars (c :<=> d) = vars c ++ vars d
>     vars Fail       = []
>
>     translate (x :-> y) = "(< " ++ var x ++ " " ++ var y ++ ")"
>     translate (x :== y) = "(= " ++ var x ++ " " ++ var y ++ ")"
>     translate (c :|: d) =
>       "(or " ++ translate c ++ " " ++ translate d ++ ")"
>     translate (c :<=> d) =
>       "(= " ++ translate c ++ " " ++ translate d ++ ")"
>     translate Fail = "false"
>
>     assert c = "(assert " ++ translate c ++ ")"
>
>     varDecls = unlines [ "(define " ++ v ++ " :: int)"
>                        | v <- nub (concatMap vars cs) ]

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
> yices cs = unsafePerformIO (logger (yicesCheck $ simplify cs))

Customised version of 'System.Process.readProcess'
==================================================

This one doesn't echo standard error.

> myReadProcess :: FilePath -> [String] -> String -> IO String
> myReadProcess name args input =
>   do (Just stdIn, Just stdOut, Just stdErr, h) <- createProcess p
>      hSetBuffering stdIn NoBuffering
>      hSetBuffering stdOut NoBuffering
>      hPutStr stdIn input
>      line <- hGetLine stdOut
>      hClose stdIn
>      hClose stdOut
>      hClose stdErr
>      waitForProcess h
>      return line
>   where
>     p = CreateProcess {
>           cmdspec       = RawCommand name args
>         , cwd           = Nothing
>         , env           = Nothing
>         , std_in        = CreatePipe
>         , std_out       = CreatePipe
>         , std_err       = CreatePipe
>         , close_fds     = True
>         , create_group  = False
>       --, delegate_ctlc = True
>         }

Global variable controlling verbosity
=====================================

> {-# NOINLINE verboseMode #-} 
> verboseMode :: IORef Bool
> verboseMode = unsafePerformIO (newIORef False)

Constraint simplifier
=====================

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
>         (pre, (x :-> y):post) -> x : every m post
>         other                 -> []

> simplify :: [Constraint] -> [Constraint]
> simplify cs = reverse (cs0 ++ concatMap prune cs1)
>   where
>     -- Partition constraints
>     cs0 = [(x :-> y) | (x :-> y) <- cs]
>     cs1 = [(x :|: y) | (x :|: y) <- cs]
> 
>     -- Graphs (forward and backward edge variants)
>     forward  = graph [(x, y) | (x :-> y) <- cs0]
>     backward = graph [(y, x) | (x :-> y) <- cs0]
> 
>     -- Sequencing points
>     sps = [seqPoint forward backward i | i <- someVertices 25 cs0]
> 
>     prune c@((x :-> y) :|: (v :-> w))
>       | path sps x y = []
>       | path sps v w = []
>       | otherwise    = [c]
