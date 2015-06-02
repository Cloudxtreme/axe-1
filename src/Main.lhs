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

> module Main where

> import Test
> import Test.QuickCheck
> import Models
> import Parser
> import System.Environment
> import System.Console.GetOpt
> import System.IO
> import Constraint
> import Logger
> import Data.IORef

Command-line options
====================

> data Flag =
>     Test String          -- Test equivlance of axiomatic and
>                          -- operational variants of given model
>   | NumTests Int         -- Number of tests to perform
>   | Check String         -- Check that an input trace satisifies
>                          -- the given model
>   | InputFile String     -- File to read input trace from
>   | Interactive String   -- Interactive mode using named model
>   | Verbose              -- Show generated constraints
>   | Operational          -- Use operational variant of model
>   | Log String           -- Enable logging to a file
>   deriving Show

> options :: [OptDescr Flag]
> options =
>   [ Option ['t'] ["test"] (ReqArg Test "MODEL")
>     "Test equivalence of axiomatic and\noperational versions of MODEL"
>   , Option ['n'] ["numtests"] (ReqArg (NumTests . read) "NUM")
>     "Number of tests to perform"
>   , Option ['c'] ["check"] (ReqArg Check "MODEL")
>     "Check that input trace satisfies MODEL"
>   , Option ['f'] ["input"] (ReqArg InputFile "FILE")
>     "Read input trace from FILE"
>   , Option ['i'] ["interactive"] (ReqArg Interactive "MODEL")
>     "Interactive mode using MODEL"
>   , Option ['v'] ["verbose"] (NoArg Verbose)
>     "Show generated constraints"
>   , Option ['o'] ["operational"] (NoArg Operational)
>     "Use operational variant of model"
>   , Option ['l'] ["log"] (ReqArg Log "FILE")
>     "Enable logging to a file"
>   ]

Main
====

> main :: IO ()
> main =
>   do args <- getArgs
>      case getOpt Permute options args of
>        (o, [], []) -> do let v = not $ null [() | Verbose <- o]
>                          writeIORef verboseMode v
>                          enableLogging o
>                          process o
>        (_,_,errs)  ->
>          do putStrLn $ usageInfo "Usage info:" options
>             putStrLn "  where MODEL is one of SC, TSO, PSO, or RMO"

> process :: [Flag] -> IO ()
> process opts
>   | checkerMode     = doCheck opts
>   | interactiveMode = doInteractive (head [m | Interactive m <- opts]) []
>                                     (not $ null [() | Operational <- opts])
>   | otherwise       = doEquivTest opts
>   where
>     checkerMode     = not $ null [m | Check m <- opts]
>     interactiveMode = not $ null [m | Interactive m <- opts]

> enableLogging :: [Flag] -> IO ()
> enableLogging opts = 
>   case [s | Log s <- opts] of
>     []  -> return ()
>     s:_ -> do writeFile s ""
>               writeIORef loggingMode (Just s)

> doEquivTest :: [Flag] -> IO ()
> doEquivTest opts =
>   do putStrLn $ "Testing models "
>              ++ "of '" ++ model ++ "' on "
>              ++ show numTests ++ " tests..."
>      quickCheckWith (withNumTests numTests) (test (stringToModel model))
>   where
>     numTests = head ([n | NumTests n <- opts] ++ [100])
>     model    = head ([m | Test m <- opts] ++ ["sc"])

> doCheck :: [Flag] -> IO ()
> doCheck opts =
>   do input <- if file == "stdin" then getContents else readFile file
>      checkTrace model input refMode
>   where
>     model   = head ([m | Check m <- opts] ++ ["sc"])
>     file    = head ([m | InputFile m <- opts] ++ ["stdin"])
>     refMode = not $ null [() | Operational <- opts]

> checkTrace model input refMode =
>   if   parseTrace input `sat` stringToModel model
>   then putStrLn "OK" >> hFlush stdout
>   else putStrLn "NO" >> hFlush stdout
>   where sat = if refMode then satisfiesOperational else satisfies

> doInteractive :: String -> [String] -> Bool -> IO ()
> doInteractive model lines refMode =
>   do line <- getLine
>      case line of
>        "exit"  -> return ()
>        "check" -> checkTrace model (concat $ reverse lines) refMode
>                >> doInteractive model [] refMode
>        other   -> doInteractive model ((line ++ "\n") : lines) refMode
