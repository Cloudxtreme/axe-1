> module Main where

> import Test
> import Test.QuickCheck
> import Models
> import Interleaving
> import Parser
> import System.Environment
> import System.Console.GetOpt

Command-line options
====================

> data Flag =
>     Test String          -- Test equivlance of axiomatic and
>                          -- operational variants of given model
>   | NumTests Int         -- Number of tests to perform
>   | Check String         -- Check that an input trace satisifies
>                          -- the given model
>   | InputFile String     -- File to read input trace from
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
>   ]

Main
====

> main :: IO ()
> main =
>   do args <- getArgs
>      case getOpt Permute options args of
>        (o, [], []) -> process o
>        (_,_,errs)  -> putStrLn $ usageInfo "Usage info:" options

> process :: [Flag] -> IO ()
> process opts
>   | checkerMode = doCheck opts
>   | otherwise   = doEquivTest opts
>   where
>     checkerMode = not $ null [m | Check m <- opts]

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
>      check input
>   where
>     model = head ([m | Check m <- opts] ++ ["sc"])
>     file  = head ([m | InputFile m <- opts] ++ ["stdin"])
>
>     check input =
>       if   parseTrace input `satisfies` stringToModel model
>       then putStrLn ("YES: satisifies '" ++ model ++ "'")
>       else putStrLn ("NO: does not satisfy '" ++ model ++ "'")
