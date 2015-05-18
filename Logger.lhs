> module Logger where

Imports
=======

> import Data.Time
> import System.IO
> import System.IO.Unsafe
> import Data.IORef
> import Control.Exception

Functions
=========

> time :: IO a -> IO (a, String)
> time m =
>   do start <- getCurrentTime
>      x     <- m
>      end   <- x `seq` getCurrentTime
>      let t = show (diffUTCTime end start)
>      return (x, t)

> logger :: IO a -> IO a
> logger m =
>   do log <- readIORef loggingMode
>      case log of
>        Nothing       -> m
>        Just filename ->
>          do (x, t) <- time m
>             appendFile filename (t ++ "\n")
>             return x

Global variable controlling verbosity
=====================================

> {-# NOINLINE loggingMode #-}
> loggingMode :: IORef (Maybe String)
> loggingMode = unsafePerformIO (newIORef Nothing)
