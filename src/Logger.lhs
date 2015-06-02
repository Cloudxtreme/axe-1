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
