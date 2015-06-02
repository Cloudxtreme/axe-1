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

> module Parser (parseTrace, parseInstr) where

Parser for instruction traces.  The format of traces is illustrated by
the following example.

  0: v1 := 1
  0: sync
  0: v0 == 0
  1: v0 := 1
  1: v1 == 0
  1: { v1 == 0 ; v1 := 2 }

This trace contains five instructions, the first three run on thread 0
and the second two run on thread 1, i.e. the thread id preceeds the
':' character.  It contains two variables v0 and v1.  All variables
reside in shared memory.  The ':=' operator denotes a store of a value
to a variable and '==' denotes a load from a variable the results in
the given value.  The '{' and '}' brackets denote an atomic
read-modify-write operation (the variable in the read and the write
must be the same).

Any instruction may also contain a timestamp annotation, e.g.

  0: v1 := 1 @ 5
  1: v0 == 0 @ 10-15

Th first line is a store that started at time 5.  The second line is a
load that started at time 10 and completed at time 15.

Haskell platform imports
========================

> import Text.Parsec
> import Text.Parsec.String (parseFromFile)
> import Data.Char (isDigit)
> import qualified Data.Map as M
> import Data.List

Local imports
=============

> import Instr

Parser
======

Takes a string and produces an abstract syntax tree of type 'a'.

> type Parser a = Parsec String () a

Natural numbers
===============

> natural :: Parser Int
> natural =
>   do digits <- many1 (satisfy isDigit)
>      return (read digits)

Instructions
============

> parseInstr :: Parser [Instr]
> parseInstr = instr

> unset :: a
> unset = error "Undefined field in Instr record"

> instr :: Parser [Instr]
> instr =
>   do spaces
>      t <- natural
>      spaces
>      char ':'
>      spaces
>      i <- atomicLoadStore t
>              <|> ((:[]) `fmap` loadOrStore operator t)
>              <|> ((:[]) `fmap` sync t)
>      spaces
>      ts <- timestamp
>      spaces
>      return (map (addStamp ts) i)
>  where
>    addStamp ts i = i { stamp = ts }

> atomicLoadStore :: ThreadId -> Parser [Instr]
> atomicLoadStore t =
>   do (char '{' <|> char '<')
>      spaces
>      load <- loadOrStore opLoad t
>      spaces
>      char ';'
>      spaces
>      store <- loadOrStore opStore t
>      spaces
>      (char '}' <|> char '>')
>      case addr load == addr store of
>        True  -> return [ load { atomic = True }
>                        , store { atomic = True } ]
>        False -> error $ "parse error: atomic load-store "
>                      ++ "must access same address!"

> loadOrStore :: Parser Opcode -> ThreadId -> Parser Instr
> loadOrStore op t =
>   do a <- address
>      spaces
>      do o <- op
>         spaces
>         v <- natural
>         return $
>           Instr {
>             uid    = unset
>           , tid    = t
>           , op     = o
>           , addr   = Addr a
>           , val    = Data v
>           , atomic = False
>           , val2   = unset
>           , stamp  = noStamp
>           }

> address :: Parser Int
> address = var <|> mem
>   where
>     var = do { char 'v'; natural }
>     mem = do { string "M["; n <- natural; string "]"; return n }

> sync :: ThreadId -> Parser Instr
> sync t =
>   do string "sync"
>      spaces
>      return $
>        Instr {
>          uid     = unset
>        , tid     = t
>        , op      = SYNC
>        , addr    = unset
>        , val     = unset
>        , atomic  = False
>        , val2    = unset
>        , stamp   = noStamp
>        }

> operator :: Parser Opcode
> operator = opLoad <|> opStore

> opLoad :: Parser Opcode
> opLoad = string "==" >> return LOAD

> opStore :: Parser Opcode
> opStore = string ":=" >> return STORE

> timestamp :: Parser Timestamp
> timestamp = 
>   do ts <- optionMaybe $
>              do string "@"
>                 spaces
>                 start <- natural
>                 stop <- optionMaybe $ (string "-" >> natural)
>                 return (Just start, stop)
>      case ts of
>        Nothing -> return noStamp
>        Just x  -> return x

Traces
======

> trace :: Parser [[Instr]]
> trace =
>   do instrs <- many instr
>      eof
>      return (threads $ sanityCheck $ augment $ concat instrs)
>   where
>     augment instrs = aug 0 instrs
>       where
>         aug n [] = []
>         aug n (instr:instrs) =
>           instr { uid = Id n } : aug m instrs
>             where m = if   op instr == LOAD && atomic instr
>                       then n
>                       else n+1

Parser
======

> parseTrace :: String -> [[Instr]]
> parseTrace s =
>   case runP trace () "input" s of
>      Left err -> error ("Parse error: " ++ show err)
>      Right t  -> t

Sanity checks
=============

We perform the following checks on the input trace, and raise an error
if any are not satisified.

  * value 0 (initial value) can only be read, not written
  * the values in all stores to same address are unique

> sanityCheck :: [Instr] -> [Instr]
> sanityCheck instrs
>   | ok        = instrs
>   | otherwise = error "Input trace fails sanity check"
>   where
>     ok             = null storeOfDefault
>                   && all (unique . map val) (M.elems storesTo)
>     storeOfDefault = [i | i <- instrs, op i == STORE, val i == Data 0]
>     storesTo       = computeStoresTo instrs
>     unique xs      = length (nub xs) == length (xs)
