> module Models where

Imports
=======

> import Instr
> import qualified Axiomatic
> import qualified Data.Map as M
> import qualified Spec as Spec
> import qualified Operational

Models
======

Each model has a Store Atomic and Non Store Atomic variant.

> data Model =
>     SC
>   | TSO
>   | PSO
>   | RMO

Function to display a model:

> instance Show Model where
>   show SC  = "sc"
>   show TSO = "tso"
>   show PSO = "pso"
>   show RMO = "rmo"

Function to parse a model.

> stringToModel :: String -> Model
> stringToModel s =
>   case s of
>     "sc"     -> SC
>     "tso"    -> TSO
>     "pso"    -> PSO
>     "rmo"    -> RMO
>     other    -> error $ "Unknown model '" ++ s ++ "'"

Check if a trace satisfies a given constraint model.

> satisfies :: [[Instr]] -> Model -> Bool
> satisfies trace model = locallyConsistent trace && ok
>   where
>     ok = case model of
>            SC  -> Axiomatic.isSC trace
>            TSO -> Axiomatic.isTSO trace
>            PSO -> Axiomatic.isPSO trace
>            RMO -> Axiomatic.isRMO trace

Check if a trace satisfies a given reference model.

> satisfiesRef :: [[Instr]] -> Model -> Bool
> satisfiesRef trace model = locallyConsistent trace && ok
>   where
>     ok = case model of
>            SC  -> Operational.isSC trace
>            TSO -> Operational.isTSO trace
>            PSO -> Operational.isPSO trace
>            RMO -> Operational.isRMO trace

Local-consistency
=================

There are some properties that traces must satisfy under any memory
model:

  * Once a thread has written to an address, it can never again read
    the intial value from that address. 

  * Once a thread has read a non-initial value from an address, it can 
    never again read the intial value from that address.

  * If a variable is not shared then any reads of that variable must
    read the latest value written locally.

  * If a read does not return the latest value written locally, there
    must exist a write of that value on another thread.

Together, these properties are referred to as "local consistency".
Traces from the random trace generator are always locally consistent,
however externally-read traces may not be.

> locallyConsistent :: [[Instr]] -> Bool
> locallyConsistent trace = all (lc M.empty M.empty) trace
>   where
>     storesTo = computeStoresTo (concat trace)
> 
>     lc m r [] = True
>     lc m r (instr:instrs) =
>       case op instr of
>         LOAD  -> (  M.findWithDefault latest (addr instr) m == val instr
>                  || val instr `elem` external )
>               && lc m r' instrs
>         STORE -> lc (M.insert (addr instr) (val instr) m) r instrs
>         SYNC  -> lc m r instrs
>       where
>         external = [val i | i <- M.findWithDefault [] (addr instr) storesTo
>                           , tid i /= tid instr]
>         latest   = M.findWithDefault (Data 0) (tid instr, addr instr) r
>         r'       = M.insert (tid instr, addr instr) (val instr) r
