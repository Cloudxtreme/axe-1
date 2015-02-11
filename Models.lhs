> module Models where

Imports
=======

> import Instr
> import qualified Axiomatic.SC
> import qualified Axiomatic.TSO
> import qualified Axiomatic.PSO
> import qualified Data.Map as M

Models
======

Each model has a Store Atomic and Non Store Atomic variant.

> data Model =
>     SA    BaseModel
>   | NonSA BaseModel

The base models are:

> data BaseModel = 
>     SC
>   | TSO
>   | PSO

Function to display a model:

> instance Show Model where
>   show (SA    SC)  = "sc"
>   show (NonSA SC)  = "sc-sa"
>   show (SA    TSO) = "tso"
>   show (NonSA TSO) = "tso-sa"
>   show (SA    PSO) = "pso"
>   show (NonSA PSO) = "pso-sa"

Function to parse a model.

> stringToModel :: String -> Model
> stringToModel s =
>   case s of
>     "sc"     -> SA SC
>     "sc-sa"  -> NonSA SC
>     "tso"    -> SA TSO
>     "tso-sa" -> NonSA TSO
>     "pso"    -> SA PSO
>     "pso-sa" -> NonSA PSO
>     other    -> error $ "Unknown model '" ++ s ++ "'"

Check if a trace satisfies a given model.

> satisfies :: [[Instr]] -> Model -> Bool
> satisfies trace model = locallyConsistent trace && ok
>   where
>     ok = case model of
>            SA SC     -> Axiomatic.SC.isSC trace
>            NonSA SC  -> Axiomatic.SC.isSCMinusSA trace
>            SA TSO    -> Axiomatic.TSO.isTSO trace
>            NonSA TSO -> Axiomatic.TSO.isTSOMinusSA trace
>            SA PSO    -> Axiomatic.PSO.isPSO trace
>            NonSA PSO -> Axiomatic.PSO.isPSOMinusSA trace

Local-consistency
=================

There are some properties that traces must satisfy under any memory
model:

  * Once a thread has written to an address, it can never again read
    the intial value from that address. 

  * If a variable is not shared then any reads of that variable must
    read the latest value written locally.

  * If a read does not return the latest value written locally, there
    must exist a write of that value on another thread.

Together, these properties are referred to as "local consistency".
Traces from the random trace generator are always locally consistent,
however externally-read traces may not be.

> locallyConsistent :: [[Instr]] -> Bool
> locallyConsistent trace = all (lc M.empty) trace
>   where
>     storesTo = computeStoresTo (concat trace)
> 
>     lc m []= True
>     lc m (instr:instrs) =
>       case op instr of
>         LOAD  -> (  M.findWithDefault (Data 0) (addr instr) m == val instr
>                  || val instr `elem` external )
>               && lc m instrs
>         STORE -> lc (M.insert (addr instr) (val instr) m) instrs
>         SYNC  -> lc m instrs
>       where
>         external = [val i | i <- storesTo ! addr instr, tid i /= tid instr]
