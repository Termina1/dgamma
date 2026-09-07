module DGamma.CP5O20SafeBlockSelectionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact finite-list location of the two neighboring actors, including the
||| source BeforeIn witness. This does not infer whole-trace block adjacency.
export
0 o20AdjacentListFacts :
  {name : Type} -> (earlier : List name) -> (left, right : name) -> (later : List name) ->
  (Elem left (earlier ++ (left :: right :: later)),
   Elem right (earlier ++ (left :: right :: later)),
   BeforeIn left right (earlier ++ (left :: right :: later)))
o20AdjacentListFacts [] left right later = (Here, There Here, BeforeHere Here)
o20AdjacentListFacts (head :: rest) left right later =
  (There (Builtin.fst (o20AdjacentListFacts rest left right later)),
   There (Builtin.fst (Builtin.snd (o20AdjacentListFacts rest left right later))),
   BeforeThere (Builtin.snd (Builtin.snd (o20AdjacentListFacts rest left right later))))
