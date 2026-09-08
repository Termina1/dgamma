module DGamma.CP5O19CartesianColumnsSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import DGamma.CP5O19CartesianLengthSpike
import DGamma.CP5O19PairObservationSpike
import DGamma.CP5O19CartesianWordRowSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact executable cut of an ACTUAL trace by its two source action words.
||| Both dependent stateful pieces, their authentic decomposition, word
||| equations and prefix count are owned by this SAME produced cut.
public export
record O19WordCut
  (name, key, world, error : Type) (value : key -> Type)
  (leftWord, rightWord : List (Action name key value world error))
  {first, last : SystemState name key value world error}
  (trace : Transitions first last) where
  constructor MkO19WordCut
  cutMiddle : SystemState name key value world error
  cutPrefix : Transitions first cutMiddle
  cutSuffix : Transitions cutMiddle last
  0 cutDecomposition : appendTransitions cutPrefix cutSuffix = trace
  0 cutLeftWord : o19ActionWord cutPrefix = leftWord
  0 cutRightWord : o19ActionWord cutSuffix = rightWord
  0 cutLeftCount : transitionCount cutPrefix = length leftWord

||| Extend an EXPLICIT produced cut by its actual observed source head.
||| All count/decomposition/word proofs see this same cut and constructor.
export
0 o19WordCutPrepend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, last : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle last) ->
  (wanted : Action name key value world error) -> (leftWord, rightWord : List (Action name key value world error)) ->
  (transitionAction step = wanted) -> O19WordCut name key world error value leftWord rightWord rest ->
  O19WordCut name key world error value (wanted :: leftWord) rightWord (MoreTransitions step rest)
o19WordCutPrepend step rest wanted leftWord rightWord exact
  (MkO19WordCut between leading suffix decomposition leftExact rightExact count) =
    MkO19WordCut between (MoreTransitions step leading) suffix (cong (MoreTransitions step) decomposition)
      (trans (cong (\action => action :: o19ActionWord leading) exact) (cong (wanted ::) leftExact)) rightExact (cong S count)
