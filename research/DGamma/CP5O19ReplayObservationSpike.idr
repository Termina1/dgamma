module DGamma.CP5O19ReplayObservationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B21: specialize the EXISTING producer-owned action fold. This observes
||| actual trace data; no execution outcome or replay target is guessed.
public export
0 o19ActionWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> List (Action name key value world error)
o19ActionWord {name} {key} {world} {error} {value} trace =
  traceActionFold name key world error value (List (Action name key value world error)) (::) [] trace

||| B22: observed TWO actual checked transitions, not independently supplied
||| moved nodes. Both actions and their complete trace/alignment are owned.
public export
record ObservedTwoActionTrace
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (wantedFirst, wantedSecond : Action name key value world error)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkObservedTwoActionTrace
  twoActionMiddle : SystemState name key value world error
  twoActionFirst : Transition initial twoActionMiddle
  twoActionSecond : Transition twoActionMiddle finalState
  0 twoActionFirstExact : (transitionAction twoActionFirst = wantedFirst)
  0 twoActionSecondExact : (transitionAction twoActionSecond = wantedSecond)
  0 twoActionTraceExact : (MoreTransitions twoActionFirst (MoreTransitions twoActionSecond NoTransitions) = trace)
  0 twoActionAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions twoActionFirst (MoreTransitions twoActionSecond NoTransitions))

||| B23: inspect an EXPLICIT actual trace; its observed two-action word rules
||| out every other length. No constructor of the sealed replay is exposed.
public export
0 o19TwoActionTraceObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (wantedFirst, wantedSecond : Action name key value world error) ->
  (trace : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (o19ActionWord trace = [wantedFirst, wantedSecond]) ->
  ObservedTwoActionTrace name key world error value nameEq keyEq wantedFirst wantedSecond trace
o19TwoActionTraceObserved nameEq keyEq wantedFirst wantedSecond NoTransitions aligned observed =
  void (uninhabited (cong length observed))
o19TwoActionTraceObserved nameEq keyEq wantedFirst wantedSecond
  (MoreTransitions first NoTransitions) aligned observed =
    void (uninhabited (cong length observed))
o19TwoActionTraceObserved nameEq keyEq wantedFirst wantedSecond
  (MoreTransitions {middle = between} first (MoreTransitions second NoTransitions)) aligned observed =
    MkObservedTwoActionTrace between first second
      (Builtin.fst (consInjective observed))
      (Builtin.fst (consInjective (Builtin.snd (consInjective observed)))) Refl aligned
o19TwoActionTraceObserved nameEq keyEq wantedFirst wantedSecond
  (MoreTransitions first (MoreTransitions second (MoreTransitions third rest))) aligned observed =
    void (uninhabited (cong length observed))

||| B24: exact producer-owned word equality, ONLY a specialization/projection
||| of the existing sealed fold. It does not open or rebuild sealed constructors.
public export
0 o19SealedActionWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal : SystemState name key value world error} ->
  {source : Transitions sourceFirst sourceFinal} ->
  {replayed : Transitions replayedFirst replayedFinal} ->
  SealedSuffixReplaySpine name key world error value nameEq keyEq source replayed ->
  (o19ActionWord replayed = o19ActionWord source)
o19SealedActionWord {name} {key} {world} {error} {value} nameEq keyEq seal =
  sealedSuffixActionFoldSame name key world error value nameEq keyEq
    (List (Action name key value world error)) (::) [] seal

||| B25: derive the ACTUAL replayed suffix alignment from its same reached
||| bundle/decomposition. No independently supplied suffix alignment is needed.
public export
0 o19ReplayedSuffixAligned :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq original earlier left right later diamond) ->
  AlignedTransitions name key world error value nameEq keyEq (replayedSuffix result)
o19ReplayedSuffixAligned {name} {key} {world} {error} {value}
  nameEq keyEq protocol original earlier left right later diamond result =
    Builtin.snd (alignedAppendSplit
      (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions))
      (replayedSuffix result)
      (Builtin.snd (alignedAppendSplit earlier
        (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) (replayedSuffix result)))
        (replace {p = AlignedTransitions name key world error value nameEq keyEq}
          (swappedDecomposition result) (replayAligned (swappedPremises result))))))

||| B30: structural composition of ACTUAL sealed-node derivations. The
||| intermediate trace is shared by the indices; no endpoint-only shortcut.
public export
0 o19AppendFinite :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, middleFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {middleTrace : Transitions initial middleFinal} ->
  {target : Transitions initial targetFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source middleTrace ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq middleTrace target ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target
o19AppendFinite FiniteAdjacentSwapDone next = next
o19AppendFinite {target}
  (FiniteAdjacentSwapStep original earlier left right later orientation diamond result _ rest) next =
    FiniteAdjacentSwapStep original earlier left right later orientation diamond result target
      (o19AppendFinite rest next)
