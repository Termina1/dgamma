module DGamma.CP5O19OrdinalPlanSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameOrdinalCapital
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The sealed numeric adjacent transposition is its own inverse. This is
||| ordinal-only, so equal action labels never identify distinct occurrences.
export
0 o19AdjacentOrdinalSymmetric :
  {point, target, source : Nat} -> AdjacentSwapOrdinalRelation point target source ->
  AdjacentSwapOrdinalRelation point source target
o19AdjacentOrdinalSymmetric (AdjacentPrefixOrdinal earlier) = AdjacentPrefixOrdinal earlier
o19AdjacentOrdinalSymmetric AdjacentMovedRightOrdinal = AdjacentMovedLeftOrdinal
o19AdjacentOrdinalSymmetric AdjacentMovedLeftOrdinal = AdjacentMovedRightOrdinal
o19AdjacentOrdinalSymmetric (AdjacentSuffixOrdinal later) = AdjacentSuffixOrdinal later

||| An ACTUAL sealed node's origin ordinal agrees with the executable
||| four-region classifier. Source-position uniqueness is not action equality.
export
0 o19AdjacentSourceOrdinalExact :
  (point, target, source : Nat) -> AdjacentSwapOrdinalRelation point target source ->
  (source = fst (adjacentSwapOrdinalExhaustive point target))
o19AdjacentSourceOrdinalExact point target source relation =
  uniqueAdjacentOrdinalInjective point source (fst (adjacentSwapOrdinalExhaustive point target)) target target
    (o19AdjacentOrdinalSymmetric relation)
    (o19AdjacentOrdinalSymmetric (snd (adjacentSwapOrdinalExhaustive point target))) Refl

||| The same actual prefix correspondence owns an executable ordinal map
||| and its all-occurrence authentication. This distinguishes repeated Iter
||| occurrences even when their complete action/tag labels are identical.
public export
record O19OrdinalActionMap
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, currentFirst, currentFinal : SystemState name key value world error}
  (source : Transitions sourceFirst sourceFinal) (current : Transitions currentFirst currentFinal)
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) where
  constructor MkO19OrdinalActionMap
  ordinalOrigin : Nat -> Nat
  0 ordinalOriginExact : {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action current) ->
    (locatedActionOrdinal (replayActionOrigin correspondence occurrence) = ordinalOrigin (locatedActionOrdinal occurrence))

||| Compose the SAME prefix ordinal map through one ACTUAL sealed adjacent
||| result. Both the correspondence index and every new ordinal equation use
||| the very same node's operationalOccurrenceFold.
export
0 o19OrdinalMapAfterNode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, currentFinal, before, middle, afterState : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {current : Transitions initial currentFinal} ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  O19OrdinalActionMap name key world error value source current correspondence ->
  (earlier : Transitions initial before) -> (left : Transition before middle) -> (right : Transition middle afterState) ->
  (later : Transitions afterState currentFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq current earlier left right later diamond) ->
  O19OrdinalActionMap name key world error value source (swappedTrace result)
    (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result))
o19OrdinalMapAfterNode correspondence previous earlier left right later diamond result =
  MkO19OrdinalActionMap
    (\position => ordinalOrigin previous (fst (adjacentSwapOrdinalExhaustive (transitionCount earlier) position)))
    (\occurrence => trans (ordinalOriginExact previous (replayActionOrigin (swappedOccurrenceCorrespondence result) occurrence))
      (cong (ordinalOrigin previous)
        (o19AdjacentSourceOrdinalExact (transitionCount earlier) (locatedActionOrdinal occurrence)
          (locatedActionOrdinal (replayActionOrigin (swappedOccurrenceCorrespondence result) occurrence))
          (operationalOrdinalRelation (swappedOccurrenceFold result) occurrence))))

||| The ORIGINAL coordinate map starts at actual correspondence identity.
export
0 o19IdentityOrdinalMap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} -> (source : Transitions first last) ->
  O19OrdinalActionMap name key world error value source source (identityActionRegistrationReplayCorrespondence source)
o19IdentityOrdinalMap source = MkO19OrdinalActionMap id (\occurrence => Refl)

||| Exact GLOBAL-origin plan for a real finite chain. Unlike the paper's
||| BlockCrossingOriginPlan this does not claim selected-block-local ranges
||| or Cartesian coverage. It records the two TRUE source ordinals at every
||| node while definitionally composing that same node's occurrence map.
public export
data O19GlobalCrossingPlan :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  {currentFinal, targetFinal : SystemState name key value world error} ->
  {current : Transitions initial currentFinal} -> {target : Transitions initial targetFinal} ->
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq current target -> List (Nat, Nat) -> Type where
  GlobalOriginPlanDone :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, sourceFinal, currentFinal : SystemState name key value world error} ->
    {source : Transitions initial sourceFinal} -> {current : Transitions initial currentFinal} ->
    {correspondence : ActionRegistrationReplayCorrespondence name key world error value source current} ->
    O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source correspondence FiniteAdjacentSwapDone []
  GlobalOriginPlanStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, sourceFinal, currentFinal, before, middle, afterState, targetFinal : SystemState name key value world error} ->
    {source : Transitions initial sourceFinal} ->
    (current : Transitions initial currentFinal) -> (earlier : Transitions initial before) ->
    (left : Transition before middle) -> (right : Transition middle afterState) -> (later : Transitions afterState currentFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq current earlier left right later diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq (swappedTrace result) target) ->
    (correspondence : ActionRegistrationReplayCorrespondence name key world error value source current) ->
    (leftOrdinal, rightOrdinal : Nat) ->
    (0 leftExact : locatedActionOrdinal (replayActionOrigin correspondence (adjacentLeftNodeOccurrence result)) = leftOrdinal) ->
    (0 rightExact : locatedActionOrdinal (replayActionOrigin correspondence (adjacentRightNodeOccurrence result)) = rightOrdinal) ->
    (positions : List (Nat, Nat)) ->
    O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source
      (composeActionRegistrationReplayCorrespondence correspondence (swappedOccurrenceCorrespondence result)) rest positions ->
    O19GlobalCrossingPlan name key world error value protocol nameEq keyEq source correspondence
      (FiniteAdjacentSwapStep current earlier left right later orientation diamond result target rest)
      ((leftOrdinal, rightOrdinal) :: positions)
