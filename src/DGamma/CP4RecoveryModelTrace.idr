module DGamma.CP4RecoveryModelTrace

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryTrace
import DGamma.CP4RecoverySelectedStep
import Decidable.Equality

%default total

public export
OccurrenceEmbedding :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {segmentFirst, segmentLast, wholeFirst, wholeLast :
    SystemState name key value world error} ->
  Transitions segmentFirst segmentLast ->
  Transitions wholeFirst wholeLast -> Type
OccurrenceEmbedding segment whole =
  {stepBefore, stepAfter : SystemState name key value world error} ->
  (transition : Transition stepBefore stepAfter) ->
  OccursIn transition segment -> OccursIn transition whole

public export
0 tailOccurrenceEmbedding :
  (head : Transition first middle) ->
  (rest : Transitions middle last) ->
  (whole : Transitions wholeFirst wholeLast) ->
  OccurrenceEmbedding (MoreTransitions head rest) whole ->
  OccurrenceEmbedding rest whole
tailOccurrenceEmbedding head rest whole embedding transition occurs =
  embedding transition (OccursLater occurs)

public export
0 installedTraceStartEvidence :
  (trace : Transitions first last) ->
  InstalledTrace name key world error value nameEq keyEq selected trace ->
  installedAt @{nameEq} selected first = True
installedTraceStartEvidence NoTransitions (InstalledEnd installed) = installed
installedTraceStartEvidence
  (MoreTransitions {middle = middle} (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest installed tail) = installed

||| Temporal induction for the concrete lifecycle accumulator. Every foreign
||| step preserves the selected fiber object; every selected installed step is
||| handled by the exhaustive dispatcher, and each successful L-Advance adds
||| its exact yielded inverse occurrence to the factorization.
public export
0 accumulatorModelAlongSegment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (segment : Transitions first last) ->
  OccurrenceEmbedding segment whole ->
  InstalledTrace name key world error value nameEq keyEq selected segment ->
  AccumulatorModel name key world error value nameEq keyEq selected whole first ->
  AccumulatorModel name key world error value nameEq keyEq selected whole last
accumulatorModelAlongSegment nameEq keyEq selected whole NoTransitions embedding
  (InstalledEnd installed) model = model
accumulatorModelAlongSegment nameEq keyEq selected whole
  segment@(MoreTransitions {middle = middle} (Fired nameEq keyEq action tag checked) rest)
  embedding (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  model with (decEq @{nameEq} selected (actionOwner action))
  accumulatorModelAlongSegment nameEq keyEq selected whole
    segment@(MoreTransitions {middle = middle} (Fired nameEq keyEq action tag checked) rest)
    embedding
    (InstalledStep action tag checked rest sourceInstalled tailInstalled) model |
    No distinct =
      let nextModel = foreignStepPreservesAccumulatorModel nameEq keyEq selected
            action tag _ _ whole checked distinct model
          tailEmbedding : OccurrenceEmbedding rest whole
          tailEmbedding chosen occurs = embedding chosen (OccursLater occurs)
      in accumulatorModelAlongSegment nameEq keyEq selected whole rest
        tailEmbedding tailInstalled nextModel
  accumulatorModelAlongSegment nameEq keyEq selected whole
    segment@(MoreTransitions {middle = middle} (Fired nameEq keyEq action tag checked) rest)
    embedding
    (InstalledStep action tag checked rest sourceInstalled tailInstalled) model |
    Yes same =
      let 0 headInSegment : OccursIn
            (Fired {before = first} {afterState = middle}
              nameEq keyEq action tag checked)
            (MoreTransitions {middle = middle}
              (Fired {before = first} {afterState = middle}
                nameEq keyEq action tag checked) rest)
          headInSegment = OccursHere
          0 headOccurs : OccursIn
            (Fired {before = first} {afterState = middle}
              nameEq keyEq action tag checked) whole
          headOccurs = embedding
            (Fired {before = first} {afterState = middle}
              nameEq keyEq action tag checked) headInSegment
          0 targetInstalled : installedAt @{nameEq} selected middle = True
          targetInstalled = installedTraceStartEvidence rest tailInstalled
          0 nextModel : AccumulatorModel name key world error value nameEq keyEq
            selected whole middle
          nextModel = selectedInstalledStepPreservesAccumulatorModel nameEq keyEq
            selected action tag _ _ checked (sym same) whole headOccurs
            targetInstalled model
          tailEmbedding : OccurrenceEmbedding rest whole
          tailEmbedding chosen occurs = embedding chosen (OccursLater occurs)
      in accumulatorModelAlongSegment nameEq keyEq selected whole rest
        tailEmbedding tailInstalled nextModel

public export
0 identityOccurrenceEmbedding :
  (trace : Transitions first last) -> OccurrenceEmbedding trace trace
identityOccurrenceEmbedding trace transition occurs = occurs

||| The L-Begin model followed through every installed step of an episode
||| prefix. This closes the full control/accumulator temporal induction half of
||| Theorem 61 independently of foreign-effect commutation.
public export
0 episodePrefixAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (pre, current : SystemState name key value world error) ->
  (episode : EpisodePrefix name key world error value nameEq keyEq selected pre
    current) ->
  AccumulatorModel name key world error value nameEq keyEq selected
    (prefixTransitions episode) current
episodePrefixAccumulatorModel nameEq keyEq selected pre current episode =
  let initialModel = beginAccumulatorModel nameEq keyEq selected
        (inside episode) (opening episode)
  in accumulatorModelAlongSegment nameEq keyEq selected (inside episode)
    (inside episode) (identityOccurrenceEmbedding (inside episode))
    (insideInstalled episode) initialModel
