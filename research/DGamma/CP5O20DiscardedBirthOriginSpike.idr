module DGamma.CP5O20DiscardedBirthOriginSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DiscardedSelectionCoverageSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A discarded stamp was either in the incoming scanner index or was born
||| at an exact occurrence of THIS suffix whose actual parent later Unloads.
||| The flat family carries no selection, canonical absence or coverage oracle.
public export
data O20DiscardedTraceOrigin :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (incoming : List (RegistrationGeneration name)) ->
  (generation : RegistrationGeneration name) -> Transitions first finalState -> Type where
  O20DiscardedBefore :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, finalState : SystemState name key value world error} ->
    {ordinal : Nat} -> {incoming : List (RegistrationGeneration name)} ->
    {generation : RegistrationGeneration name} -> {trace : Transitions first finalState} ->
    (0 member : Elem generation incoming) ->
    O20DiscardedTraceOrigin name key world error value ordinal incoming generation trace
  O20DiscardedWithin :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, finalState : SystemState name key value world error} ->
    {ordinal : Nat} -> {incoming : List (RegistrationGeneration name)} ->
    {generation : RegistrationGeneration name} -> {trace : Transitions first finalState} ->
    (0 child, parent : name) -> (0 component : Component key value world error) ->
    (0 birth : LocatedGeneratedRegistration child parent component trace) ->
    (0 exact : (generation = MkRegistrationGeneration child (ordinal + registrationOrdinal birth))) ->
    (0 closing : ActionOccurs (LUnload parent) (afterRegistration birth)) ->
    O20DiscardedTraceOrigin name key world error value ordinal incoming generation trace

||| Prepend the actual native head to a tail-origin packet when its incoming
||| discarded list is unchanged. A within-tail birth retains its exact suffix
||| and closing occurrence; the arithmetic transports only its ordinal count.
export
0 o20DiscardedOriginPrepend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (incoming, observed : List (RegistrationGeneration name)) ->
  (generation : RegistrationGeneration name) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (observed = incoming) ->
  O20DiscardedTraceOrigin name key world error value (S ordinal) observed generation rest ->
  O20DiscardedTraceOrigin name key world error value ordinal incoming generation (MoreTransitions step rest)
o20DiscardedOriginPrepend name key world error value ordinal incoming observed generation step rest unchanged (O20DiscardedBefore member) =
  O20DiscardedBefore (replace {p = Elem generation} unchanged member)
o20DiscardedOriginPrepend name key world error value ordinal incoming observed generation step rest unchanged
  (O20DiscardedWithin child parent component birth exact closing) =
    O20DiscardedWithin child parent component
      (MkLocatedGeneratedRegistration (registrationBefore birth) (registrationAfter birth)
        (MoreTransitions step (beforeRegistration birth)) (registrationTransition birth)
        (afterRegistration birth) (registrationAction birth)
        (cong (MoreTransitions step) (registrationDecomposition birth)))
      (trans exact (cong (MkRegistrationGeneration child) (plusSuccRightSucc ordinal (registrationOrdinal birth)))) closing

||| A member of the actual newly-prepended discarded list is either this
||| checked birth or a previous discarded stamp. Only membership is eliminated.
export
0 o20DiscardedNewHeadOrigin :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (incoming : List (RegistrationGeneration name)) ->
  (generation : RegistrationGeneration name) -> (child, parent : name) ->
  (component : Component key value world error) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (transitionAction step = OInsert child (ChildOf parent) component) ->
  ActionOccurs (LUnload parent) rest ->
  Elem generation (MkRegistrationGeneration child ordinal :: incoming) ->
  O20DiscardedTraceOrigin name key world error value ordinal incoming generation (MoreTransitions step rest)
o20DiscardedNewHeadOrigin name key world error value {first} {middle} ordinal incoming _ child parent component step rest actionExact closing Here =
  O20DiscardedWithin child parent component
    (MkLocatedGeneratedRegistration first middle NoTransitions step rest actionExact Refl)
    (cong (MkRegistrationGeneration child) (sym (plusZeroRightNeutral ordinal))) closing
o20DiscardedNewHeadOrigin name key world error value ordinal incoming generation child parent component step rest actionExact closing (There member) =
  O20DiscardedBefore member

||| Lift the tail packet through the ACTUAL discard constructor. A previous
||| index member is resolved against that same head; a later birth keeps its
||| own suffix and count. No selection or withdrawal inference is performed.
export
0 o20DiscardedOriginAfterDiscard :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (incoming : List (RegistrationGeneration name)) ->
  (generation : RegistrationGeneration name) -> (child, parent : name) ->
  (component : Component key value world error) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (transitionAction step = OInsert child (ChildOf parent) component) ->
  ActionOccurs (LUnload parent) rest ->
  O20DiscardedTraceOrigin name key world error value (S ordinal)
    (MkRegistrationGeneration child ordinal :: incoming) generation rest ->
  O20DiscardedTraceOrigin name key world error value ordinal incoming generation (MoreTransitions step rest)
o20DiscardedOriginAfterDiscard name key world error value ordinal incoming generation child parent component step rest actionExact closing (O20DiscardedBefore member) =
  o20DiscardedNewHeadOrigin name key world error value ordinal incoming generation child parent component step rest actionExact closing member
o20DiscardedOriginAfterDiscard name key world error value ordinal incoming generation child parent component step rest actionExact closing
  (O20DiscardedWithin laterChild laterParent laterComponent birth exact laterClosing) =
    o20DiscardedOriginPrepend name key world error value ordinal incoming incoming generation step rest Refl
      (O20DiscardedWithin laterChild laterParent laterComponent birth exact laterClosing)

||| Reverse coverage of the actual discarded index through EVERY public
||| bilateral scanner constructor. This produces the native birth and future
||| Unload when not already incoming; it does not assume a discard classifier.
export
0 o20DiscardedOriginScan :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (mapping : RegistrationGenerationBijection name) ->
  (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
  (rightOrdinal : Nat) -> (rightIndex : RegistrationIndexState name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (leftFinalIndex, rightFinalIndex : RegistrationIndexState name) ->
  {pendingLeft, pendingRight : List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq mapping leftOrdinal leftIndex left leftFinalIndex
    rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight ->
  (generation : RegistrationGeneration name) -> Elem generation (indexedDeletedGenerations leftFinalIndex) ->
  O20DiscardedTraceOrigin name key world error value leftOrdinal
    (indexedDeletedGenerations leftIndex) generation left
o20DiscardedOriginScan name key world error value nameEq mapping leftOrdinal
  (MkRegistrationIndexState live activations counts discarded) rightOrdinal rightIndex
  left right leftFinalIndex rightFinalIndex correspondence generation member = case correspondence of
    RegistrationCorrespondenceEnd => O20DiscardedBefore member
    SkipLeftNonRegistration action step rest actionExact nonRegistration tail =>
      o20DiscardedOriginPrepend name key world error value leftOrdinal discarded
        (indexedDeletedGenerations (advanceRegistrationIndex @{nameEq} leftOrdinal action (MkRegistrationIndexState live activations counts discarded)))
        generation step rest
        (o20IndexDiscardedAdvance name key world error value nameEq leftOrdinal action
          (MkRegistrationIndexState live activations counts discarded))
        (o20DiscardedOriginScan name key world error value nameEq mapping (S leftOrdinal)
          (advanceRegistrationIndex @{nameEq} leftOrdinal action (MkRegistrationIndexState live activations counts discarded))
          rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail generation member)
    DiscardLeftDeletedRegistration {child} {parent} {component} step rest actionExact closing tail =>
      o20DiscardedOriginAfterDiscard name key world error value leftOrdinal discarded generation child parent component
        step rest actionExact (deletedParentEpisodeCloses closing)
        (o20DiscardedOriginScan name key world error value nameEq mapping (S leftOrdinal)
          (advanceDeletedRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts discarded))
          rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail generation member)
    QueueLeftGeneratedRegistration {child} {parent} {component} step rest actionExact retained tail =>
      o20DiscardedOriginPrepend name key world error value leftOrdinal discarded
        (indexedDeletedGenerations (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts discarded)))
        generation step rest
        (o20SurvivingDiscardedObserved name key world error value nameEq leftOrdinal child parent component
          live activations counts discarded (lookupParentActivation @{nameEq} parent activations) Refl)
        (o20DiscardedOriginScan name key world error value nameEq mapping (S leftOrdinal)
          (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts discarded))
          rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail generation member)
    MatchLeftWithPendingRight {child} {parent} {component} step rest actionExact retained priorWords event laterWords matched tail =>
      o20DiscardedOriginPrepend name key world error value leftOrdinal discarded
        (indexedDeletedGenerations (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts discarded)))
        generation step rest
        (o20SurvivingDiscardedObserved name key world error value nameEq leftOrdinal child parent component
          live activations counts discarded (lookupParentActivation @{nameEq} parent activations) Refl)
        (o20DiscardedOriginScan name key world error value nameEq mapping (S leftOrdinal)
          (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts discarded))
          rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail generation member)
    SkipRightNonRegistration action step rest actionExact nonRegistration tail =>
      o20DiscardedOriginScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceRegistrationIndex @{nameEq} rightOrdinal action rightIndex)
        left rest leftFinalIndex rightFinalIndex tail generation member
    DiscardRightDeletedRegistration {child} {parent} {component} step rest actionExact closing tail =>
      o20DiscardedOriginScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceDeletedRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex)
        left rest leftFinalIndex rightFinalIndex tail generation member
    QueueRightGeneratedRegistration {child} {parent} {component} step rest actionExact retained tail =>
      o20DiscardedOriginScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex)
        left rest leftFinalIndex rightFinalIndex tail generation member
    MatchRightWithPendingLeft {child} {parent} {component} step rest actionExact retained priorWords event laterWords matched tail =>
      o20DiscardedOriginScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex)
        left rest leftFinalIndex rightFinalIndex tail generation member
