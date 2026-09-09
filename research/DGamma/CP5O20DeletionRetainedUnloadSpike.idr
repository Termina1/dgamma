module DGamma.CP5O20DeletionRetainedUnloadSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A checked native Unload cannot belong to a registered generation known
||| Inactive at that exact scanner boundary. No raw-name-global exclusion is used.
export
0 o20RegisteredUnloadImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) -> (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (applyAction @{nameEq} @{keyEq} (LUnload actor) before = Just (tag, afterState)) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered live before ->
  GenerationOwnedActor nameEq registered ordinal live (the (Action name key value world error) (LUnload actor)) -> Void
o20RegisteredUnloadImpossible name key world error value nameEq keyEq registered ordinal live
  actor before afterState tag raw inactive owned =
    inactiveCannotUnload nameEq keyEq actor before afterState tag raw
      (inactive actor (fst owned) (snd (snd owned)) (fst (snd owned)))

||| Every native source step excludes an Unload owned by an exact registered
||| generation, using the continuously advanced ORIGINAL scanner environment.
public export
data O20RegisteredUnloadFree :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  O20RegisteredUnloadEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {registered : List (RegistrationGeneration name)} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {state : SystemState name key value world error} ->
    O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
      (the (Transitions state state) NoTransitions)
  O20RegisteredUnloadStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {registered : List (RegistrationGeneration name)} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 excludes : (actor : name) -> (transitionAction step = LUnload actor) ->
      GenerationOwnedActor nameEq registered ordinal live (transitionAction step) -> Void) ->
    (0 tail : O20RegisteredUnloadFree name key world error value nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) rest) ->
    O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
      (MoreTransitions step rest)

||| Specialize a raw action only along its explicit Unload equation; the
||| registered exclusion remains generation-scoped at the same native cut.
export
0 o20RegisteredActionNotUnload :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered live before ->
  (actor : name) -> (action = LUnload actor) ->
  GenerationOwnedActor nameEq registered ordinal live action -> Void
o20RegisteredActionNotUnload name key world error value nameEq keyEq registered ordinal live
  _ before afterState tag raw inactive actor Refl owned =
    o20RegisteredUnloadImpossible name key world error value nameEq keyEq registered ordinal live
      actor before afterState tag raw inactive owned

||| One aligned source edge produces Unload exclusion and advances both
||| unique generation state and the native registered-Inactive invariant.
export
0 o20RegisteredUnloadFreeHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (IsBeginAction (transitionAction step) ->
    GenerationOwnedActor nameEq registered ordinal live (transitionAction step) -> Void) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered live first ->
  (AlignedTransitions name key world error value nameEq keyEq rest ->
    GenerationEnvironmentNamesUnique
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) ->
    CurrentRegisteredInactiveFibers name key world error value nameEq registered
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) middle ->
    O20RegisteredUnloadFree name key world error value nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) rest) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest) ->
  O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
    (MoreTransitions step rest)
o20RegisteredUnloadFreeHead name key world error value nameEq keyEq registered ordinal live unique
  {first} {middle} _ _ noBegin inactive continue (AlignedStep action tag checked rest alignedRest) =
    O20RegisteredUnloadStep (Fired nameEq keyEq action tag checked) rest
      (o20RegisteredActionNotUnload name key world error value nameEq keyEq registered ordinal live
        action first middle tag (checkedActionProjects nameEq keyEq action first middle tag checked) inactive)
      (continue alignedRest
        (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action live unique)
        (currentRegisteredInactiveStep nameEq keyEq registered ordinal live unique action first middle tag
          (checkedActionProjects nameEq keyEq action first middle tag checked) noBegin inactive))

||| Whole aligned source induction: the authentic no-registered-Begin
||| certificate and initial Inactive invariant forbid registered Unloads.
export
0 o20RegisteredUnloadFreeTrace :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq registered ordinal live trace ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered live first ->
  O20RegisteredUnloadFree name key world error value nameEq registered ordinal live trace
o20RegisteredUnloadFreeTrace name key world error value nameEq keyEq registered ordinal live unique
  _ aligned NoRegisteredEpisodeEnd inactive = O20RegisteredUnloadEnd
o20RegisteredUnloadFreeTrace name key world error value nameEq keyEq registered ordinal live unique
  _ aligned (NoRegisteredEpisodeStep step rest noBegin tail) inactive =
    o20RegisteredUnloadFreeHead name key world error value nameEq keyEq registered ordinal live unique
      step rest noBegin inactive
      (\alignedRest, nextUnique, nextInactive =>
        o20RegisteredUnloadFreeTrace name key world error value nameEq keyEq registered (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live)
          nextUnique rest alignedRest tail nextInactive) aligned

||| The actual deletable candidate owns whole-source registered-Unload
||| exclusion. The initial invariant is produced at the empty generation scan;
||| no future-Unload retention or per-action exclusion is supplied by the caller.
export
0 o20DeletionRegisteredUnloadFree :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  O20RegisteredUnloadFree name key world error value nameEq (selectedRegistrations candidate) Z [] trace
o20DeletionRegisteredUnloadFree name key world error value protocol nameEq keyEq {initial}
  trace premises candidate =
    o20RegisteredUnloadFreeTrace name key world error value nameEq keyEq
      (selectedRegistrations candidate) Z [] UniqueNil trace (replayAligned (chainReplayCapital premises))
      (selectedChildrenHaveNoEpisode candidate)
      (reachedCurrentRegisteredInactive {name} {key} {world} {error} {value}
        nameEq keyEq (selectedRegistrations candidate)
        (the (Transitions initial initial) NoTransitions) Z [] GenerationTraceScanEnd AlignedEnd NoRegisteredEpisodeEnd)

||| Read only the native head's registered-Unload exclusion from its
||| source-indexed certificate. No discarded history is inferred here.
export
0 o20RegisteredUnloadHeadExcludes :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {registered : List (RegistrationGeneration name)} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {step : Transition first middle} -> {rest : Transitions middle finalState} ->
  O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
    (MoreTransitions step rest) ->
  (actor : name) -> (transitionAction step = LUnload actor) ->
  GenerationOwnedActor nameEq registered ordinal live (transitionAction step) -> Void
o20RegisteredUnloadHeadExcludes (O20RegisteredUnloadStep step rest excludes tail) = excludes

||| The tail exclusion uses the ORIGINAL head's advanced generation state,
||| including when that head will be absent from the filtered trace.
export
0 o20RegisteredUnloadFreeTail :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {registered : List (RegistrationGeneration name)} ->
  {ordinal : Nat} -> {live : GenerationEnvironment name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {step : Transition first middle} -> {rest : Transitions middle finalState} ->
  O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
    (MoreTransitions step rest) ->
  O20RegisteredUnloadFree name key world error value nameEq registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) rest
o20RegisteredUnloadFreeTail (O20RegisteredUnloadStep step rest excludes tail) = tail

||| Keep an actual Unload occurrence across a retained physical head.
||| Head equality is the subsequence producer's equation; tail retention is
||| the structural induction result, not an assumed zero edge.
export
0 o20UnloadOccursThroughKeptHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState, otherFirst, otherMiddle, otherFinal : SystemState name key value world error} ->
  (actor : name) -> (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (kept : Transition otherFirst otherMiddle) -> (later : Transitions otherMiddle otherFinal) ->
  (transitionAction step = transitionAction kept) ->
  (ActionOccurs (LUnload actor) rest -> ActionOccurs (LUnload actor) later) ->
  ActionOccurs (LUnload actor) (MoreTransitions step rest) ->
  ActionOccurs (LUnload actor) (MoreTransitions kept later)
o20UnloadOccursThroughKeptHead actor _ _ kept later same continue (ActionOccursHere step rest exact) =
  ActionOccursHere kept later (trans (sym same) exact)
o20UnloadOccursThroughKeptHead actor _ _ kept later same continue (ActionOccursLater step rest occurs) =
  ActionOccursLater kept later (continue occurs)

||| A genuinely deleted non-Unload head cannot consume the given Unload
||| occurrence. Only the occurrence is eliminated; its later case is retained.
export
0 o20UnloadOccursPastDeletedHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  (actor : name) -> (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (later : Transitions otherFirst otherFinal) ->
  Not (transitionAction step = LUnload actor) ->
  (ActionOccurs (LUnload actor) rest -> ActionOccurs (LUnload actor) later) ->
  ActionOccurs (LUnload actor) (MoreTransitions step rest) -> ActionOccurs (LUnload actor) later
o20UnloadOccursPastDeletedHead actor _ _ later excludes continue (ActionOccursHere step rest exact) =
  void (excludes exact)
o20UnloadOccursPastDeletedHead actor _ _ later excludes continue (ActionOccursLater step rest occurs) =
  continue occurs
