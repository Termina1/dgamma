module DGamma.CP4DeletionGenerationFilter

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Decidable.Equality

%default total

justInjectiveFilter : Just left = Just right -> left = right
justInjectiveFilter Refl = Refl

||| Constructive decision procedure for exact generation ownership.
public export
decGenerationOwnedActor :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  Dec (GenerationOwnedActor nameEq registered ordinal live action)
decGenerationOwnedActor nameEq registered ordinal live action
  with (actionGenerationAt @{nameEq} ordinal live action)
  decGenerationOwnedActor nameEq registered ordinal live action | Nothing =
    No (\(generation ** (found, member)) => case found of Refl impossible)
  decGenerationOwnedActor nameEq registered ordinal live action |
    Just generation with (isElem generation registered)
    decGenerationOwnedActor nameEq registered ordinal live action |
      Just generation | Yes member = Yes (generation ** (Refl, member))
    decGenerationOwnedActor nameEq registered ordinal live action |
      Just generation | No absent =
        No (\(observed ** (found, member)) =>
          let same = justInjectiveFilter found
          in case same of Refl => absent member)

lifecycleActionTrue :
  (action : Action name key value world error) ->
  Dec (isLifecycleAction action = True)
lifecycleActionTrue action = decEq (isLifecycleAction action) True

||| Constructive decision procedure for the generation-repaired Lemma-72
||| deletion predicate. The two constructors are intentionally overlapping: a
||| lifecycle action of an R generation may be deleted for either reason.
public export
decEpisodeGenerationDeletedActor :
  (nameEq : DecEq name) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  Dec (EpisodeGenerationDeletedActor nameEq selected registered ordinal live
    action)
decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action
  with (decEq @{nameEq} (actionOwner action) selected)
  decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
    Yes owner with (lifecycleActionTrue action)
    decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
      Yes owner | Yes lifecycle =
        Yes (DeleteEpisodeGenerationLifecycle owner lifecycle)
    decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
      Yes owner | No notLifecycle
      with (decGenerationOwnedActor nameEq registered ordinal live action)
      decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
        Yes owner | No notLifecycle | Yes generated =
          Yes (DeleteRegisteredGeneration generated)
      decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
        Yes owner | No notLifecycle | No notGenerated =
          No (\deleted => case deleted of
            DeleteEpisodeGenerationLifecycle observedOwner lifecycle =>
              notLifecycle lifecycle
            DeleteRegisteredGeneration generated => notGenerated generated)
  decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
    No notOwner
    with (decGenerationOwnedActor nameEq registered ordinal live action)
    decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
      No notOwner | Yes generated = Yes (DeleteRegisteredGeneration generated)
    decEpisodeGenerationDeletedActor nameEq selected registered ordinal live action |
      No notOwner | No notGenerated =
        No (\deleted => case deleted of
          DeleteEpisodeGenerationLifecycle owner lifecycle => notOwner owner
          DeleteRegisteredGeneration generated => notGenerated generated)

||| `TransitionResult` intentionally hides the action it fired. Filtering needs
||| that equality in the `KeepGenerationAction` constructor, so this local
||| package retains it without changing the runtime LTS interface.
public export
record NamedTransition
  (name, key, world, error : Type) (value : key -> Type)
  (action : Action name key value world error)
  (before : SystemState name key value world error) where
  constructor MkNamedTransition
  namedAfter : SystemState name key value world error
  namedTag : RuleTag
  namedTransition : Transition before namedAfter
  0 namedAction : transitionAction namedTransition = action

public export
fireNamed :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  Maybe (NamedTransition name key world error value action before)
fireNamed nameEq keyEq action before
  with (checkedApplyAction @{nameEq} @{keyEq} action before) proof checked
  fireNamed nameEq keyEq action before | Nothing = Nothing
  fireNamed nameEq keyEq action before | Just (tag, afterState) =
    Just (MkNamedTransition afterState tag
      (Fired nameEq keyEq action tag checked) Refl)

public export
0 fireNamedNothingImpliesCheckedNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  fireNamed nameEq keyEq action before = Nothing ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Nothing
fireNamedNothingImpliesCheckedNothing nameEq keyEq action before fired
  with (checkedApplyAction @{nameEq} @{keyEq} action before) proof checked
  fireNamedNothingImpliesCheckedNothing nameEq keyEq action before fired |
    Nothing = Refl
  fireNamedNothingImpliesCheckedNothing nameEq keyEq action before fired |
    Just (tag, afterState) = case fired of Refl impossible

||| Existential output of the executable generation filter. The survivor trace
||| and the bidirectional keep/delete witness are constructed together, so the
||| output cannot silently retain a deletable action.
public export
record GenerationFilterResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type)
  (ordinal : Nat) (live : GenerationEnvironment name)
  {originalFirst, originalFinal : SystemState name key value world error}
  (original : Transitions originalFirst originalFinal)
  (survivingFirst : SystemState name key value world error) where
  constructor MkGenerationFilterResult
  survivingFinal : SystemState name key value world error
  surviving : Transitions survivingFirst survivingFinal
  0 filteredSubsequence : GenerationActionSubsequence nameEq deletable ordinal
    live original surviving

||| Total constructive filter for `GenerationActionSubsequence`. A `Nothing`
||| result means exactly that a kept action did not fire at the smaller replay
||| state; later control lemmas discharge those cases for Lemma 72.
public export
0 filterGenerationActions :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (decDeletable : (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    (action : Action name key value world error) ->
    Dec (deletable ordinal live action)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  Maybe (GenerationFilterResult name key world error value nameEq deletable
    ordinal live original survivingFirst)
filterGenerationActions {name} {key} {world} {error} {value}
  nameEq keyEq deletable decDeletable ordinal live NoTransitions survivingFirst =
    Just (MkGenerationFilterResult survivingFirst NoTransitions
      GenerationActionSubsequenceEnd)
filterGenerationActions {name} {key} {world} {error} {value}
  nameEq keyEq deletable decDeletable ordinal live
  (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked)
    originalRest) survivingFirst
  with (decDeletable ordinal live action)
  filterGenerationActions nameEq keyEq deletable decDeletable ordinal live
    (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked)
      originalRest) survivingFirst | Yes deleteHead =
        case filterGenerationActions nameEq keyEq deletable decDeletable
          (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          originalRest survivingFirst of
          Nothing => Nothing
          Just (MkGenerationFilterResult finalState survivor tailWitness) =>
            Just (MkGenerationFilterResult finalState survivor
              (DeleteGenerationAction
                (Fired stepNameEq stepKeyEq action tag checked) originalRest
                deleteHead tailWitness))
  filterGenerationActions nameEq keyEq deletable decDeletable ordinal live
    (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked)
      originalRest) survivingFirst | No keepHead =
        case fireNamed nameEq keyEq action survivingFirst of
          Nothing => Nothing
          Just (MkNamedTransition nextState survivorTag survivorTransition sameAction) =>
            case filterGenerationActions nameEq keyEq deletable decDeletable
              (S ordinal)
              (advanceGenerationEnvironment @{nameEq} ordinal action live)
              originalRest nextState of
              Nothing => Nothing
              Just (MkGenerationFilterResult finalState survivorRest tailWitness) =>
                Just (MkGenerationFilterResult finalState
                  (MoreTransitions survivorTransition survivorRest)
                  (KeepGenerationAction
                    (Fired stepNameEq stepKeyEq action tag checked) originalRest
                    survivorTransition survivorRest keepHead (sym sameAction)
                    tailWitness))

||| Selected-episode specialization used by the Lemma-72 proof.
public export
0 filterSelectedEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  Maybe (GenerationFilterResult name key world error value nameEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    ordinal live original survivingFirst)
filterSelectedEpisode {name} {key} {world} {error} {value}
  nameEq keyEq selected registered ordinal live original survivingFirst =
    filterGenerationActions nameEq keyEq
      (EpisodeGenerationDeletedActor nameEq selected registered)
      (decEpisodeGenerationDeletedActor nameEq selected registered)
      ordinal live original survivingFirst

||| Prefix/suffix specialization deleting exact R generations.
public export
0 filterRegisteredGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  Maybe (GenerationFilterResult name key world error value nameEq
    (GenerationOwnedActor nameEq registered)
    ordinal live original survivingFirst)
filterRegisteredGenerations {name} {key} {world} {error} {value}
  nameEq keyEq registered ordinal live original survivingFirst =
    filterGenerationActions nameEq keyEq
      (GenerationOwnedActor nameEq registered)
      (decGenerationOwnedActor nameEq registered)
      ordinal live original survivingFirst
