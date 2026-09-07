module DGamma.CP5ImmutableBirthMetadataSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Parent and component are immutable through actual non-birth updates.
||| Retirement is deliberately excluded: the frozen evaluator may change it.
public export
0 rawImmutableMetadataUpdate :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (property : name -> (Parent name, Component key value world error) -> Type) ->
  (actor : name) -> (source, target : Registry name key value world error) ->
  (update : RegistryLocalUpdate name key world error value nameEq actor source target) ->
  ((next : Fiber name key value world error) ->
    (absent : lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} actor source = Nothing) ->
    target = insertBinding @{nameEq} actor next source absent -> property actor (fiberParent next, fiberComponent next)) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected source = Just fiber -> property selected (fiberParent fiber, fiberComponent fiber)) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected target = Just observed -> property selected (fiberParent observed, fiberComponent observed)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  (LocalInsert next absent) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (cong (\fiber => (fiberParent fiber, fiberComponent fiber)) (justInjective (trans (sym (lookupInserted actor next source absent)) found)))
          (inserted next absent Refl)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalInsert next absent))) found)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  (LocalReplace {oldFiber} {oldFound} {staticComponent} {staticParent} next) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (trans (sym (cong2 MkPair staticParent staticComponent)) (cong (\fiber => (fiberParent fiber, fiberComponent fiber))
            (justInjective (trans (sym (lookupReplacedFiber actor oldFiber next source oldFound)) found))))
          (previous actor oldFiber oldFound)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalReplace {oldFiber} {oldFound} {staticComponent} {staticParent} next))) found)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  LocalDelete inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => void (nothingIsNotJust
          (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source)) found))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source LocalDelete)) found)

||| Authenticate both immutable endpoint fields at the actual original birth.
public export
0 rawMetadataBirthStep :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (occurrence : LocatedActionOccurrence action global) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry before) = Just fiber ->
    LocatedActionOccurrence (OInsert selected (fiberParent fiber) (fiberComponent fiber)) global) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry afterState) = Just observed ->
  LocatedActionOccurrence (OInsert selected (fiberParent observed) (fiberComponent observed)) global
rawMetadataBirthStep name key world error value nameEq keyEq global action
  before afterState tag raw occurrence sourceBirth =
    rawImmutableMetadataUpdate name key world error value nameEq
      (\selected, metadata => LocatedActionOccurrence
        (OInsert selected (fst metadata) (snd metadata)) global)
      (actionOwner action) (registry before) (registry afterState)
      (systemRegistryUpdate (applyActionLocalUpdate nameEq keyEq action before afterState tag raw))
      (\next, absent, targetIsInsert =>
        case rawAbsentOwnerInsertion name key world error value nameEq keyEq action
          before afterState tag raw absent of
          (parent ** (component ** inserted)) =>
            replace {p = \metadata => LocatedActionOccurrence
              (OInsert (actionOwner action) (fst metadata) (snd metadata)) global}
              (cong (\fiber => (fiberParent fiber, fiberComponent fiber)) (justInjective
                (trans (sym (oInsertResultLookup nameEq keyEq (actionOwner action) parent component
                  before afterState tag (replace
                    {p = \chosen => applyAction @{nameEq} @{keyEq} chosen before = Just (tag, afterState)}
                    inserted raw)))
                  (trans (cong (lookupFiber @{nameEq} (actionOwner action)) targetIsInsert)
                    (lookupInserted (actionOwner action) next (registry before) absent)))))
              (replace {p = \chosen => LocatedActionOccurrence chosen global} inserted occurrence))
      sourceBirth

||| Forward induction retains actual birth locations and exact immutable metadata.
public export
0 rawMetadataBirthInvariant :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState, first, last : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (segment : Transitions first last) ->
  AlignedTransitions name key world error value nameEq keyEq segment ->
  ((action : Action name key value world error) ->
    LocatedActionOccurrence action segment -> LocatedActionOccurrence action global) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry first) = Just fiber ->
    LocatedActionOccurrence
      (OInsert selected (fiberParent fiber) (fiberComponent fiber)) global) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry last) = Just observed ->
  LocatedActionOccurrence
    (OInsert selected (fiberParent observed) (fiberComponent observed)) global
rawMetadataBirthInvariant name key world error value nameEq keyEq global
  NoTransitions AlignedEnd embedding previous = previous
rawMetadataBirthInvariant name key world error value nameEq keyEq global
  (MoreTransitions head rest) aligned embedding previous =
    case aligned of
      AlignedStep action tag checked _ alignedRest =>
        rawMetadataBirthInvariant name key world error value nameEq keyEq global rest alignedRest
          (\wanted, occurrence => embedding wanted (case occurrence of
            MkLocatedActionOccurrence before afterState prior step later actionExact decomposition =>
              MkLocatedActionOccurrence before afterState (MoreTransitions (Fired nameEq keyEq action tag checked) prior) step later
                actionExact (cong (MoreTransitions (Fired nameEq keyEq action tag checked)) decomposition)))
          (rawMetadataBirthStep name key world error value nameEq keyEq global action _ _ tag
            (checkedActionProjects nameEq keyEq action _ _ tag checked)
            (embedding action (MkLocatedActionOccurrence _ _ NoTransitions (Fired nameEq keyEq action tag checked) rest Refl Refl)) previous)

||| Any actual prefix lookup identifies a birth of this exact parent and component.
public export
0 rawMetadataBirthAtPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prior : Transitions initial middle) -> (later : Transitions middle finalState) ->
  appendTransitions prior later = global ->
  AlignedTransitions name key world error value nameEq keyEq prior ->
  bindings (registry initial) = [] ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry middle) = Just observed ->
  LocatedActionOccurrence
    (OInsert selected (fiberParent observed) (fiberComponent observed)) global
rawMetadataBirthAtPrefix name key world error value nameEq keyEq {initial}
  global prior later decomposition aligned empty =
    rawMetadataBirthInvariant name key world error value nameEq keyEq global prior aligned
      (\action, occurrence => replace {p = \whole => LocatedActionOccurrence action whole} decomposition
        (case occurrence of
          MkLocatedActionOccurrence before afterState pre step post actionExact split =>
            MkLocatedActionOccurrence before afterState pre step (appendTransitions post later) actionExact
              (trans (sym (appendTransitionsAssociative pre (MoreTransitions step post) later))
                (cong (\whole => appendTransitions whole later) split))))
      (\selected, fiber, found =>
        case emptyRegistryProtocolRanked (emptyRegistrationProtocol {key = key} {value = value}
          {world = world} {error = error}) nameEq initial empty selected fiber found of
          (rank ** ranked) => void (nothingIsNotJust ranked))

||| Uniqueness compares two authenticated births, yielding both immutable fields.
public export
0 uniqueRawBirthMetadata :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (left : LocatedActionOccurrence (OInsert selected leftParent leftComponent) trace) ->
  (right : LocatedActionOccurrence (OInsert selected rightParent rightComponent) trace) ->
  (leftParent, leftComponent) = (rightParent, rightComponent)
uniqueRawBirthMetadata name key world error value nameEq keyEq trace unique
  selected leftParent rightParent leftComponent rightComponent left right =
    case justInjective
      (trans (sym (rawClosingActionAtLocated name key world error value trace
        (OInsert selected leftParent leftComponent) left))
        (trans (cong (\ordinal => rawClosingActionAt name key world error value ordinal trace)
          (uniqueInsertionPosition unique selected leftParent rightParent leftComponent rightComponent left right))
          (rawClosingActionAtLocated name key world error value trace
            (OInsert selected rightParent rightComponent) right))) of
      Refl => Refl
