module DGamma.CP5RawClosingRankSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Executable action observation; equality of ordinals is not a state cast.
public export
rawClosingActionAt :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {0 initial, finalState : SystemState name key value world error} ->
  Nat -> Transitions initial finalState -> Maybe (Action name key value world error)
rawClosingActionAt name key world error value ordinal NoTransitions = Nothing
rawClosingActionAt name key world error value Z (MoreTransitions (Fired nameEq keyEq action tag checked) rest) = Just action
rawClosingActionAt name key world error value (S ordinal) (MoreTransitions step rest) =
  rawClosingActionAt name key world error value ordinal rest

public export
0 rawClosingActionAtSplit :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {initial, before, afterState, finalState : SystemState name key value world error} ->
  (prior : Transitions initial before) -> (step : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  rawClosingActionAt name key world error value (transitionCount prior)
    (appendTransitions prior (MoreTransitions step later)) = Just (transitionAction step)
rawClosingActionAtSplit name key world error value NoTransitions
  (Fired nameEq keyEq action tag checked) later = Refl
rawClosingActionAtSplit name key world error value (MoreTransitions head tail) step later =
  rawClosingActionAtSplit name key world error value tail step later

public export
0 rawClosingActionAtLocated :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (action : Action name key value world error) ->
  (occurrence : LocatedActionOccurrence action trace) ->
  rawClosingActionAt name key world error value (locatedActionOrdinal occurrence) trace = Just action
rawClosingActionAtLocated name key world error value trace action occurrence =
  trans (cong (rawClosingActionAt name key world error value (locatedActionOrdinal occurrence))
    (sym (actionOccurrenceDecomposition occurrence)))
    (trans (rawClosingActionAtSplit name key world error value
      (beforeActionOccurrence occurrence) (locatedTransition occurrence) (afterActionOccurrence occurrence))
      (cong Just (locatedAction occurrence)))

||| Fresh raw names identify the immutable COMPONENT, not merely its rank.
public export
0 uniqueRawBirthComponents :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (left : LocatedActionOccurrence (OInsert selected leftParent leftComponent) trace) ->
  (right : LocatedActionOccurrence (OInsert selected rightParent rightComponent) trace) ->
  leftComponent = rightComponent
uniqueRawBirthComponents name key world error value nameEq keyEq trace unique
  selected leftParent rightParent leftComponent rightComponent left right =
    case justInjective
      (trans (sym (rawClosingActionAtLocated name key world error value trace
        (OInsert selected leftParent leftComponent) left))
        (trans (cong (\ordinal => rawClosingActionAt name key world error value ordinal trace)
          (uniqueInsertionPosition unique selected leftParent rightParent leftComponent rightComponent left right))
          (rawClosingActionAtLocated name key world error value trace
            (OInsert selected rightParent rightComponent) right))) of
      Refl => Refl


||| Only an actual O-Insert can fire at an absent owner.
public export
0 rawAbsentOwnerInsertion :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (actionOwner action) (registry before) = Nothing ->
  (parent : Parent name ** (component : Component key value world error **
    action = OInsert (actionOwner action) parent component))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (OInsert actor parent component) before afterState tag raw absent = (parent ** (component ** Refl))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (ORetire actor) before afterState tag raw absent =
    void (nothingIsNotJust (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (ORetire actor) before = Nothing)
      (rewrite absent in Refl))) raw))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (ORemove actor) before afterState tag raw absent =
    void (nothingIsNotJust (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (ORemove actor) before = Nothing)
      (rewrite absent in Refl))) raw))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (LBegin actor) before afterState tag raw absent =
    void (nothingIsNotJust (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (LBegin actor) before = Nothing)
      (rewrite absent in Refl))) raw))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (LAdvance actor) before afterState tag raw absent =
    void (nothingIsNotJust (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (LAdvance actor) before = Nothing)
      (rewrite absent in Refl))) raw))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (LDivert actor) before afterState tag raw absent =
    void (nothingIsNotJust (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (LDivert actor) before = Nothing)
      (rewrite absent in Refl))) raw))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (LLeave actor) before afterState tag raw absent =
    void (nothingIsNotJust (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (LLeave actor) before = Nothing)
      (rewrite absent in Refl))) raw))
rawAbsentOwnerInsertion name key world error value nameEq keyEq
  (LUnload actor) before afterState tag raw absent =
    void (nothingIsNotJust (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (LUnload actor) before = Nothing)
      (rewrite absent in Refl))) raw))


||| Structural observed-update rule. The update is an EXPLICIT argument, not a
||| computed scrutinee expected to refine rigid projections of a system state.
public export
0 rawImmutableComponentUpdate :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (property : name -> Component key value world error -> Type) ->
  (actor : name) -> (source, target : Registry name key value world error) ->
  (update : RegistryLocalUpdate name key world error value nameEq actor source target) ->
  ((next : Fiber name key value world error) ->
    (absent : lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} actor source = Nothing) ->
    target = insertBinding @{nameEq} actor next source absent -> property actor (fiberComponent next)) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected source = Just fiber -> property selected (fiberComponent fiber)) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected target = Just observed -> property selected (fiberComponent observed)
rawImmutableComponentUpdate name key world error value nameEq property actor source _
  (LocalInsert next absent) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (cong fiberComponent (justInjective (trans (sym (lookupInserted actor next source absent)) found)))
          (inserted next absent Refl)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalInsert next absent))) found)
rawImmutableComponentUpdate name key world error value nameEq property actor source _
  (LocalReplace {oldFiber} {oldFound} {staticComponent} next) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (trans (sym staticComponent) (cong fiberComponent
            (justInjective (trans (sym (lookupReplacedFiber actor oldFiber next source oldFound)) found))))
          (previous actor oldFiber oldFound)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalReplace {oldFiber} {oldFound} {staticComponent} next))) found)
rawImmutableComponentUpdate name key world error value nameEq property actor source _
  LocalDelete inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => void (nothingIsNotJust
          (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source)) found))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source LocalDelete)) found)
