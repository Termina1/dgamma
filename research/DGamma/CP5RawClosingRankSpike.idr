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


||| Actual evaluator producer for the explicit-update invariant. The computed
||| update is only PASSED to the structural helper; never eliminated here.
public export
0 rawComponentBirthStep :
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
    (parent : Parent name ** LocatedActionOccurrence
      (OInsert selected parent (fiberComponent fiber)) global)) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry afterState) = Just observed ->
  (parent : Parent name ** LocatedActionOccurrence
    (OInsert selected parent (fiberComponent observed)) global)
rawComponentBirthStep name key world error value nameEq keyEq global action
  before afterState tag raw occurrence sourceBirth =
    rawImmutableComponentUpdate name key world error value nameEq
      (\selected, component => (parent : Parent name **
        LocatedActionOccurrence (OInsert selected parent component) global))
      (actionOwner action) (registry before) (registry afterState)
      (systemRegistryUpdate (applyActionLocalUpdate nameEq keyEq action before afterState tag raw))
      (\next, absent, targetIsInsert =>
        case rawAbsentOwnerInsertion name key world error value nameEq keyEq action
          before afterState tag raw absent of
          (parent ** (component ** inserted)) =>
            (parent ** replace
              {p = \chosen => LocatedActionOccurrence (OInsert (actionOwner action) parent chosen) global}
              (cong fiberComponent (justInjective
                (trans (sym (oInsertResultLookup nameEq keyEq (actionOwner action) parent component
                  before afterState tag (replace
                    {p = \chosen => applyAction @{nameEq} @{keyEq} chosen before = Just (tag, afterState)}
                    inserted raw)))
                  (trans (cong (lookupFiber @{nameEq} (actionOwner action)) targetIsInsert)
                    (lookupInserted (actionOwner action) next (registry before) absent)))))
              (replace {p = \chosen => LocatedActionOccurrence chosen global} inserted occurrence)))
      sourceBirth


||| Forward trace induction preserves authentic birth locations in one fixed
||| global trace. The embedding is structural inclusion, not generation casting.
public export
0 rawComponentBirthInvariant :
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
    (parent : Parent name ** LocatedActionOccurrence
      (OInsert selected parent (fiberComponent fiber)) global)) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry last) = Just observed ->
  (parent : Parent name ** LocatedActionOccurrence
    (OInsert selected parent (fiberComponent observed)) global)
rawComponentBirthInvariant name key world error value nameEq keyEq global
  NoTransitions AlignedEnd embedding previous = previous
rawComponentBirthInvariant name key world error value nameEq keyEq global
  (MoreTransitions head rest) aligned embedding previous =
    case aligned of
      AlignedStep action tag checked _ alignedRest =>
        rawComponentBirthInvariant name key world error value nameEq keyEq global rest alignedRest
          (\wanted, occurrence => embedding wanted (case occurrence of
            MkLocatedActionOccurrence before afterState prior step later actionExact decomposition =>
              MkLocatedActionOccurrence before afterState (MoreTransitions (Fired nameEq keyEq action tag checked) prior) step later
                actionExact (cong (MoreTransitions (Fired nameEq keyEq action tag checked)) decomposition)))
          (rawComponentBirthStep name key world error value nameEq keyEq global action _ _ tag
            (checkedActionProjects nameEq keyEq action _ _ tag checked)
            (embedding action (MkLocatedActionOccurrence _ _ NoTransitions (Fired nameEq keyEq action tag checked) rest Refl Refl)) previous)


||| A present fiber at ANY reached prefix has a birth of its exact component
||| in the actual global trace. This uses only emptiness and checked alignment.
public export
0 rawComponentBirthAtPrefix :
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
  (parent : Parent name ** LocatedActionOccurrence
    (OInsert selected parent (fiberComponent observed)) global)
rawComponentBirthAtPrefix name key world error value nameEq keyEq {initial}
  global prior later decomposition aligned empty =
    rawComponentBirthInvariant name key world error value nameEq keyEq global prior aligned
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


||| Immutable cross-time coherence: the same raw name at ANY two reached cuts
||| has the SAME component, even across inactivity, removal and other actors.
||| Freshness identifies two authenticated births, never two arbitrary states.
public export
0 uniqueRawComponentsAcrossPrefixes :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftState, rightState, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq global ->
  (leftPrior : Transitions initial leftState) -> (leftLater : Transitions leftState finalState) ->
  appendTransitions leftPrior leftLater = global ->
  (rightPrior : Transitions initial rightState) -> (rightLater : Transitions rightState finalState) ->
  appendTransitions rightPrior rightLater = global ->
  (selected : name) -> (leftFiber, rightFiber : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftState) = Just leftFiber ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry rightState) = Just rightFiber ->
  fiberComponent leftFiber = fiberComponent rightFiber
uniqueRawComponentsAcrossPrefixes name key world error value nameEq keyEq global aligned empty unique
  leftPrior leftLater leftSplit rightPrior rightLater rightSplit selected leftFiber rightFiber leftFound rightFound =
    case rawComponentBirthAtPrefix name key world error value nameEq keyEq global leftPrior leftLater leftSplit
      (fst (alignedAppendSplit leftPrior leftLater
        (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym leftSplit) aligned)))
      empty selected leftFiber leftFound of
      (leftParent ** leftBirth) =>
        case rawComponentBirthAtPrefix name key world error value nameEq keyEq global rightPrior rightLater rightSplit
          (fst (alignedAppendSplit rightPrior rightLater
            (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym rightSplit) aligned)))
          empty selected rightFiber rightFound of
          (rightParent ** rightBirth) =>
            uniqueRawBirthComponents name key world error value nameEq keyEq global unique selected
              leftParent rightParent (fiberComponent leftFiber) (fiberComponent rightFiber) leftBirth rightBirth
