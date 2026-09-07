module DGamma.CP5RetirementHistorySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Needed to exclude closing classifications for supported endpoint births.
||| This is same-trace operational monotonicity, not cross-trace A9 agreement.
export
0 retirementUpdateFalseBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (old, updated : Fiber name key value world error) ->
  RetirementUpdate old updated -> (retired updated = False) -> (retired old = False)
retirementUpdateFalseBackward name key world error value old updated (RetirementStable same) finalFalse =
  trans (sym same) finalFalse
retirementUpdateFalseBackward name key world error value old updated (RetirementApplied finalTrue) finalFalse =
  case trans (sym finalTrue) finalFalse of Refl impossible

||| Nonretired target fibers inherit any source property, except at a genuine
||| fresh insertion. Actual local updates—not a flag equality assumption—own it.
export
0 rawUnretiredPropertyUpdate :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (property : name -> Type) -> (actor : name) -> (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  ((lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} actor source = Nothing) -> property actor) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected source = Just fiber) -> (retired fiber = False) -> property selected) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected target = Just observed) -> (retired observed = False) -> property selected
rawUnretiredPropertyUpdate name key world error value nameEq property actor source _
  (LocalInsert next absent) inserted previous selected observed found finalFalse =
    case decEq @{nameEq} selected actor of
      Yes same => case same of Refl => inserted absent
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source (LocalInsert next absent))) found) finalFalse
rawUnretiredPropertyUpdate name key world error value nameEq property actor source _
  (LocalReplace {oldFiber} {oldFound} {retirementUpdate} next) inserted previous selected observed found finalFalse =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => previous actor oldFiber oldFound
          (retirementUpdateFalseBackward name key world error value oldFiber next retirementUpdate
            (trans (cong retired (justInjective (trans (sym (lookupReplacedFiber actor oldFiber next source oldFound)) found))) finalFalse))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source (LocalReplace {oldFiber} {oldFound} {retirementUpdate} next))) found) finalFalse
rawUnretiredPropertyUpdate name key world error value nameEq property actor source _
  LocalDelete inserted previous selected observed found finalFalse =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => void (nothingIsNotJust (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source)) found))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source LocalDelete)) found) finalFalse

export
0 rawUnretiredPropertyStep :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (property : name -> Type) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  ((parent : Parent name) -> (component : Component key value world error) ->
    (action = OInsert (actionOwner action) parent component) -> property (actionOwner action)) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry before) = Just fiber) -> (retired fiber = False) -> property selected) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry afterState) = Just observed) -> (retired observed = False) -> property selected
rawUnretiredPropertyStep name key world error value nameEq keyEq property action before afterState tag raw inserted previous =
  rawUnretiredPropertyUpdate name key world error value nameEq property (actionOwner action)
    (registry before) (registry afterState) (systemRegistryUpdate (applyActionLocalUpdate nameEq keyEq action before afterState tag raw))
    (\absent => case rawAbsentOwnerInsertion name key world error value nameEq keyEq action before afterState tag raw absent of
      (parent ** component ** exact) => inserted parent component exact) previous

||| Forward induction permits arbitrary property targets while authenticating
||| each possible reset as an actual insertion in the supplied global segment.
export
0 rawUnretiredPropertyTrace :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (property : name -> Type) ->
  {initial, finalState, first, last : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (segment : Transitions first last) ->
  AlignedTransitions name key world error value nameEq keyEq segment ->
  ((action : Action name key value world error) -> LocatedActionOccurrence action segment -> LocatedActionOccurrence action global) ->
  ((selected : name) -> (parent : Parent name) -> (component : Component key value world error) ->
    LocatedActionOccurrence (OInsert selected parent component) global -> property selected) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry first) = Just fiber) -> (retired fiber = False) -> property selected) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry last) = Just observed) -> (retired observed = False) -> property selected
rawUnretiredPropertyTrace name key world error value nameEq keyEq property global NoTransitions AlignedEnd embedding inserted previous = previous
rawUnretiredPropertyTrace name key world error value nameEq keyEq property global
  (MoreTransitions head rest) aligned embedding inserted previous =
    case aligned of
      AlignedStep action tag checked _ alignedRest =>
        rawUnretiredPropertyTrace name key world error value nameEq keyEq property global rest alignedRest
          (\wanted, occurrence => embedding wanted
            (currentBirthPrependLocation name key world error value (Fired nameEq keyEq action tag checked) rest wanted occurrence)) inserted
          (rawUnretiredPropertyStep name key world error value nameEq keyEq property action _ _ tag
            (checkedActionProjects nameEq keyEq action _ _ tag checked)
            (\parent, component, exact => inserted (actionOwner action) parent component
              (replace {p = \wanted => LocatedActionOccurrence wanted global} exact
                (embedding action (MkLocatedActionOccurrence _ _ NoTransitions (Fired nameEq keyEq action tag checked) rest Refl Refl)))) previous)

0 retiredLookupCannotBeUnretired :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (selected : name) -> (state : SystemState name key value world error) ->
  (retiredFiber, otherFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry state) = Just retiredFiber) -> (retired retiredFiber = True) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry state) = Just otherFiber) -> (retired otherFiber = False) -> Void
retiredLookupCannotBeUnretired name key world error value nameEq selected state retiredFiber otherFiber found retiredTrue otherFound otherFalse =
  case trans (sym retiredTrue) (trans (cong retired (justInjective (trans (sym found) otherFound))) otherFalse) of Refl impossible

||| Resurrection of a retired name requires an ACTUAL later insertion.
||| No uniqueness is assumed here, so legal remove/reinsert traces are allowed.
export
0 unretiredAfterRetiredHasBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  (selected : name) -> (retiredFiber, finalFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry first) = Just retiredFiber) -> (retired retiredFiber = True) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just finalFiber) -> (retired finalFiber = False) ->
  (parent : Parent name ** component : Component key value world error **
    LocatedActionOccurrence (OInsert selected parent component) trace)
unretiredAfterRetiredHasBirth name key world error value nameEq keyEq {first} trace aligned selected
  retiredFiber finalFiber retiredFound retiredTrue finalFound finalFalse =
    rawUnretiredPropertyTrace name key world error value nameEq keyEq
      (\wanted => (wanted = selected) -> (parent : Parent name ** component : Component key value world error **
        LocatedActionOccurrence (OInsert wanted parent component) trace)) trace trace aligned
      (\action, occurrence => occurrence)
      (\wanted, parent, component, birth, same => (parent ** component ** birth))
      (\wanted, fiber, found, unretired, same => void
        (retiredLookupCannotBeUnretired name key world error value nameEq selected first retiredFiber fiber retiredFound retiredTrue
          (replace {p = \actor => (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
            @{nameEq} actor (registry first) = Just fiber)} same found) unretired))
      selected finalFiber finalFound finalFalse Refl

export
0 observedActionPositionBound :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (position : Nat) -> (action : Action name key value world error) ->
  (rawClosingActionAt name key world error value position trace = Just action) -> LT position (transitionCount trace)
observedActionPositionBound name key world error value NoTransitions position action observed = case observed of Refl impossible
observedActionPositionBound name key world error value (MoreTransitions step rest) Z action observed = LTESucc LTEZero
observedActionPositionBound name key world error value (MoreTransitions step rest) (S position) action observed =
  LTESucc (observedActionPositionBound name key world error value rest position action observed)

export
0 beforeCutOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle finalState) ->
  (action : Action name key value world error) -> LocatedActionOccurrence action prior ->
  LocatedActionOccurrence action (appendTransitions prior later)
beforeCutOccurrence name key world error value prior later action
  (MkLocatedActionOccurrence before afterState earlier step remaining exact decomposition) =
    MkLocatedActionOccurrence before afterState earlier step (appendTransitions remaining later) exact
      (trans (sym (appendTransitionsAssociative earlier (MoreTransitions step remaining) later))
        (cong (\whole => appendTransitions whole later) decomposition))

export
0 beforeCutOccurrenceOrdinal :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle finalState) ->
  (action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action prior) ->
  (locatedActionOrdinal (beforeCutOccurrence name key world error value prior later action occurrence) = locatedActionOrdinal occurrence)
beforeCutOccurrenceOrdinal name key world error value prior later action
  (MkLocatedActionOccurrence before afterState earlier step remaining exact decomposition) = Refl

export
0 afterCutOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle finalState) ->
  (action : Action name key value world error) -> LocatedActionOccurrence action later ->
  LocatedActionOccurrence action (appendTransitions prior later)
afterCutOccurrence name key world error value NoTransitions later action occurrence = occurrence
afterCutOccurrence name key world error value (MoreTransitions step rest) later action occurrence =
  currentBirthPrependLocation name key world error value step (appendTransitions rest later) action
    (afterCutOccurrence name key world error value rest later action occurrence)

export
0 afterCutOccurrenceBound :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle finalState) ->
  (action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action later) ->
  LTE (transitionCount prior) (locatedActionOrdinal (afterCutOccurrence name key world error value prior later action occurrence))
afterCutOccurrenceBound name key world error value NoTransitions later action occurrence = LTEZero
afterCutOccurrenceBound name key world error value (MoreTransitions step rest) later action occurrence =
  replace {p = LTE (S (transitionCount rest))}
    (sym (currentBirthPrependOrdinal name key world error value step (appendTransitions rest later) action
      (afterCutOccurrence name key world error value rest later action occurrence)))
    (LTESucc (afterCutOccurrenceBound name key world error value rest later action occurrence))

||| Strong original uniqueness excludes two births on opposite sides of an
||| authentic cut. This compares ordinals; no dependent endpoint casts occur.
export
0 uniqueBirthsAcrossCutImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq (appendTransitions prior later) ->
  (selected : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (leftBirth : LocatedActionOccurrence (OInsert selected leftParent leftComponent) prior) ->
  (rightBirth : LocatedActionOccurrence (OInsert selected rightParent rightComponent) later) -> Void
uniqueBirthsAcrossCutImpossible name key world error value nameEq keyEq prior later unique
  selected leftParent rightParent leftComponent rightComponent leftBirth rightBirth =
    LTImpliesNotGTE
      (observedActionPositionBound name key world error value prior (locatedActionOrdinal leftBirth)
        (OInsert selected leftParent leftComponent)
        (rawClosingActionAtLocated name key world error value prior (OInsert selected leftParent leftComponent) leftBirth))
      (replace {p = LTE (transitionCount prior)}
        (trans (sym (uniqueInsertionPosition unique selected leftParent rightParent leftComponent rightComponent
          (beforeCutOccurrence name key world error value prior later (OInsert selected leftParent leftComponent) leftBirth)
          (afterCutOccurrence name key world error value prior later (OInsert selected rightParent rightComponent) rightBirth)))
          (beforeCutOccurrenceOrdinal name key world error value prior later (OInsert selected leftParent leftComponent) leftBirth))
        (afterCutOccurrenceBound name key world error value prior later (OInsert selected rightParent rightComponent) rightBirth))

||| A retired fiber at an authentic prefix cannot be nonretired at the final
||| endpoint under whole-original uniqueness. Its earlier birth is DERIVED.
export
0 retiredCutNonretiredEndpointImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (later : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq prior ->
  AlignedTransitions name key world error value nameEq keyEq later -> (bindings (registry first) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq (appendTransitions prior later) ->
  (selected : name) -> (retiredFiber, finalFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry middle) = Just retiredFiber) -> (retired retiredFiber = True) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just finalFiber) -> (retired finalFiber = False) -> Void
retiredCutNonretiredEndpointImpossible name key world error value nameEq keyEq prior later priorAligned laterAligned empty unique
  selected retiredFiber finalFiber retiredFound retiredTrue finalFound finalFalse =
    case unretiredAfterRetiredHasBirth name key world error value nameEq keyEq later laterAligned selected
      retiredFiber finalFiber retiredFound retiredTrue finalFound finalFalse of
      (parent ** component ** laterBirth) =>
        uniqueBirthsAcrossCutImpossible name key world error value nameEq keyEq prior later unique selected
          (fiberParent retiredFiber) parent (fiberComponent retiredFiber) component
          (rawMetadataBirthAtPrefix name key world error value nameEq keyEq prior prior NoTransitions
            (currentBirthTraceAppendEmpty name key world error value prior) priorAligned empty selected retiredFiber retiredFound) laterBirth

0 retirementAppliedTrue :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (fiber : Fiber name key value world error) -> (retired (retireFiber fiber) = True)
retirementAppliedTrue name key world error value (MkFiber component parent retiredFlag table lifecycle) = Refl

0 rawRetireTargetObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry before) = observed) ->
  (applyAction @{nameEq} @{keyEq} (ORetire selected) before = Just (tag, afterState)) ->
  (fiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry afterState) = Just fiber, retired fiber = True))
rawRetireTargetObserved name key world error value nameEq keyEq selected before afterState tag Nothing sourceExact raw =
  void (nothingIsNotJust (trans (sym (the (applyAction @{nameEq} @{keyEq} (ORetire selected) before = Nothing)
    (rewrite sourceExact in Refl))) raw))
rawRetireTargetObserved name key world error value nameEq keyEq selected before afterState tag (Just sourceFiber) sourceExact raw =
  replace {p = \target => (fiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry target) = Just fiber, retired fiber = True))}
    (cong snd (justInjective (trans (sym (the
      (applyAction @{nameEq} @{keyEq} (ORetire selected) before =
        Just (ORetireTag, MkSystemState (worldState before) (replaceBinding @{nameEq} selected (retireFiber sourceFiber) (registry before))))
      (rewrite sourceExact in Refl))) raw)))
    (retireFiber sourceFiber ** (lookupReplacedFiber @{nameEq} selected sourceFiber (retireFiber sourceFiber) (registry before) sourceExact,
      retirementAppliedTrue name key world error value sourceFiber))

export
0 rawRetireTarget :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (applyAction @{nameEq} @{keyEq} (ORetire selected) before = Just (tag, afterState)) ->
  (fiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry afterState) = Just fiber, retired fiber = True))
rawRetireTarget name key world error value nameEq keyEq selected before afterState tag raw =
  rawRetireTargetObserved name key world error value nameEq keyEq selected before afterState tag
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry before)) Refl raw

export
0 retirementAlignedHeadRaw :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest) ->
  (applyAction @{nameEq} @{keyEq} (transitionAction step) first = Just (transitionTag step, middle))
retirementAlignedHeadRaw name key world error value nameEq keyEq _ _
  (AlignedStep action tag checked rest alignedRest) = checkedActionProjects nameEq keyEq action _ _ tag checked

export
0 retirementAlignedLocatedRaw :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  (action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action trace) ->
  (applyAction @{nameEq} @{keyEq} action (actionBeforeState occurrence) =
    Just (transitionTag (locatedTransition occurrence), actionAfterState occurrence))
retirementAlignedLocatedRaw name key world error value nameEq keyEq trace aligned action occurrence =
  replace {p = \wanted => (applyAction @{nameEq} @{keyEq} wanted (actionBeforeState occurrence) =
    Just (transitionTag (locatedTransition occurrence), actionAfterState occurrence))} (locatedAction occurrence)
    (retirementAlignedHeadRaw name key world error value nameEq keyEq (locatedTransition occurrence) (afterActionOccurrence occurrence)
      (snd (alignedAppendSplit (beforeActionOccurrence occurrence) (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence))
        (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (actionOccurrenceDecomposition occurrence)) aligned))))

0 retirementCutCannotEndUnretired :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, before, afterState, finalState : SystemState name key value world error} ->
  (prior : Transitions first before) -> (step : Transition before afterState) -> (later : Transitions afterState finalState) ->
  AlignedTransitions name key world error value nameEq keyEq (appendTransitions prior (MoreTransitions step later)) ->
  (bindings (registry first) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq (appendTransitions prior (MoreTransitions step later)) ->
  (selected : name) -> (transitionAction step = ORetire selected) -> (finalFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just finalFiber) -> (retired finalFiber = False) -> Void
retirementCutCannotEndUnretired name key world error value nameEq keyEq {before} {afterState} prior step later aligned empty unique selected exact
  finalFiber finalFound finalFalse =
    case rawRetireTarget name key world error value nameEq keyEq selected before afterState (transitionTag step)
      (replace {p = \action => (applyAction @{nameEq} @{keyEq} action before = Just (transitionTag step, afterState))} exact
        (retirementAlignedHeadRaw name key world error value nameEq keyEq step later
          (snd (alignedAppendSplit prior (MoreTransitions step later) aligned)))) of
      (retiredFiber ** (retiredFound, retiredTrue)) =>
        retiredCutNonretiredEndpointImpossible name key world error value nameEq keyEq
          (appendTransitions prior (MoreTransitions step NoTransitions)) later
          (fst (alignedAppendSplit (appendTransitions prior (MoreTransitions step NoTransitions)) later
            (replace {p = AlignedTransitions name key world error value nameEq keyEq}
              (sym (appendTransitionsAssociative prior (MoreTransitions step NoTransitions) later)) aligned)))
          (snd (alignedAppendSplit (appendTransitions prior (MoreTransitions step NoTransitions)) later
            (replace {p = AlignedTransitions name key world error value nameEq keyEq}
              (sym (appendTransitionsAssociative prior (MoreTransitions step NoTransitions) later)) aligned))) empty
          (replace {p = UniqueRawNameInsertions name key world error value nameEq keyEq}
            (sym (appendTransitionsAssociative prior (MoreTransitions step NoTransitions) later)) unique)
          selected retiredFiber finalFiber retiredFound retiredTrue finalFound finalFalse

||| Every historical retirement of this raw name is excluded by a nonretired
||| endpoint under strong original uniqueness; legal reuse is NOT asserted away.
export
0 nonretiredEndpointRejectsRetirement :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  (bindings (registry first) = []) -> UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected : name) -> (finalFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just finalFiber) -> (retired finalFiber = False) ->
  LocatedActionOccurrence (ORetire selected) trace -> Void
nonretiredEndpointRejectsRetirement name key world error value nameEq keyEq trace aligned empty unique selected finalFiber finalFound finalFalse
  (MkLocatedActionOccurrence before afterState prior step later exact decomposition) =
    retirementCutCannotEndUnretired name key world error value nameEq keyEq prior step later
      (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym decomposition) aligned) empty
      (replace {p = UniqueRawNameInsertions name key world error value nameEq keyEq} (sym decomposition) unique)
      selected exact finalFiber finalFound finalFalse
