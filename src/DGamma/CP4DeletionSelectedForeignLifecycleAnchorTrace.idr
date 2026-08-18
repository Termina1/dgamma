module DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorCore
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 nothingNotJustAnchorTrace : Nothing = Just item -> Void
nothingNotJustAnchorTrace Refl impossible

0 lookupNothingFromNotElemAnchorTrace :
  (nameEq : DecEq name) -> (wanted : name) ->
  (entries : List (Binding name item)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries @{nameEq} wanted entries = Nothing
lookupNothingFromNotElemAnchorTrace nameEq wanted entries absent
  with (lookupEntries @{nameEq} wanted entries) proof found
  lookupNothingFromNotElemAnchorTrace nameEq wanted entries absent | Nothing =
    Refl
  lookupNothingFromNotElemAnchorTrace nameEq wanted entries absent |
    Just observed = void (absent
      (lookupJustElem @{nameEq} wanted entries observed found))

0 lookupDeleteSelfAnchorTrace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed : name) ->
  (registry : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed
    (deleteBinding @{nameEq} removed registry) =
      the (Maybe (Fiber name key value world error)) Nothing
lookupDeleteSelfAnchorTrace nameEq removed
  (MkCoeffectContext entries unique) =
    lookupNothingFromNotElemAnchorTrace nameEq removed
      (deleteEntries @{nameEq} removed entries)
      (deletedKeyNotElem removed entries unique)

||| Turn the positional trace witness used by Theorem 61 into the located
||| prefix/head/suffix form used by the deletion and ordering proofs.
public export
0 occursInGivesLocatedAction :
  (transition : Transition stepBefore stepAfter) ->
  (global : Transitions initial finalState) ->
  OccursIn transition global ->
  LocatedActionOccurrence (transitionAction transition) global
occursInGivesLocatedAction transition
  (MoreTransitions transition rest) OccursHere =
    MkLocatedActionOccurrence stepBefore stepAfter NoTransitions transition rest
      Refl Refl
occursInGivesLocatedAction transition
  (MoreTransitions head rest) (OccursLater later) =
    case occursInGivesLocatedAction transition rest later of
      MkLocatedActionOccurrence before after earlier locatedStep laterTrace sameAction
        decomposition =>
          MkLocatedActionOccurrence before after
            (MoreTransitions head earlier) locatedStep laterTrace sameAction
            (cong (MoreTransitions head) decomposition)

||| Exact component preservation for a checked step whose named fiber is
||| present on both sides.  O-Insert/O-Remove owner cases are contradictory;
||| every replacement carries the evaluator's static-component certificate.
public export
0 checkedStepPreservesPresentComponent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  (beforeFiber, afterFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry before) = Just beforeFiber ->
  lookupFiber @{nameEq} selected (registry afterState) = Just afterFiber ->
  fiberComponent afterFiber = fiberComponent beforeFiber
checkedStepPreservesPresentComponent nameEq keyEq selected action tag before
  afterState checked beforeFiber afterFiber beforeFound afterFound
  with (decEq @{nameEq} selected (actionOwner action))
  checkedStepPreservesPresentComponent nameEq keyEq selected action tag before
    afterState checked beforeFiber afterFiber beforeFound afterFound |
    No distinct =
      let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
            checked
          0 update = applyActionLocalUpdate nameEq keyEq action before afterState
            tag raw
          0 lookupSame = systemLocalUpdateForeign nameEq selected
            (actionOwner action) distinct before afterState update
          0 sameFiber : (afterFiber = beforeFiber)
          sameFiber = justInjective
            (trans (sym afterFound) (trans lookupSame beforeFound))
      in cong fiberComponent sameFiber
  checkedStepPreservesPresentComponent nameEq keyEq selected action tag
    before@(MkSystemState beforeWorld beforeRegistry)
    afterState@(MkSystemState afterWorld afterRegistry) checked beforeFiber
    afterFiber beforeFound afterFound | Yes sameOwner =
      let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
            checked
          0 update = applyActionLocalUpdate nameEq keyEq action before afterState
            tag raw
      in case sameOwner of
        Refl => case systemRegistryUpdate update of
          LocalInsert inserted absent =>
            void (nothingNotJustAnchorTrace (trans (sym absent) beforeFound))
          LocalReplace next {oldFiber} {oldFound} {staticComponent} =>
            let 0 oldSame : (oldFiber = beforeFiber)
                oldSame = justInjective (trans (sym oldFound) beforeFound)
                0 nextFound : (lookupFiber @{nameEq} (actionOwner action)
                  (replaceBinding @{nameEq} (actionOwner action) next
                    beforeRegistry) = Just next)
                nextFound = lookupReplacedFiber (actionOwner action) oldFiber
                  next beforeRegistry oldFound
                0 nextSame : (next = afterFiber)
                nextSame = justInjective (trans (sym nextFound) afterFound)
            in trans (cong fiberComponent (sym nextSame))
              (trans staticComponent (cong fiberComponent oldSame))
          LocalDelete =>
            void (nothingNotJustAnchorTrace
              (trans (sym (lookupDeleteSelfAnchorTrace nameEq
                (actionOwner action) beforeRegistry)) afterFound))

0 installedFiberAtAnchorTrace :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{nameEq} selected state = True ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} selected (registry state) = Just fiber)
installedFiberAtAnchorTrace nameEq selected state installed
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  installedFiberAtAnchorTrace nameEq selected state installed | Nothing =
    void (case installed of Refl impossible)
  installedFiberAtAnchorTrace nameEq selected state installed | Just fiber =
    (fiber ** Refl)

||| Component stability across an installed trace segment.  This is the exact
||| transport needed to relate a retained occurrence's current owner to the
||| fiber at its L-Begin boundary without assuming fiber/proof equality.
public export
0 installedTracePreservesComponent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected trace ->
  (firstFiber, finalFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry first) = Just firstFiber ->
  lookupFiber @{nameEq} selected (registry finalState) = Just finalFiber ->
  fiberComponent finalFiber = fiberComponent firstFiber
installedTracePreservesComponent nameEq keyEq selected NoTransitions
  (InstalledEnd installed) firstFiber finalFiber firstFound finalFound =
    cong fiberComponent (justInjective (trans (sym finalFound) firstFound))
installedTracePreservesComponent nameEq keyEq selected
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  firstFiber finalFiber firstFound finalFound =
    case installedFiberAtAnchorTrace nameEq selected _
      (installedTraceStart tailInstalled) of
      (middleFiber ** middleFound) =>
        let 0 firstStep = checkedStepPreservesPresentComponent nameEq keyEq
              selected action tag _ _ checked firstFiber middleFiber firstFound
              middleFound
            0 tail = installedTracePreservesComponent nameEq keyEq selected rest
              tailInstalled middleFiber finalFiber middleFound finalFound
        in trans tail firstStep

||| Split installed evidence at one exact transition occurrence.  The prefix
||| ends at the selected step's source and the suffix starts at its target.
public export
record InstalledOccurrenceSplit
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, finalState, stepBefore, stepAfter :
    SystemState name key value world error}
  (transition : Transition stepBefore stepAfter)
  (trace : Transitions first finalState) where
  constructor MkInstalledOccurrenceSplit
  installedOccurrencePrefix : Transitions first stepBefore
  installedOccurrenceSuffix : Transitions stepAfter finalState
  0 installedPrefixEvidence : InstalledTrace name key world error value nameEq
    keyEq selected installedOccurrencePrefix
  0 installedSuffixEvidence : InstalledTrace name key world error value nameEq
    keyEq selected installedOccurrenceSuffix
  0 installedOccurrenceSource : installedAt @{nameEq} selected stepBefore = True
  0 installedOccurrenceTarget : installedAt @{nameEq} selected stepAfter = True
  0 installedOccurrenceDecomposition :
    appendTransitions installedOccurrencePrefix
      (MoreTransitions transition installedOccurrenceSuffix) = trace

public export
0 splitInstalledAtOccurrence :
  (transition : Transition stepBefore stepAfter) ->
  (trace : Transitions first finalState) ->
  (installed : InstalledTrace name key world error value nameEq keyEq selected
    trace) ->
  OccursIn transition trace ->
  InstalledOccurrenceSplit name key world error value nameEq keyEq selected
    transition trace
splitInstalledAtOccurrence
  (Fired nameEq keyEq action tag checked)
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  OccursHere = MkInstalledOccurrenceSplit NoTransitions rest
    (InstalledEnd sourceInstalled) tailInstalled sourceInstalled
    (installedTraceStart tailInstalled) Refl
splitInstalledAtOccurrence transition
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  (OccursLater later) =
    case splitInstalledAtOccurrence transition rest tailInstalled later of
      MkInstalledOccurrenceSplit earlier laterTrace earlierInstalled laterInstalled
        occurrenceSource occurrenceTarget decomposition =>
          MkInstalledOccurrenceSplit
            (MoreTransitions (Fired nameEq keyEq action tag checked) earlier)
            laterTrace
            (InstalledStep action tag checked earlier sourceInstalled
              earlierInstalled)
            laterInstalled occurrenceSource occurrenceTarget
            (cong (MoreTransitions
              (Fired nameEq keyEq action tag checked)) decomposition)

||| Complete the closed-consumer anchor once the occurrence locator has exposed
||| the actor-opening-to-current installed segment.  Both component equations
||| are derived by the checked trace induction above.
public export
0 closedForeignLifecycleAnchorFromInstalledPrefix :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (global : Transitions initial finalState) ->
  (selected, actor : name) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    actor global) ->
  (current : SystemState name key value world error) ->
  (openingToCurrent : Transitions
    (closedStartState (locatedEpisode consumerEpisode)) current) ->
  InstalledTrace name key world error value nameEq keyEq selected
    openingToCurrent ->
  InstalledTrace name key world error value nameEq keyEq actor
    openingToCurrent ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry current) = Just currentSelected ->
  lookupFiber @{nameEq} actor (registry current) = Just currentOwner ->
  ForeignLifecyclePrecedenceAnchor name key world error value nameEq keyEq
    global selected actor currentSelected currentOwner
closedForeignLifecycleAnchorFromInstalledPrefix nameEq keyEq global selected actor
  consumerEpisode current openingToCurrent selectedInstalled actorInstalled
  currentSelected currentOwner currentSelectedFound currentOwnerFound =
    case installedFiberAtAnchorTrace nameEq selected
      (closedStartState (locatedEpisode consumerEpisode))
      (installedTraceStart selectedInstalled) of
      (openingSelected ** openingSelectedFound) =>
        case installedFiberAtAnchorTrace nameEq actor
          (closedStartState (locatedEpisode consumerEpisode))
          (installedTraceStart actorInstalled) of
          (openingOwner ** openingOwnerFound) =>
            ClosedForeignLifecyclePrecedenceAnchor consumerEpisode
              openingSelected openingOwner openingSelectedFound openingOwnerFound
              (sym (installedTracePreservesComponent nameEq keyEq selected
                openingToCurrent selectedInstalled openingSelected currentSelected
                openingSelectedFound currentSelectedFound))
              (sym (installedTracePreservesComponent nameEq keyEq actor
                openingToCurrent actorInstalled openingOwner currentOwner
                openingOwnerFound currentOwnerFound))
