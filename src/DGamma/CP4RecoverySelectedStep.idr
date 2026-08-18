module DGamma.CP4RecoverySelectedStep

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryTrace
import DGamma.CP4RecoverySelectedRetire
import DGamma.CP4RecoverySelectedDivert
import DGamma.CP4RecoverySelectedLeave
import DGamma.CP4RecoverySelectedAdvance
import Decidable.Equality

%default total

0 justPairInjective : Just left = Just right -> left = right
justPairInjective Refl = Refl

0 falseNotTrue : False = True -> Void
falseNotTrue Refl impossible

public export
0 accumulatorModelInstalledAt :
  (model : AccumulatorModel name key world error value nameEq keyEq selected
    whole state) ->
  installedAt @{nameEq} selected state = True
accumulatorModelInstalledAt model = rewrite modelFound model in
  case modelInstalled model of
    AccumulatorReloading remaining view life => rewrite life in Refl
    AccumulatorActive view life => rewrite life in Refl
    AccumulatorUnloading view outcome life => rewrite life in Refl

0 successfulRetireTag :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  tag = ORetireTag
successfulRetireTag nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} selected fibers)
  successfulRetireTag nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  successfulRetireTag nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Just fiber = sym (cong fst (justPairInjective raw))

0 successfulLeaveTag :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (tag, afterState) ->
  tag = LLeaveTag
successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} selected fibers)
  successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Just fiber with (fiberLifecycle fiber)
    successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Inactive outcome =
        void (nothingIsNotJust raw)
    successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Reloading remaining accumulator view =
        void (nothingIsNotJust raw)
    successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust raw)
    successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Active accumulator view | True =
          void (nothingIsNotJust raw)
      successfulLeaveTag nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Active accumulator view | False =
          sym (cong fst (justPairInjective raw))

0 insertCannotExisting :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry before) = Just fiber -> Void
insertCannotExisting {name} {key} {world} {error} {value}
  nameEq keyEq selected parent component (MkSystemState ambient fibers) afterState
  tag raw fiber existing
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  insertCannotExisting nameEq keyEq selected parent component
    (MkSystemState ambient fibers) afterState tag raw fiber existing | False =
      void (nothingIsNotJust raw)
  insertCannotExisting nameEq keyEq selected parent component
    (MkSystemState ambient fibers) afterState tag raw fiber existing | True
    with (setFresh @{nameEq} selected (freshFiber component parent) fibers)
      proof fresh
    insertCannotExisting nameEq keyEq selected parent component
      (MkSystemState ambient fibers) afterState tag raw fiber existing | True |
      Nothing = void (nothingIsNotJust raw)
    insertCannotExisting nameEq keyEq selected parent component
      (MkSystemState ambient fibers) afterState tag raw fiber existing | True |
      Just applied =
        let 0 absent : (lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} selected fibers =
              Nothing)
            absent = setFreshAbsent nameEq selected (freshFiber component parent)
              fibers applied fresh
        in void (nothingIsNotJust (trans (sym absent) existing))

0 removeCannotInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORemove selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected before = True -> Void
removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw installedSource
  with (lookupFiber @{nameEq} selected fibers)
  removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw installedSource | Nothing = void (nothingIsNotJust raw)
  removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw installedSource | Just fiber with (fiberLifecycle fiber)
    removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber | Inactive outcome =
        void (falseNotTrue installedSource)
    removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber |
      Reloading remaining accumulator view with (retired fiber)
      removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw installedSource | Just fiber |
        Reloading remaining accumulator view | False =
          void (nothingIsNotJust raw)
      removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw installedSource | Just fiber |
        Reloading remaining accumulator view | True =
          void (nothingIsNotJust raw)
    removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber |
      Active accumulator view with (retired fiber)
      removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw installedSource | Just fiber |
        Active accumulator view | False = void (nothingIsNotJust raw)
      removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw installedSource | Just fiber |
        Active accumulator view | True = void (nothingIsNotJust raw)
    removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber |
      Unloading accumulator view outcome with (retired fiber)
      removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw installedSource | Just fiber |
        Unloading accumulator view outcome | False = void (nothingIsNotJust raw)
      removeCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw installedSource | Just fiber |
        Unloading accumulator view outcome | True = void (nothingIsNotJust raw)

0 beginCannotInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected before = True -> Void
beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw installedSource
  with (lookupFiber @{nameEq} selected fibers)
  beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw installedSource | Nothing = void (nothingIsNotJust raw)
  beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw installedSource | Just fiber with (fiberLifecycle fiber)
    beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber | Inactive Nothing =
        void (falseNotTrue installedSource)
    beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber | Inactive (Just err) =
        void (nothingIsNotJust raw)
    beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust raw)
    beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber |
      Active accumulator view = void (nothingIsNotJust raw)
    beginCannotInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedSource | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust raw)

0 unloadCannotEndInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected afterState = True -> Void
unloadCannotEndInstalled {name} {key} {world} {error} {value}
  nameEq keyEq selected (MkSystemState ambient fibers) afterState tag raw
  installedTarget with (lookupFiber @{nameEq} selected fibers) proof found
  unloadCannotEndInstalled nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw installedTarget | Nothing = void (nothingIsNotJust raw)
  unloadCannotEndInstalled nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw installedTarget |
    Just (MkFiber component parent retiredFlag table lifecycle)
    with (lifecycle)
    unloadCannotEndInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedTarget |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Inactive outcome = void (nothingIsNotJust raw)
    unloadCannotEndInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedTarget |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Reloading remaining accumulator view = void (nothingIsNotJust raw)
    unloadCannotEndInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedTarget |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Active accumulator view = void (nothingIsNotJust raw)
    unloadCannotEndInstalled nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw installedTarget |
      Just (MkFiber component parent retiredFlag table lifecycle) |
      Unloading accumulator view outcome
      with (relied @{nameEq} selected fibers)
      unloadCannotEndInstalled nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag raw installedTarget |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Unloading accumulator view outcome | True = void (nothingIsNotJust raw)
      unloadCannotEndInstalled nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag raw installedTarget |
        Just (MkFiber component parent retiredFlag table lifecycle) |
        Unloading accumulator view outcome | False =
          let concrete : SystemState name key value world error
              concrete = MkSystemState
                (localWorld (accumulator
                  (MkLocalState ambient
                    (restrictOwnedPreservingOrder (componentProvisions component)
                      (ownedValues table)))))
                (replaceBinding @{nameEq} selected
                  (setFiberRuntime
                    (MkFiber component parent retiredFlag table
                      (Unloading accumulator view outcome))
                    (localTable (accumulator
                      (MkLocalState ambient
                        (restrictOwnedPreservingOrder
                          (componentProvisions component) (ownedValues table)))))
                    (Inactive outcome)) fibers)
              0 concreteIsAfter : concrete = afterState
              concreteIsAfter = cong snd (justPairInjective raw)
              0 targetFound : lookupFiber @{nameEq} selected
                (registry concrete) =
                Just (setFiberRuntime
                  (MkFiber component parent retiredFlag table
                    (Unloading accumulator view outcome))
                  (localTable (accumulator
                    (MkLocalState ambient
                      (restrictOwnedPreservingOrder
                        (componentProvisions component) (ownedValues table)))))
                  (Inactive outcome))
              targetFound = lookupReplacedFiber selected
                (MkFiber component parent retiredFlag table
                  (Unloading accumulator view outcome))
                (setFiberRuntime
                  (MkFiber component parent retiredFlag table
                    (Unloading accumulator view outcome))
                  (localTable (accumulator
                    (MkLocalState ambient
                      (restrictOwnedPreservingOrder
                        (componentProvisions component) (ownedValues table)))))
                  (Inactive outcome)) fibers found
              0 concreteUninstalled : installedAt @{nameEq} selected concrete = False
              concreteUninstalled = rewrite targetFound in Refl
              0 targetUninstalled : installedAt @{nameEq} selected afterState = False
              targetUninstalled = replace
                {p = \observed => installedAt @{nameEq} selected observed = False}
                concreteIsAfter concreteUninstalled
          in void (falseNotTrue (trans (sym targetUninstalled) installedTarget))

||| Complete selected-owner dispatcher for a step whose source and target both
||| lie inside the episode. Boundary/freshness actions are eliminated; the four
||| accumulator-carrying selected rules delegate to their saturated proofs.
public export
0 selectedInstalledStepPreservesAccumulatorModel :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  actionOwner action = selected ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState} nameEq keyEq action tag
      checked) whole) ->
  installedAt @{nameEq} selected afterState = True ->
  AccumulatorModel name key world error value nameEq keyEq selected whole before ->
  AccumulatorModel name key world error value nameEq keyEq selected whole afterState
selectedInstalledStepPreservesAccumulatorModel nameEq keyEq selected
  action tag before afterState checked owner whole occurs targetInstalled model =
  let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag checked
      0 sourceInstalled = accumulatorModelInstalledAt model
  in case action of
    OInsert actor parent component => case owner of
      Refl => void (insertCannotExisting nameEq keyEq selected parent component
        before afterState tag raw (modelFiber model) (modelFound model))
    ORetire actor => case owner of
      Refl =>
        case successfulRetireTag nameEq keyEq selected before afterState tag raw of
          Refl => selectedRetirePreservesAccumulatorModel nameEq keyEq selected
            before afterState whole checked model
    ORemove actor => case owner of
      Refl =>
        void (removeCannotInstalled nameEq keyEq selected before afterState tag raw
          sourceInstalled)
    LBegin actor => case owner of
      Refl =>
        void (beginCannotInstalled nameEq keyEq selected before afterState tag raw
          sourceInstalled)
    LAdvance actor => case owner of
      Refl =>
        selectedAdvancePreservesAccumulatorModel nameEq keyEq selected before
          afterState tag checked whole occurs model
    LDivert actor => case owner of
      Refl =>
        case successfulLDivertTag nameEq keyEq selected before afterState tag raw of
          Refl => selectedDivertPreservesAccumulatorModel nameEq keyEq selected
            before afterState whole checked model
    LLeave actor => case owner of
      Refl =>
        case successfulLeaveTag nameEq keyEq selected before afterState tag raw of
          Refl => selectedLeavePreservesAccumulatorModel nameEq keyEq selected
            before afterState whole checked model
    LUnload actor => case owner of
      Refl =>
        void (unloadCannotEndInstalled nameEq keyEq selected before afterState tag
          raw targetInstalled)
