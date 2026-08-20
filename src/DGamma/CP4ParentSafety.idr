module DGamma.CP4ParentSafety

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

||| A parent is still inside the activation that licensed a child insertion.
||| Unloading is deliberately excluded: entering it is exactly a
||| `ParentRecoveryStep` in `RegistrationDiscipline`.
public export
data LifecycleOpen :
  Lifecycle key value world error name deps provision -> Type where
  OpenReloading : LifecycleOpen (Reloading remaining accumulator view)
  OpenActive : LifecycleOpen (Active accumulator view)

0 lifecycleOpenInactiveAbsurd : LifecycleOpen (Inactive outcome) -> Void
lifecycleOpenInactiveAbsurd OpenReloading impossible
lifecycleOpenInactiveAbsurd OpenActive impossible

0 lifecycleOpenUnloadingAbsurd :
  LifecycleOpen (Unloading accumulator view outcome) -> Void
lifecycleOpenUnloadingAbsurd OpenReloading impossible
lifecycleOpenUnloadingAbsurd OpenActive impossible

public export
record ParentOpenAt
  {name, key, world, error : Type} {value : key -> Type}
  (nameEq : DecEq name) (parent : name)
  (state : SystemState name key value world error) where
  constructor MkParentOpenAt
  openParentFiber : Fiber name key value world error
  openParentFound : lookupFiber @{nameEq} parent (registry state) =
    Just openParentFiber
  openParentLifecycle : LifecycleOpen (fiberLifecycle openParentFiber)

0 reloadingEndpointOpen :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingEndpoint @{nameEq} selected state = True ->
  ParentOpenAt nameEq selected state
reloadingEndpointOpen nameEq selected state present
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  reloadingEndpointOpen nameEq selected state present | Nothing =
    case present of Refl impossible
  reloadingEndpointOpen nameEq selected state present | Just fiber
    with (fiberLifecycle fiber) proof life
    reloadingEndpointOpen nameEq selected state present | Just fiber |
      Inactive outcome = case present of Refl impossible
    reloadingEndpointOpen nameEq selected state present | Just fiber |
      Reloading remaining accumulator view =
        MkParentOpenAt fiber found
          (replace {p = LifecycleOpen} (sym life) OpenReloading)
    reloadingEndpointOpen nameEq selected state present | Just fiber |
      Active accumulator view = case present of Refl impossible
    reloadingEndpointOpen nameEq selected state present | Just fiber |
      Unloading accumulator view outcome = case present of Refl impossible

0 activeEndpointOpen :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeEndpoint @{nameEq} selected state = True ->
  ParentOpenAt nameEq selected state
activeEndpointOpen nameEq selected state present
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  activeEndpointOpen nameEq selected state present | Nothing =
    case present of Refl impossible
  activeEndpointOpen nameEq selected state present | Just fiber
    with (fiberLifecycle fiber) proof life
    activeEndpointOpen nameEq selected state present | Just fiber |
      Inactive outcome = case present of Refl impossible
    activeEndpointOpen nameEq selected state present | Just fiber |
      Reloading remaining accumulator view = case present of Refl impossible
    activeEndpointOpen nameEq selected state present | Just fiber |
      Active accumulator view = MkParentOpenAt fiber found
        (replace {p = LifecycleOpen} (sym life) OpenActive)
    activeEndpointOpen nameEq selected state present | Just fiber |
      Unloading accumulator view outcome = case present of Refl impossible

0 parentOpenForeign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  ParentOpenAt nameEq selected before ->
  ParentOpenAt nameEq selected afterState
parentOpenForeign nameEq keyEq selected action distinct before afterState tag
  equation (MkParentOpenAt fiber found opened) =
    let update = applyActionLocalUpdate nameEq keyEq action before afterState tag
          equation
        frame = systemLocalUpdateForeign nameEq selected (actionOwner action)
          distinct before afterState update
        targetFound = trans frame found
    in MkParentOpenAt fiber targetFound opened

0 lifecycleOpenInstalled : (life : Lifecycle key value world error name deps provision) ->
  LifecycleOpen life -> installed life = True
lifecycleOpenInstalled (Inactive outcome) OpenReloading impossible
lifecycleOpenInstalled (Inactive outcome) OpenActive impossible
lifecycleOpenInstalled (Reloading remaining accumulator view) OpenReloading = Refl
lifecycleOpenInstalled (Reloading remaining accumulator view) OpenActive impossible
lifecycleOpenInstalled (Active accumulator view) OpenReloading impossible
lifecycleOpenInstalled (Active accumulator view) OpenActive = Refl
lifecycleOpenInstalled (Unloading accumulator view outcome) OpenReloading impossible
lifecycleOpenInstalled (Unloading accumulator view outcome) OpenActive impossible

0 parentOpenInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  ParentOpenAt nameEq selected state ->
  installedAt @{nameEq} selected state = True
parentOpenInstalled nameEq selected state
  (MkParentOpenAt fiber found opened) =
    trans (installedAtFound nameEq selected state fiber found)
      (lifecycleOpenInstalled (fiberLifecycle fiber) opened)

0 parentOpenCannotInsertSelf :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq}
    (OInsert selected parent component) before = Just (tag, afterState) ->
  ParentOpenAt nameEq selected before -> Void
parentOpenCannotInsertSelf nameEq keyEq selected parent component before
  afterState tag checked opened =
    case installationEvolutionStep nameEq keyEq selected
      (OInsert selected parent component) tag before afterState checked of
      RemainedUninstalled sourceFalse targetFalse =>
        case trans (sym sourceFalse)
          (parentOpenInstalled nameEq selected before opened) of Refl impossible

0 retireActionAtFound :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected fibers = Just fiber ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (ORetire selected)
    (MkSystemState ambient fibers) =
  Just (ORetireTag, MkSystemState ambient
    (replaceBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error}
      selected (retireFiber fiber) fibers))
retireActionAtFound nameEq keyEq selected ambient fibers fiber found =
  rewrite found in Refl

0 parentOpenRetire :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  ParentOpenAt nameEq selected before ->
  ParentOpenAt nameEq selected afterState
parentOpenRetire nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  (MkParentOpenAt fiber found opened) =
    let reduced :
          (Just (ORetireTag,
            MkSystemState ambient
              (replaceBinding @{nameEq} selected (retireFiber fiber) fibers)) =
           Just (tag, afterState))
        reduced = trans
          (sym (retireActionAtFound nameEq keyEq selected ambient fibers fiber
            found)) equation
    in case justInjective reduced of
          Refl => case fiber of
            MkFiber component parent retired table
              (Reloading remaining accumulator view) =>
                MkParentOpenAt (retireFiber fiber)
                  (lookupReplacedFiber selected fiber (retireFiber fiber) fibers
                    found) opened
            MkFiber component parent retired table (Active accumulator view) =>
                MkParentOpenAt (retireFiber fiber)
                  (lookupReplacedFiber selected fiber (retireFiber fiber) fibers
                    found) opened
            MkFiber component parent retired table (Inactive outcome) =>
              void (lifecycleOpenInactiveAbsurd opened)
            MkFiber component parent retired table
              (Unloading accumulator view outcome) =>
                void (lifecycleOpenUnloadingAbsurd opened)

0 beginActionOpenIsNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected fibers = Just fiber ->
  LifecycleOpen (fiberLifecycle fiber) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (LBegin selected)
    (MkSystemState ambient fibers) = Nothing
beginActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table (Inactive outcome)) found opened =
    void (lifecycleOpenInactiveAbsurd opened)
beginActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table
    (Reloading remaining accumulator view)) found OpenReloading =
      rewrite found in Refl
beginActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table (Active accumulator view)) found
  OpenActive = rewrite found in Refl
beginActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table
    (Unloading accumulator view outcome)) found opened =
      void (lifecycleOpenUnloadingAbsurd opened)

0 unloadActionOpenIsNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected fibers = Just fiber ->
  LifecycleOpen (fiberLifecycle fiber) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (LUnload selected)
    (MkSystemState ambient fibers) = Nothing
unloadActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table (Inactive outcome)) found opened =
    void (lifecycleOpenInactiveAbsurd opened)
unloadActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table
    (Reloading remaining accumulator view)) found OpenReloading =
      rewrite found in Refl
unloadActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table (Active accumulator view)) found
  OpenActive = rewrite found in Refl
unloadActionOpenIsNothing nameEq keyEq selected ambient fibers
  (MkFiber component parent retired table
    (Unloading accumulator view outcome)) found opened =
      void (lifecycleOpenUnloadingAbsurd opened)

0 parentOpenCannotBegin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (tag, afterState) ->
  ParentOpenAt nameEq selected before -> Void
parentOpenCannotBegin nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  (MkParentOpenAt fiber found opened) =
    nothingIsNotJust (trans
      (sym (beginActionOpenIsNothing nameEq keyEq selected ambient fibers fiber
        found opened)) equation)

0 parentOpenCannotUnload :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) ->
  ParentOpenAt nameEq selected before -> Void
parentOpenCannotUnload nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  (MkParentOpenAt fiber found opened) =
    nothingIsNotJust (trans
      (sym (unloadActionOpenIsNothing nameEq keyEq selected ambient fibers fiber
        found opened)) equation)

0 parentRecoveryProvenanceHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (parent, child : name) ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  ChildRetirementProvenance parent child
    (MoreTransitions transition rest) ->
  ParentRecoveryStep parent transition -> Void
parentRecoveryProvenanceHead parent child transition rest
  (ParentDoesNotRecover
    (NoParentRecoveryStep transition rest noRecovery tail)) recovery =
      noRecovery recovery
parentRecoveryProvenanceHead parent child transition rest
  (ChildRetiredBeforeParent
    (ChildRetiresLater transition rest noRecovery tail)) recovery =
      noRecovery recovery
parentRecoveryProvenanceHead parent child transition rest
  (ChildRetiredBeforeParent
    (ChildRetiresNow transition rest retiresNow)) recovery =
      case recovery of
        ParentLeaves leaves =>
          case trans (sym retiresNow) leaves of Refl impossible
        ParentDivertsBefore diverts =>
          case trans (sym retiresNow) diverts of Refl impossible
        ParentDivertsAfter advances tagShape =>
          case trans (sym retiresNow) advances of Refl impossible
        ParentRaises advances tagShape =>
          case trans (sym retiresNow) advances of Refl impossible

0 parentOpenOwnerStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  ParentOpenAt nameEq (actionOwner action) before ->
  (ParentRecoveryStep (actionOwner action)
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) -> Void) ->
  ParentOpenAt nameEq (actionOwner action) afterState
parentOpenOwnerStep nameEq keyEq
  action@(OInsert selected parent component) tag before afterState checked opened
  noRecovery =
    void (parentOpenCannotInsertSelf nameEq keyEq selected parent component
      before afterState tag checked opened)
parentOpenOwnerStep nameEq keyEq action@(ORetire selected) tag before afterState
  checked opened noRecovery =
    parentOpenRetire nameEq keyEq selected before afterState tag
      (checkedActionProjects nameEq keyEq action before afterState tag checked)
      opened
parentOpenOwnerStep nameEq keyEq action@(ORemove selected) tag before afterState
  checked opened noRecovery =
    case installationEvolutionStep nameEq keyEq selected action tag before
      afterState checked of
      RemainedUninstalled sourceFalse targetFalse =>
        case trans (sym sourceFalse)
          (parentOpenInstalled nameEq selected before opened) of Refl impossible
parentOpenOwnerStep nameEq keyEq action@(LBegin selected) tag before afterState
  checked opened noRecovery =
    void (parentOpenCannotBegin nameEq keyEq selected before afterState tag
      (checkedActionProjects nameEq keyEq action before afterState tag checked)
      opened)
parentOpenOwnerStep nameEq keyEq action@(LAdvance selected) tag before afterState
  checked opened noRecovery =
    case advanceStructureTheorem nameEq keyEq selected before afterState tag
      (checkedActionProjects nameEq keyEq action before afterState tag checked) of
      IterAdvance fiber found witness reloading =>
        reloadingEndpointOpen nameEq selected afterState reloading
      FinishAdvance fiber found witness active =>
        activeEndpointOpen nameEq selected afterState active
      DivertAdvance unloading =>
        void (noRecovery (ParentDivertsAfter Refl Refl))
      RaiseAdvance unloading =>
        void (noRecovery (ParentRaises Refl Refl))
parentOpenOwnerStep nameEq keyEq action@(LDivert selected) tag before afterState
  checked opened noRecovery = void (noRecovery (ParentDivertsBefore Refl))
parentOpenOwnerStep nameEq keyEq action@(LLeave selected) tag before afterState
  checked opened noRecovery = void (noRecovery (ParentLeaves Refl))
parentOpenOwnerStep nameEq keyEq action@(LUnload selected) tag before afterState
  checked opened noRecovery =
    void (parentOpenCannotUnload nameEq keyEq selected before afterState tag
      (checkedActionProjects nameEq keyEq action before afterState tag checked)
      opened)

0 retirementProvenanceTail :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (parent, child : name) ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  (transitionAction transition = ORetire child -> Void) ->
  ChildRetirementProvenance parent child
    (MoreTransitions transition rest) ->
  ChildRetirementProvenance parent child rest
retirementProvenanceTail parent child transition rest notNow
  (ParentDoesNotRecover
    (NoParentRecoveryStep transition rest noRecovery tail)) =
      ParentDoesNotRecover tail
retirementProvenanceTail parent child transition rest notNow
  (ChildRetiredBeforeParent
    (ChildRetiresLater transition rest noRecovery tail)) =
      ChildRetiredBeforeParent tail
retirementProvenanceTail parent child transition rest notNow
  (ChildRetiredBeforeParent
    (ChildRetiresNow transition rest retiresNow)) =
      void (notNow retiresNow)

public export
record PendingChild
  {name, key, world, error : Type} {value : key -> Type}
  (nameEq : DecEq name) (state : SystemState name key value world error)
  {finalState : SystemState name key value world error}
  (trace : Transitions state finalState) (child, parent : name) where
  constructor MkPendingChild
  pendingNamesDistinct : Not (child = parent)
  pendingParentOpen : ParentOpenAt nameEq parent state
  pendingRetirement : ChildRetirementProvenance parent child trace

public export
PendingChildrenSafe :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  {finalState : SystemState name key value world error} ->
  Transitions state finalState -> Type
PendingChildrenSafe nameEq state trace =
  (child, parent : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} child (registry state) = Just fiber ->
  fiberParent fiber = ChildOf parent ->
  retired fiber = False ->
  PendingChild nameEq state trace child parent

0 emptyPendingChildrenSafe :
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  (trace : Transitions state finalState) ->
  bindings (registry state) = [] ->
  PendingChildrenSafe nameEq state trace
emptyPendingChildrenSafe nameEq state trace empty child parent fiber found
  childParent notRetired =
    let absent = lookupFiberEmptyRegistry nameEq child state empty
    in void (nothingIsNotJust (trans (sym absent) found))

0 actionCannotRetireForeign :
  (child : name) -> (action : Action name key value world error) ->
  Not (child = actionOwner action) -> action = ORetire child -> Void
actionCannotRetireForeign child action distinct retires =
  distinct (sym (cong actionOwner retires))

0 pendingForeignChildStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (rest : Transitions afterState finalState) ->
  PendingChildrenSafe nameEq before
    (MoreTransitions
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) rest) ->
  (child, parent : name) -> (fiber : Fiber name key value world error) ->
  Not (child = actionOwner action) ->
  lookupFiber @{nameEq} child (registry afterState) = Just fiber ->
  fiberParent fiber = ChildOf parent -> retired fiber = False ->
  PendingChild nameEq afterState rest child parent
pendingForeignChildStep nameEq keyEq action tag before afterState checked rest
  sourceSafe child parent fiber childDistinct found childParent notRetired =
    let 0 raw : (applyAction @{nameEq} @{keyEq} action before =
          Just (tag, afterState))
        raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 update : SystemLocalUpdate name key world error value nameEq
          (actionOwner action) before afterState
        update = applyActionLocalUpdate nameEq keyEq action before afterState tag
          raw
        0 sourceFound :
          (lookupFiber @{nameEq} child (registry before) = Just fiber)
        sourceFound = trans
          (sym (systemLocalUpdateForeign nameEq child (actionOwner action)
            childDistinct before afterState update)) found
        0 sourcePending : PendingChild nameEq before
          (MoreTransitions
            (Fired {before = before} {afterState = afterState}
              nameEq keyEq action tag checked) rest)
          child parent
        sourcePending = sourceSafe child parent fiber sourceFound childParent
          notRetired
        0 headNoRecovery :
          (ParentRecoveryStep parent
            (Fired {before = before} {afterState = afterState}
              nameEq keyEq action tag checked) -> Void)
        headNoRecovery = parentRecoveryProvenanceHead parent child
          (Fired {before = before} {afterState = afterState}
            nameEq keyEq action tag checked) rest
          (pendingRetirement sourcePending)
        0 targetOpen : ParentOpenAt nameEq parent afterState
        targetOpen = case decEq @{nameEq} parent (actionOwner action) of
          No parentDistinct => parentOpenForeign nameEq keyEq parent action
            parentDistinct before afterState tag raw
            (pendingParentOpen sourcePending)
          Yes Refl => parentOpenOwnerStep nameEq keyEq action tag before
            afterState checked (pendingParentOpen sourcePending) headNoRecovery
        0 tailRetirement : ChildRetirementProvenance parent child rest
        tailRetirement = retirementProvenanceTail parent child
          (Fired {before = before} {afterState = afterState}
            nameEq keyEq action tag checked) rest
          (actionCannotRetireForeign child action childDistinct)
          (pendingRetirement sourcePending)
    in MkPendingChild (pendingNamesDistinct sourcePending) targetOpen
      tailRetirement

public export
data LifecycleActionOnly :
  Action name key value world error -> Type where
  IsBegin : LifecycleActionOnly (LBegin selected)
  IsAdvance : LifecycleActionOnly (LAdvance selected)
  IsDivert : LifecycleActionOnly (LDivert selected)
  IsLeave : LifecycleActionOnly (LLeave selected)
  IsUnload : LifecycleActionOnly (LUnload selected)

0 lifecycleActionSourceFound :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  LifecycleActionOnly action ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} (actionOwner action) (registry before) = Just fiber)
lifecycleActionSourceFound nameEq keyEq (LBegin selected) IsBegin before
  afterState tag equation with (lookupFiber @{nameEq} selected (registry before))
  lifecycleActionSourceFound nameEq keyEq (LBegin selected) IsBegin before
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  lifecycleActionSourceFound nameEq keyEq (LBegin selected) IsBegin before
    afterState tag equation | Just fiber = (fiber ** Refl)
lifecycleActionSourceFound nameEq keyEq (LAdvance selected) IsAdvance before
  afterState tag equation with (lookupFiber @{nameEq} selected (registry before))
  lifecycleActionSourceFound nameEq keyEq (LAdvance selected) IsAdvance before
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  lifecycleActionSourceFound nameEq keyEq (LAdvance selected) IsAdvance before
    afterState tag equation | Just fiber = (fiber ** Refl)
lifecycleActionSourceFound nameEq keyEq (LDivert selected) IsDivert before
  afterState tag equation with (lookupFiber @{nameEq} selected (registry before))
  lifecycleActionSourceFound nameEq keyEq (LDivert selected) IsDivert before
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  lifecycleActionSourceFound nameEq keyEq (LDivert selected) IsDivert before
    afterState tag equation | Just fiber = (fiber ** Refl)
lifecycleActionSourceFound nameEq keyEq (LLeave selected) IsLeave before
  afterState tag equation with (lookupFiber @{nameEq} selected (registry before))
  lifecycleActionSourceFound nameEq keyEq (LLeave selected) IsLeave before
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  lifecycleActionSourceFound nameEq keyEq (LLeave selected) IsLeave before
    afterState tag equation | Just fiber = (fiber ** Refl)
lifecycleActionSourceFound nameEq keyEq (LUnload selected) IsUnload before
  afterState tag equation with (lookupFiber @{nameEq} selected (registry before))
  lifecycleActionSourceFound nameEq keyEq (LUnload selected) IsUnload before
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  lifecycleActionSourceFound nameEq keyEq (LUnload selected) IsUnload before
    afterState tag equation | Just fiber = (fiber ** Refl)

0 lifecycleActionNotRetire :
  (action : Action name key value world error) -> LifecycleActionOnly action ->
  action = ORetire (actionOwner action) -> Void
lifecycleActionNotRetire (LBegin selected) IsBegin Refl impossible
lifecycleActionNotRetire (LAdvance selected) IsAdvance Refl impossible
lifecycleActionNotRetire (LDivert selected) IsDivert Refl impossible
lifecycleActionNotRetire (LLeave selected) IsLeave Refl impossible
lifecycleActionNotRetire (LUnload selected) IsUnload Refl impossible

0 lookupNotElemNothingQ : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries wanted entries = Nothing
lookupNotElemNothingQ wanted [] absent = Refl
lookupNotElemNothingQ wanted (Bind current observed :: rest) absent
  with (decEq wanted current)
  lookupNotElemNothingQ current (Bind current observed :: rest) absent |
    Yes Refl = void (absent Here)
  lookupNotElemNothingQ wanted (Bind current observed :: rest) absent |
    No distinct = lookupNotElemNothingQ wanted rest
      (\later => absent (There later))

0 lookupDeleteSelfQ : DecEq key => (removed : key) ->
  (context : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed context) = Nothing
lookupDeleteSelfQ removed (MkCoeffectContext entries unique) =
  lookupNotElemNothingQ removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

data RegistryLocalUpdateView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  Registry name key value world error -> Registry name key value world error ->
  Type where
  ViewedInsert :
    (inserted : Fiber name key value world error) ->
    (absent : lookupFiber @{nameEq} actor source = Nothing) ->
    target = insertBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error}
      actor inserted source absent ->
    RegistryLocalUpdateView {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq actor source target
  ViewedReplace :
    (next, oldFiber : Fiber name key value world error) ->
    (oldFound : lookupFiber @{nameEq} actor source = Just oldFiber) ->
    (staticParent : fiberParent next = fiberParent oldFiber) ->
    RetirementUpdate oldFiber next ->
    target = replaceBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor next source ->
    RegistryLocalUpdateView {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq actor source target
  ViewedDelete :
    (oldFiber : Fiber name key value world error) ->
    (oldFound : lookupFiber @{nameEq} actor source = Just oldFiber) ->
    target = deleteBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor source ->
    RegistryLocalUpdateView {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq actor source target

0 registryLocalUpdateView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (update : RegistryLocalUpdate name key world error value nameEq actor
    source target) ->
  RegistryLocalUpdateView {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq actor source target
registryLocalUpdateView nameEq actor source _
  (LocalInsert inserted absent) = ViewedInsert inserted absent Refl
registryLocalUpdateView nameEq actor source _
  (LocalReplace next {oldFiber} {oldFound} {staticParent}
    {retirementUpdate}) =
      ViewedReplace next oldFiber oldFound staticParent retirementUpdate Refl
registryLocalUpdateView nameEq actor source _
  (LocalDelete {oldFiber} {oldFound}) =
    ViewedDelete oldFiber oldFound Refl

0 pendingSelectedLifecycleStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  LifecycleActionOnly action -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (rest : Transitions afterState finalState) ->
  PendingChildrenSafe nameEq before
    (MoreTransitions
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) rest) ->
  (parent : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner action) (registry afterState) = Just fiber ->
  fiberParent fiber = ChildOf parent -> retired fiber = False ->
  PendingChild nameEq afterState rest (actionOwner action) parent
pendingSelectedLifecycleStep nameEq keyEq action lifecycle tag
  (MkSystemState beforeWorld sourceRegistry)
  (MkSystemState afterWorld targetRegistryValue)
  checked rest sourceSafe parent fiber found childParent notRetired =
    let 0 raw : (applyAction @{nameEq} @{keyEq} action (MkSystemState beforeWorld sourceRegistry) =
          Just (tag, (MkSystemState afterWorld targetRegistryValue)))
        raw = checkedActionProjects nameEq keyEq action (MkSystemState beforeWorld sourceRegistry) (MkSystemState afterWorld targetRegistryValue) tag
          checked
        0 update : SystemLocalUpdate name key world error value nameEq
          (actionOwner action) (MkSystemState beforeWorld sourceRegistry) (MkSystemState afterWorld targetRegistryValue)
        update = applyActionLocalUpdate nameEq keyEq action (MkSystemState beforeWorld sourceRegistry) (MkSystemState afterWorld targetRegistryValue) tag
          raw
        0 sourceExists :
          (sourceFiber : Fiber name key value world error **
            lookupFiber @{nameEq} (actionOwner action) sourceRegistry =
              Just sourceFiber)
        sourceExists = lifecycleActionSourceFound nameEq keyEq action lifecycle
          (MkSystemState beforeWorld sourceRegistry) (MkSystemState afterWorld targetRegistryValue) tag raw
    in case registryLocalUpdateView nameEq (actionOwner action) sourceRegistry
      targetRegistryValue (systemRegistryUpdate update) of
      ViewedInsert inserted absent targetShape =>
        let (sourceFiber ** sourceFound) = sourceExists
        in void (nothingIsNotJust (trans (sym absent) sourceFound))
      ViewedDelete oldFiber oldFound targetShape =>
        let 0 observedFound :
              (lookupFiber @{nameEq} (actionOwner action)
                (deleteBinding @{nameEq} (actionOwner action) sourceRegistry) =
                  Just fiber)
            observedFound = replace
              {p = \context => lookupFiber @{nameEq} (actionOwner action)
                context = Just fiber}
              targetShape found
        in void (nothingIsNotJust
          (trans (sym (lookupDeleteSelfQ (actionOwner action) sourceRegistry))
            observedFound))
      ViewedReplace next oldFiber oldFound staticParent retirementUpdate
        targetShape =>
          let 0 nextFound :
                (lookupFiber @{nameEq} (actionOwner action)
                  (replaceBinding @{nameEq} (actionOwner action) next
                    sourceRegistry) = Just next)
              nextFound = lookupReplacedFiber (actionOwner action) oldFiber
                next sourceRegistry oldFound
              0 observedFound :
                (lookupFiber @{nameEq} (actionOwner action)
                  (replaceBinding @{nameEq} (actionOwner action) next
                    sourceRegistry) = Just fiber)
              observedFound = replace
                {p = \context => lookupFiber @{nameEq} (actionOwner action)
                  context = Just fiber}
                targetShape found
              0 sameNext : (next = fiber)
              sameNext = justInjective (trans (sym nextFound) observedFound)
          in case sameNext of
            Refl =>
              let 0 sourceParent : (fiberParent oldFiber = ChildOf parent)
                  sourceParent = trans (sym staticParent) childParent
                  0 sourceNotRetired : (retired oldFiber = False)
                  sourceNotRetired = case retirementUpdate of
                    RetirementStable stable => trans (sym stable) notRetired
                    RetirementApplied applied =>
                      void (case trans (sym applied) notRetired of Refl impossible)
                  0 sourcePending : PendingChild {name = name} {key = key}
                    {value = value} {world = world} {error = error} nameEq
                    (MkSystemState beforeWorld sourceRegistry)
                    (MoreTransitions
                      (Fired {before = MkSystemState beforeWorld sourceRegistry}
                        {afterState = MkSystemState afterWorld targetRegistryValue}
                        nameEq keyEq action tag checked) rest)
                    (actionOwner action) parent
                  sourcePending = sourceSafe (actionOwner action) parent
                    oldFiber oldFound sourceParent sourceNotRetired
                  0 parentDistinct : Not (parent = actionOwner action)
                  parentDistinct same = pendingNamesDistinct sourcePending
                    (sym same)
                  0 targetOpen : ParentOpenAt {name = name} {key = key}
                    {value = value} {world = world} {error = error}
                    nameEq parent (MkSystemState afterWorld targetRegistryValue)
                  targetOpen = parentOpenForeign nameEq keyEq parent action
                    parentDistinct (MkSystemState beforeWorld sourceRegistry)
                    (MkSystemState afterWorld targetRegistryValue) tag raw
                    (pendingParentOpen sourcePending)
                  0 tailRetirement : ChildRetirementProvenance parent
                    (actionOwner action) rest
                  tailRetirement = retirementProvenanceTail parent
                    (actionOwner action)
                    (Fired {before = MkSystemState beforeWorld sourceRegistry}
                      {afterState = MkSystemState afterWorld targetRegistryValue}
                      nameEq keyEq action tag checked) rest
                    (lifecycleActionNotRetire action lifecycle)
                    (pendingRetirement sourcePending)
              in MkPendingChild (pendingNamesDistinct sourcePending) targetOpen
                tailRetirement

0 childOfInjective : ChildOf left = ChildOf right -> left = right
childOfInjective Refl = Refl

0 rootIsNotChild : Root = ChildOf parent -> Void
rootIsNotChild Refl impossible

0 retiredAfterRetireQ : (fiber : Fiber name key value world error) ->
  retired (retireFiber fiber) = True
retiredAfterRetireQ (MkFiber component parent retiredFlag table lifecycle) = Refl

0 retireTargetIsRetired :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry afterState) = Just fiber ->
  retired fiber = True
retireTargetIsRetired nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation fiber targetFound
  with (lookupFiber @{nameEq} selected fibers) proof sourceFound
  retireTargetIsRetired nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation fiber targetFound |
    Nothing = void (nothingIsNotJust equation)
  retireTargetIsRetired nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation fiber targetFound |
    Just sourceFiber = case justInjective equation of
      Refl =>
        let 0 retiredFound :
              (lookupFiber @{nameEq} selected
                (replaceBinding @{nameEq} selected (retireFiber sourceFiber)
                  fibers) = Just (retireFiber sourceFiber))
            retiredFound = lookupReplacedFiber selected sourceFiber
              (retireFiber sourceFiber) fibers sourceFound
            0 same : (retireFiber sourceFiber = fiber)
            same = justInjective (trans (sym retiredFound) targetFound)
        in case same of Refl => retiredAfterRetireQ sourceFiber

public export
0 removeTargetIsAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (ORemove selected) before = Just (tag, afterState) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected (registry afterState) = Nothing
removeTargetIsAbsent nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers)
  removeTargetIsAbsent nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  removeTargetIsAbsent nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation |
    Just sourceFiber
    with (retired sourceFiber && isInactive (fiberLifecycle sourceFiber) &&
      not (hasChild @{nameEq} selected fibers))
    removeTargetIsAbsent nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation |
      Just sourceFiber | False = void (nothingIsNotJust equation)
    removeTargetIsAbsent nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation |
      Just sourceFiber | True =
        case justInjective equation of
          Refl => lookupDeleteSelfQ selected fibers

0 insertedRootCannotBeChild :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (component : Component key value world error) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert selected Root component) before = Just (tag, afterState)) ->
  (parent : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry afterState) = Just fiber ->
  fiberParent fiber = ChildOf parent -> Void
insertedRootCannotBeChild nameEq keyEq selected component tag before afterState
  checked parent fiber found childParent =
    let 0 raw : (applyAction @{nameEq} @{keyEq}
          (OInsert selected Root component) before = Just (tag, afterState))
        raw = checkedActionProjects nameEq keyEq
          (OInsert selected Root component) before afterState tag checked
        0 freshFound :
          (lookupFiber @{nameEq} selected (registry afterState) =
            Just (freshFiber component Root))
        freshFound = oInsertResultLookup nameEq keyEq selected Root component
          before afterState tag raw
        0 same : freshFiber component Root = fiber
        same = justInjective (trans (sym freshFound) found)
    in case same of
      Refl => rootIsNotChild childParent

0 insertedChildPending :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, insertedParent : name) ->
  (component : Component key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert selected (ChildOf insertedParent) component) before =
      Just (tag, afterState)) ->
  (rest : Transitions afterState finalState) ->
  ParentRegistrationYield protocol nameEq insertedParent component before ->
  ChildRetirementProvenance insertedParent selected rest ->
  (parent : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry afterState) = Just fiber ->
  fiberParent fiber = ChildOf parent -> retired fiber = False ->
  PendingChild nameEq afterState rest selected parent
insertedChildPending protocol nameEq keyEq selected insertedParent component tag
  before afterState checked rest yielded retirement parent fiber found childParent
  notRetired =
    let 0 raw : (applyAction @{nameEq} @{keyEq}
          (OInsert selected (ChildOf insertedParent) component) before =
            Just (tag, afterState))
        raw = checkedActionProjects nameEq keyEq
          (OInsert selected (ChildOf insertedParent) component) before afterState
          tag checked
        0 freshFound :
          (lookupFiber @{nameEq} selected (registry afterState) =
            Just (freshFiber component (ChildOf insertedParent)))
        freshFound = oInsertResultLookup nameEq keyEq selected
          (ChildOf insertedParent) component before afterState tag raw
        0 sameFiber : freshFiber component (ChildOf insertedParent) = fiber
        sameFiber = justInjective (trans (sym freshFound) found)
        0 sourceParentOpen : ParentOpenAt nameEq insertedParent before
        sourceParentOpen = MkParentOpenAt (parentFiberAtYield yielded)
          (parentFoundAtYield yielded)
          (replace {p = LifecycleOpen} (sym (parentAtYield yielded))
            OpenReloading)
        0 sourceUninstalled : installedAt @{nameEq} selected before = False
        sourceUninstalled = case installationEvolutionStep nameEq keyEq selected
          (OInsert selected (ChildOf insertedParent) component) tag before
          afterState checked of
            RemainedUninstalled sourceFalse targetFalse => sourceFalse
        0 namesDistinct : Not (selected = insertedParent)
        namesDistinct same = case same of
          Refl => case trans (sym sourceUninstalled)
            (parentOpenInstalled nameEq selected before sourceParentOpen) of
              Refl impossible
        0 targetParentOpen : ParentOpenAt nameEq insertedParent afterState
        targetParentOpen = parentOpenForeign nameEq keyEq insertedParent
          (OInsert selected (ChildOf insertedParent) component)
          (\same => namesDistinct (sym same)) before afterState tag raw
          sourceParentOpen
    in case sameFiber of
      Refl => case childOfInjective childParent of
        Refl => MkPendingChild namesDistinct targetParentOpen retirement

0 pendingChildrenSafeStep :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (rest : Transitions afterState finalState) ->
  RegistrationStepDiscipline protocol nameEq action before rest ->
  PendingChildrenSafe nameEq before
    (MoreTransitions
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) rest) ->
  PendingChildrenSafe nameEq afterState rest
pendingChildrenSafeStep protocol nameEq keyEq
  (OInsert selected Root component) tag before afterState checked rest
  discipline sourceSafe child parent fiber found childParent notRetired
  with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq
    (OInsert selected Root component) tag before afterState checked rest
    discipline sourceSafe child parent fiber found childParent notRetired |
    No distinct = pendingForeignChildStep nameEq keyEq (OInsert selected Root component) tag before
      afterState checked rest sourceSafe child parent fiber distinct found
      childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq
    (OInsert selected Root component) tag before afterState checked rest
    discipline sourceSafe selected parent fiber found childParent notRetired |
    Yes Refl = void (insertedRootCannotBeChild nameEq keyEq selected component
      tag before afterState checked parent fiber found childParent)
pendingChildrenSafeStep protocol nameEq keyEq
  (OInsert selected (ChildOf insertedParent) component) tag before
  afterState checked rest (yielded, retirement) sourceSafe child parent fiber
  found childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq
    (OInsert selected (ChildOf insertedParent) component) tag before
    afterState checked rest (yielded, retirement) sourceSafe child parent fiber
    found childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (OInsert selected (ChildOf insertedParent) component) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq
    (OInsert selected (ChildOf insertedParent) component) tag before
    afterState checked rest (yielded, retirement) sourceSafe selected parent
    fiber found childParent notRetired | Yes Refl =
      insertedChildPending protocol nameEq keyEq selected insertedParent
        component tag before afterState checked rest yielded retirement parent
        fiber found childParent notRetired
pendingChildrenSafeStep protocol nameEq keyEq (ORetire selected) tag
  before afterState checked rest discipline sourceSafe child parent fiber found
  childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq (ORetire selected) tag
    before afterState checked rest discipline sourceSafe child parent fiber found
    childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (ORetire selected) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq (ORetire selected) tag
    before afterState checked rest discipline sourceSafe selected parent fiber
    found childParent notRetired | Yes Refl =
      let 0 raw : (applyAction @{nameEq} @{keyEq} (ORetire selected) before =
            Just (tag, afterState))
          raw = checkedActionProjects nameEq keyEq (ORetire selected) before afterState tag
            checked
          0 targetRetired : retired fiber = True
          targetRetired = retireTargetIsRetired nameEq keyEq selected before
            afterState tag raw fiber found
      in case trans (sym targetRetired) notRetired of Refl impossible
pendingChildrenSafeStep protocol nameEq keyEq (ORemove selected) tag
  before afterState checked rest discipline sourceSafe child parent fiber found
  childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq (ORemove selected) tag
    before afterState checked rest discipline sourceSafe child parent fiber found
    childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (ORemove selected) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq (ORemove selected) tag
    before afterState checked rest discipline sourceSafe selected parent fiber
    found childParent notRetired | Yes Refl =
      let 0 raw : (applyAction @{nameEq} @{keyEq} (ORemove selected) before =
            Just (tag, afterState))
          raw = checkedActionProjects nameEq keyEq (ORemove selected) before afterState tag
            checked
          0 absent :
            (lookupFiber @{nameEq} {key = key} {value = value}
              {world = world} {error = error} selected
              (registry afterState) = Nothing)
          absent = removeTargetIsAbsent nameEq keyEq selected before afterState
            tag raw
      in void (nothingIsNotJust (trans (sym absent) found))
pendingChildrenSafeStep protocol nameEq keyEq (LBegin selected) tag
  before afterState checked rest discipline sourceSafe child parent fiber found
  childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq (LBegin selected) tag
    before afterState checked rest discipline sourceSafe child parent fiber found
    childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (LBegin selected) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq (LBegin selected) tag
    before afterState checked rest discipline sourceSafe selected parent fiber
    found childParent notRetired | Yes Refl =
      pendingSelectedLifecycleStep nameEq keyEq (LBegin selected) IsBegin tag before
        afterState checked rest sourceSafe parent fiber found childParent
        notRetired
pendingChildrenSafeStep protocol nameEq keyEq (LAdvance selected) tag
  before afterState checked rest discipline sourceSafe child parent fiber found
  childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq (LAdvance selected) tag
    before afterState checked rest discipline sourceSafe child parent fiber found
    childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (LAdvance selected) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq (LAdvance selected) tag
    before afterState checked rest discipline sourceSafe selected parent fiber
    found childParent notRetired | Yes Refl =
      pendingSelectedLifecycleStep nameEq keyEq (LAdvance selected) IsAdvance tag before
        afterState checked rest sourceSafe parent fiber found childParent
        notRetired
pendingChildrenSafeStep protocol nameEq keyEq (LDivert selected) tag
  before afterState checked rest discipline sourceSafe child parent fiber found
  childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq (LDivert selected) tag
    before afterState checked rest discipline sourceSafe child parent fiber found
    childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (LDivert selected) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq (LDivert selected) tag
    before afterState checked rest discipline sourceSafe selected parent fiber
    found childParent notRetired | Yes Refl =
      pendingSelectedLifecycleStep nameEq keyEq (LDivert selected) IsDivert tag before
        afterState checked rest sourceSafe parent fiber found childParent
        notRetired
pendingChildrenSafeStep protocol nameEq keyEq (LLeave selected) tag
  before afterState checked rest discipline sourceSafe child parent fiber found
  childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq (LLeave selected) tag
    before afterState checked rest discipline sourceSafe child parent fiber found
    childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (LLeave selected) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq (LLeave selected) tag
    before afterState checked rest discipline sourceSafe selected parent fiber
    found childParent notRetired | Yes Refl =
      pendingSelectedLifecycleStep nameEq keyEq (LLeave selected) IsLeave tag before
        afterState checked rest sourceSafe parent fiber found childParent
        notRetired
pendingChildrenSafeStep protocol nameEq keyEq (LUnload selected) tag
  before afterState checked rest discipline sourceSafe child parent fiber found
  childParent notRetired with (decEq @{nameEq} child selected)
  pendingChildrenSafeStep protocol nameEq keyEq (LUnload selected) tag
    before afterState checked rest discipline sourceSafe child parent fiber found
    childParent notRetired | No distinct =
      pendingForeignChildStep nameEq keyEq (LUnload selected) tag before afterState checked
        rest sourceSafe child parent fiber distinct found childParent notRetired
  pendingChildrenSafeStep protocol nameEq keyEq (LUnload selected) tag
    before afterState checked rest discipline sourceSafe selected parent fiber
    found childParent notRetired | Yes Refl =
      pendingSelectedLifecycleStep nameEq keyEq (LUnload selected) IsUnload tag before
        afterState checked rest sourceSafe parent fiber found childParent
        notRetired

0 tracePendingChildrenSafe :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions first finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  RegistrationDiscipline protocol nameEq trace ->
  PendingChildrenSafe nameEq first trace ->
  PendingChildrenSafe nameEq finalState NoTransitions
tracePendingChildrenSafe protocol nameEq keyEq NoTransitions AlignedEnd
  RegistrationDisciplineEnd sourceSafe = sourceSafe
tracePendingChildrenSafe protocol nameEq keyEq
  (MoreTransitions
    (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest)
  (RegistrationDisciplineStep
    (Fired nameEq keyEq action tag checked) rest stepDiscipline tailDiscipline)
  sourceSafe =
    tracePendingChildrenSafe protocol nameEq keyEq rest alignedRest
      tailDiscipline
      (pendingChildrenSafeStep protocol nameEq keyEq action tag first middle
        checked rest stepDiscipline sourceSafe)

public export
0 reachedPendingChildrenSafe :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  PendingChildrenSafe nameEq state NoTransitions
reachedPendingChildrenSafe protocol nameEq keyEq state reached discipline =
  tracePendingChildrenSafe protocol nameEq keyEq (reachTrace reached)
    (reachAligned reached) discipline
    (emptyPendingChildrenSafe nameEq (reachInitial reached) (reachTrace reached)
      (reachInitialEmpty reached))

||| The endpoint parent of every current non-retired child is still Reloading
||| or Active. This is the constructive operational consequence of
||| `ChildRetirementProvenance` used by Lemma 70.
public export
0 reachedNonRetiredChildParentOpen :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationDiscipline protocol nameEq (reachTrace reached) ->
  (child, parent : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} child (registry state) = Just fiber ->
  fiberParent fiber = ChildOf parent -> retired fiber = False ->
  ParentOpenAt nameEq parent state
reachedNonRetiredChildParentOpen protocol nameEq keyEq state reached discipline
  child parent fiber found childParent notRetired =
    pendingParentOpen
      (reachedPendingChildrenSafe protocol nameEq keyEq state reached discipline
        child parent fiber found childParent notRetired)
