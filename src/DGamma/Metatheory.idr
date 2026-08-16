module DGamma.Metatheory

import DGamma.Core
import DGamma.Coeffects
import DGamma.Unified
import DGamma.Calculus
import Decidable.Equality
import Data.List
import Data.List.Elem
import Data.Maybe

%default total

public export
parentValid : DecEq name => Parent name -> Registry name key value world error -> Bool
parentValid Root fibers = True
parentValid (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
parentChainSafe : DecEq name => Nat -> List name -> name ->
  Registry name key value world error -> Bool
parentChainSafe Z seen current fibers = False
parentChainSafe (S fuel) seen current fibers = case lookupFiber current fibers of
  Nothing => False
  Just fiber => case fiberParent fiber of
    Root => True
    ChildOf parent => if elemDec parent seen
      then False
      else parentChainSafe fuel (parent :: seen) parent fibers

public export
viewProvidersPresent : DecEq name => Registry name key value world error ->
  View name deps -> Bool
viewProvidersPresent fibers EmptyView = True
viewProvidersPresent fibers (ProviderView provider rest) =
  case lookupFiber provider fibers of
    Nothing => False
    Just fiber => stableProvider (fiberLifecycle fiber) &&
                  viewProvidersPresent fibers rest

||| Definition 58(3–4), strengthened with the key/provider-table connection
||| needed by reachable committed views. The extra connection is established by
||| L-Begin and preserved until guarded L-Unload.
public export
viewBindingsValid : DecEq name => DecEq key => (deps : List key) ->
  View name deps -> Registry name key value world error -> Bool
viewBindingsValid deps view fibers =
  viewProvidersPresent fibers view &&
  isJust (resolveCommittedValues deps view fibers)

public export
fiberViewValid : DecEq name => DecEq key =>
  (fiber : Fiber name key value world error) ->
  Registry name key value world error -> Bool
fiberViewValid (MkFiber component parent retired table lifecycle) fibers =
  case lifecycle of
    Inactive _ => True
    Reloading _ _ view =>
      viewBindingsValid (dependencies (componentDependencies component)) view fibers
    Active _ view =>
      viewBindingsValid (dependencies (componentDependencies component)) view fibers
    Unloading _ view _ =>
      viewBindingsValid (dependencies (componentDependencies component)) view fibers

public export
pairwiseProvisionDisjoint : DecEq key =>
  List (Binding name (FiberAt name key value world error)) -> Bool
pairwiseProvisionDisjoint [] = True
pairwiseProvisionDisjoint (Bind _ fiber :: rest) =
  provisionsDisjointFrom (componentProvisions (fiberComponent fiber)) rest &&
  pairwiseProvisionDisjoint rest

||| Definition 58, executable. Registry/table uniqueness and view totality are
||| intrinsic; the Boolean checks the remaining global obligations.
public export
wellFormed : DecEq name => DecEq key =>
  SystemState name key value world error -> Bool
wellFormed = registryWellFormed

public export
0 justInjective : Just left = Just right -> left = right
justInjective Refl = Refl

public export
0 nothingIsNotJust : Nothing = Just x -> Void
nothingIsNotJust Refl impossible

public export
0 checkedActionProjects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)
checkedActionProjects nameEq keyEq action before afterState tag equation
  with (applyAction @{nameEq} @{keyEq} action before) proof raw
  checkedActionProjects nameEq keyEq action before afterState tag equation | Nothing =
    void (nothingIsNotJust equation)
  checkedActionProjects nameEq keyEq action before afterState tag equation |
    Just (rawTag, rawAfter) with (registryWellFormed @{nameEq} @{keyEq} rawAfter)
    checkedActionProjects nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | False = void (nothingIsNotJust equation)
    checkedActionProjects nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | True =
        case justInjective equation of Refl => Refl

public export
0 checkedActionTargetValid :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
checkedActionTargetValid nameEq keyEq action before afterState tag equation
  with (applyAction @{nameEq} @{keyEq} action before)
  checkedActionTargetValid nameEq keyEq action before afterState tag equation | Nothing =
    void (nothingIsNotJust equation)
  checkedActionTargetValid nameEq keyEq action before afterState tag equation |
    Just (rawTag, rawAfter) with (registryWellFormed @{nameEq} @{keyEq} rawAfter) proof valid
    checkedActionTargetValid nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | False = void (nothingIsNotJust equation)
    checkedActionTargetValid nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | True =
        case justInjective equation of Refl => valid

public export
0 applyActionDeterministic : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (state : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action state = Just (leftTag, leftState) ->
  applyAction @{nameEq} @{keyEq} action state = Just (rightTag, rightState) ->
  (leftTag = rightTag, leftState = rightState)
applyActionDeterministic nameEq keyEq action state left right =
  case justInjective (trans (sym left) right) of Refl => (Refl, Refl)

public export
TransitionSourceValid : {before, afterState :
  SystemState name key value world error} -> Transition before afterState -> Type
TransitionSourceValid {before} (Fired nameEq keyEq action tag equation) =
  registryWellFormed @{nameEq} @{keyEq} before = True

public export
TransitionTargetValid : {before, afterState :
  SystemState name key value world error} -> Transition before afterState -> Type
TransitionTargetValid {afterState} (Fired nameEq keyEq action tag equation) =
  registryWellFormed @{nameEq} @{keyEq} afterState = True

||| The checked monitor's target-admission fact. This is useful operationally,
||| but is deliberately not named Theorem 59: it does not derive preservation
||| from the raw rule and source invariant.
public export
0 checkedTransitionTargetValid : (step : Transition before afterState) ->
  TransitionTargetValid step
checkedTransitionTargetValid (Fired nameEq keyEq action tag equation) =
  checkedActionTargetValid nameEq keyEq action _ _ tag equation

0 falseIsNotTrue : False = True -> Void
falseIsNotTrue Refl impossible

0 boolAndLeft : (left, right : Bool) -> left && right = True -> left = True
boolAndLeft False right valid = void (falseIsNotTrue valid)
boolAndLeft True right valid = Refl

0 boolAndRight : (left, right : Bool) -> left && right = True -> right = True
boolAndRight False right valid = void (falseIsNotTrue valid)
boolAndRight True False valid = void (falseIsNotTrue valid)
boolAndRight True True valid = Refl

0 setFreshAbsent : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (n : name) ->
  (fiber : Fiber name key value world error) ->
  (before : Registry name key value world error) ->
  (applied : CoeffectApplied before) ->
  setFresh @{nameEq} n fiber before = Just applied ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n before = Nothing
setFreshAbsent {key} {world} {error} {value} nameEq n fiber before applied success
  with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n before)
  setFreshAbsent {key} {world} {error} {value} nameEq n fiber before applied success | Just old =
    void (nothingIsNotJust success)
  setFreshAbsent {key} {world} {error} {value} nameEq n fiber before applied success | Nothing = Refl

0 setFreshAfter : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (n : name) ->
  (fiber : Fiber name key value world error) ->
  (before : Registry name key value world error) ->
  (applied : CoeffectApplied before) ->
  (success : setFresh @{nameEq} n fiber before = Just applied) ->
  coeffectAfter applied =
    insertBinding @{nameEq} n fiber before
      (setFreshAbsent {key = key} {value = value} {world = world} {error = error} nameEq n fiber before applied success)
setFreshAfter {key} {world} {error} {value} nameEq n fiber before applied success
  with (lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n before)
  setFreshAfter {key} {world} {error} {value} nameEq n fiber before applied success | Just old =
    void (nothingIsNotJust success)
  setFreshAfter {key} {world} {error} {value} nameEq n fiber before applied success | Nothing =
    case justInjective success of Refl => Refl

0 preservationOInsert :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (OInsert n parent component) before =
    Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationOInsert {name} {key} {world} {error} {value}
  nameEq keyEq n parent component (MkSystemState ambient fibers) afterState tag
  valid equation
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers)) proof premises
  preservationOInsert {name} {key} {world} {error} {value}
    nameEq keyEq n parent component (MkSystemState ambient fibers) afterState tag
    valid equation | False = void (nothingIsNotJust equation)
  preservationOInsert {name} {key} {world} {error} {value}
    nameEq keyEq n parent component (MkSystemState ambient fibers) afterState tag
    valid equation | True
    with (setFresh @{nameEq} n (freshFiber component parent) fibers) proof inserted
    preservationOInsert {name} {key} {world} {error} {value}
      nameEq keyEq n parent component (MkSystemState ambient fibers) afterState tag
      valid equation | True | Nothing = void (nothingIsNotJust equation)
    preservationOInsert {name} {key} {world} {error} {value}
      nameEq keyEq n parent component (MkSystemState ambient fibers) afterState tag
      valid equation | True | Just applied =
        case justInjective equation of
          Refl =>
            let parentValid = trans (sym (parentPresentIsInvariant nameEq parent fibers))
                  (boolAndLeft _ _ premises)
            in rewrite setFreshAfter nameEq n (freshFiber component parent)
                 fibers applied inserted in
              registryWellFormedInactiveInsert {name = name} {key = key}
                {world = world} {error = error} {value = value} nameEq keyEq n
                component parent ambient fibers
                (setFreshAbsent nameEq n (freshFiber component parent)
                  fibers applied inserted)
                parentValid (boolAndRight _ _ premises) valid

0 preservationORetire :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (ORetire n) before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationORetire {name} {key} {world} {error} {value}
  nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation
  with (lookupFiber @{nameEq} n fibers) proof found
  preservationORetire {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Nothing = void (nothingIsNotJust equation)
  preservationORetire {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just fiber = case justInjective equation of
      Refl => registryWellFormedRetire {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq ambient n
        fiber fibers found valid

0 notTrueMeansFalse : (value : Bool) -> not value = True -> value = False
notTrueMeansFalse False valid = Refl
notTrueMeansFalse True valid = void (falseIsNotTrue valid)

0 inactiveLifecycleWitness :
  (lifecycle : Lifecycle key value world error name deps provision) ->
  isInactive lifecycle = True ->
  (outcome : Maybe error ** lifecycle = Inactive outcome)
inactiveLifecycleWitness (Inactive outcome) valid = (outcome ** Refl)
inactiveLifecycleWitness (Reloading rest accumulator view) valid =
  void (falseIsNotTrue valid)
inactiveLifecycleWitness (Active accumulator view) valid =
  void (falseIsNotTrue valid)
inactiveLifecycleWitness (Unloading accumulator view outcome) valid =
  void (falseIsNotTrue valid)

0 preservationORemove :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (ORemove n) before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationORemove {name} {key} {world} {error} {value}
  nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation
  with (lookupFiber @{nameEq} n fibers) proof found
  preservationORemove {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Nothing = void (nothingIsNotJust equation)
  preservationORemove {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table lifecycle)
    with (retired && isInactive lifecycle && not (hasChild @{nameEq} n fibers))
      proof guards
    preservationORemove {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table lifecycle) | False =
        void (nothingIsNotJust equation)
    preservationORemove {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table lifecycle) | True =
        let tailValid = boolAndRight retired
              (isInactive lifecycle && not (hasChild @{nameEq} n fibers)) guards
            inactiveValid = boolAndLeft (isInactive lifecycle)
              (not (hasChild @{nameEq} n fibers)) tailValid
            childAbsent = notTrueMeansFalse (hasChild @{nameEq} n fibers)
              (boolAndRight (isInactive lifecycle)
                (not (hasChild @{nameEq} n fibers)) tailValid)
        in case inactiveLifecycleWitness lifecycle inactiveValid of
          (outcome ** Refl) => case justInjective equation of
            Refl => registryWellFormedInactiveDelete {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq keyEq
              ambient n component parent retired table outcome fibers found
              childAbsent valid

0 sourceViewsFromWellFormed :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (MkSystemState ambient fibers) = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers) fibers = True
sourceViewsFromWellFormed nameEq keyEq ambient fibers valid =
  andFourFourth
    (parentsInvariant @{nameEq} (registryFibers {value = value} {world = world} {error = error} fibers) fibers)
    (chainsInvariant @{nameEq} (S (length (registryFibers {value = value} {world = world} {error = error} fibers)))
      (registryFibers {value = value} {world = world} {error = error} fibers) fibers)
    (pairwiseProvisionInvariant @{keyEq} (registryFibers {value = value} {world = world} {error = error} fibers))
    (viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error} (registryFibers {value = value} {world = world} {error = error} fibers) fibers) valid

0 preservationLBegin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (LBegin n) before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationLBegin {name} {key} {world} {error} {value}
  nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation
  with (lookupFiber @{nameEq} n fibers) proof found
  preservationLBegin {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Nothing = void (nothingIsNotJust equation)
  preservationLBegin {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Inactive Nothing))
    with (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retired table (Inactive Nothing)) fibers)
      proof target
    preservationLBegin {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table (Inactive Nothing)) | Nothing =
        void (nothingIsNotJust equation)
    preservationLBegin {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table (Inactive Nothing)) | Just view =
        case justInjective equation of
          Refl =>
            let sourceSelected = targetFiberBindingsSound {name = name}
                  {key = key} {world = world} {error = error} {value = value}
                  nameEq keyEq (MkFiber component parent retired table (Inactive Nothing))
                  fibers view target
                targetSelected = viewBindingsUnstableRuntime {name = name}
                  {key = key} {world = world} {error = error} {value = value}
                  nameEq keyEq (dependencies (componentDependencies component))
                  view n (MkFiber component parent retired table (Inactive Nothing)) table
                  (Reloading (componentProgram component) id view) fibers found Refl sourceSelected
                sourceViews = sourceViewsFromWellFormed nameEq keyEq ambient fibers
                  valid
                targetViews = viewsInvariantUnstableRuntimeReplace {name = name}
                  {key = key} {world = world} {error = error} {value = value}
                  nameEq keyEq n
                  (MkFiber component parent retired table (Inactive Nothing)) table
                  (Reloading (componentProgram component) id view) fibers found Refl
                  targetSelected sourceViews
            in registryWellFormedRuntimeReplace {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq keyEq ambient
              n (MkFiber component parent retired table (Inactive Nothing)) table
              (Reloading (componentProgram component) id view) fibers found valid targetViews
  preservationLBegin {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Inactive (Just err))) =
      void (nothingIsNotJust equation)
  preservationLBegin {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Reloading rest accumulator view)) = void (nothingIsNotJust equation)
  preservationLBegin {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Active accumulator view)) =
      void (nothingIsNotJust equation)
  preservationLBegin {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) = void (nothingIsNotJust equation)

||| Paper Theorem 59, stated over the raw ten-rule evaluator. Unlike the checked
||| admission fact, this direction cannot hide a malformed endpoint.
||| TODO(proof): rule induction plus registry replacement/insertion/deletion
||| invariant lemmas. This remains the CP2 proof-bar gap after round 2.
public export
preservationTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
preservationTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True

||| Rule identity predicates used by episode boundaries.
public export
record BeginStep (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                 (before, afterState : SystemState name key value world error) where
  constructor MkBeginStep
  beginEquation : checkedApplyAction @{nameEq} @{keyEq} (LBegin n) before =
                  Just (LBeginTag, afterState)

public export
beginTransition : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {before, afterState : SystemState name key value world error} ->
  BeginStep nameEq keyEq n before afterState -> Transition before afterState
beginTransition {nameEq} {keyEq} {n} opening =
  Fired nameEq keyEq (LBegin n) LBeginTag (beginEquation opening)

public export
record UnloadStep (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                  (before, afterState : SystemState name key value world error) where
  constructor MkUnloadStep
  unloadEquation : checkedApplyAction @{nameEq} @{keyEq} (LUnload n) before =
                   Just (LUnloadTag, afterState)

public export
unloadTransition : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {before, afterState : SystemState name key value world error} ->
  UnloadStep nameEq keyEq n before afterState -> Transition before afterState
unloadTransition {nameEq} {keyEq} {n} closing =
  Fired nameEq keyEq (LUnload n) LUnloadTag (unloadEquation closing)

||| Every state in this trace segment, including both endpoints, is installed.
public export
data InstalledTrace : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (n : name) ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  InstalledEnd : installedAt @{nameEq} n state = True ->
    InstalledTrace name key world error value nameEq n (NoTransitions {state})
  InstalledStep : (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    installedAt @{nameEq} n first = True ->
    InstalledTrace name key world error value nameEq n rest ->
    InstalledTrace name key world error value nameEq n
      (MoreTransitions transition rest)

||| A prefix is anchored at the unique left boundary: the state immediately
||| after L-Begin. It cannot be manufactured from an Active/Unloading suffix.
public export
record EpisodePrefix (name, key, world, error : Type) (value : key -> Type)
                     (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                     (preStart, current : SystemState name key value world error) where
  constructor MkEpisodePrefix
  episodeStartState : SystemState name key value world error
  opening : BeginStep nameEq keyEq n preStart episodeStartState
  inside : Transitions episodeStartState current
  insideInstalled : InstalledTrace name key world error value nameEq n inside

||| A maximal closed episode has both boundaries: L-Begin on the left and the
||| first L-Unload on the right.
public export
record ClosedEpisode (name, key, world, error : Type) (value : key -> Type)
                     (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                     (preStart, afterClose : SystemState name key value world error) where
  constructor MkClosedEpisode
  closedStartState : SystemState name key value world error
  lastInstalledState : SystemState name key value world error
  closedOpening : BeginStep nameEq keyEq n preStart closedStartState
  closedInside : Transitions closedStartState lastInstalledState
  closedInsideInstalled : InstalledTrace name key world error value nameEq n closedInside
  closing : UnloadStep nameEq keyEq n lastInstalledState afterClose

public export
closedTransitions : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {pre, afterState : SystemState name key value world error} ->
  (episode : ClosedEpisode name key world error value nameEq keyEq n pre afterState) ->
  Transitions (closedStartState episode) afterState
closedTransitions episode = appendTransitions (closedInside episode)
  (MoreTransitions (unloadTransition (closing episode)) NoTransitions)

public export
prefixTransitions : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {pre, current : SystemState name key value world error} ->
  (episode : EpisodePrefix name key world error value nameEq keyEq n pre current) ->
  Transitions (episodeStartState episode) current
prefixTransitions episode = inside episode

||| Paper Definition-53 effect state: ambient state plus every named owned
||| table, with registry/control fields erased. Absent and empty tables are
||| intentionally observationally identical, as required by vestigial entries.
public export
record EffectState (name, key : Type) (value : key -> Type) (world : Type) where
  constructor MkEffectState
  effectAmbient : world
  effectTables : name -> CoeffectContext key value

public export
projectEffectState : DecEq name =>
  SystemState name key value world error -> EffectState name key value world
projectEffectState state = MkEffectState (worldState state) tableFor
  where
  tableFor : name -> CoeffectContext key value
  tableFor selected = case lookupFiber selected (registry state) of
    Nothing => emptyContext
    Just fiber => ownedValues (fiberTable fiber)

||| Exact effect-state agreement without function extensionality.
public export
record EffectStateRelated {name, key : Type} {value : key -> Type} {world : Type}
  (keyEq : DecEq key) (left, right : EffectState name key value world) where
  constructor MkEffectStateRelated
  0 ambientExact : effectAmbient left = effectAmbient right
  0 tablesExact : (selected : name) -> (k : key) ->
    lookupBinding k (effectTables left selected) =
    lookupBinding k (effectTables right selected)

0 effectStateReflexive : (keyEq : DecEq key) ->
  (state : EffectState name key value world) ->
  EffectStateRelated keyEq state state
effectStateReflexive keyEq state =
  MkEffectStateRelated Refl (\selected, k => Refl)

0 effectStateSymmetric : (keyEq : DecEq key) ->
  EffectStateRelated keyEq left right -> EffectStateRelated keyEq right left
effectStateSymmetric keyEq relation = MkEffectStateRelated
  (sym (ambientExact relation))
  (\selected, k => sym (tablesExact relation selected k))

0 effectStateTransitive : (keyEq : DecEq key) ->
  EffectStateRelated keyEq left middle -> EffectStateRelated keyEq middle right ->
  EffectStateRelated keyEq left right
effectStateTransitive keyEq first second = MkEffectStateRelated
  (trans (ambientExact first) (ambientExact second))
  (\selected, k => trans (tablesExact first selected k)
                         (tablesExact second selected k))

public export
EffectStateEquivalence : {name, key, world : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> Equivalence (EffectState name key value world)
EffectStateEquivalence {name} {key} {world} {value} keyEq =
  MkEquivalence (EffectStateRelated keyEq)
  (effectStateReflexive keyEq) (effectStateSymmetric keyEq)
  (effectStateTransitive keyEq)

record RestrictedEntries (key : Type) (value : key -> Type)
                         (allowed : List key) where
  constructor MkRestrictedEntries
  restrictedBindings : List (Binding key value)
  0 restrictedUnique : UniqueKeys (bindingKeys restrictedBindings)
  0 restrictedSound : (k : key) -> Elem k (bindingKeys restrictedBindings) ->
    Elem k allowed

restrictEntries : DecEq key => (allowed : List key) -> (0 unique : UniqueKeys allowed) ->
  CoeffectContext key value -> RestrictedEntries key value allowed
restrictEntries [] UniqueNil table = MkRestrictedEntries [] UniqueNil
  (\k, present => absurd present)
restrictEntries (k :: ks) (UniqueCons absent uniqueRest) table
  with (lookupBinding k table)
  restrictEntries (k :: ks) (UniqueCons absent uniqueRest) table | Nothing =
    let tail = restrictEntries ks uniqueRest table in
      MkRestrictedEntries (restrictedBindings tail) (restrictedUnique tail)
        (\present, occurs => There (restrictedSound tail present occurs))
  restrictEntries (k :: ks) (UniqueCons absent uniqueRest) table | Just v =
    let tail = restrictEntries ks uniqueRest table
        0 notInTail = \occurs => absent
          (restrictedSound tail k occurs) in
      MkRestrictedEntries (Bind k v :: restrictedBindings tail)
        (UniqueCons notInTail (restrictedUnique tail))
        (\present, occurs => case occurs of
          Here => Here
          There later => There (restrictedSound tail present later))

||| Reconstruct an owned table by restricting an arbitrary effect table to the
||| component's declared provision. This makes full-state maps executable while
||| preserving capability confinement intrinsically.
public export
restrictOwned : DecEq key => (provision : CoeffectSpec key) ->
  CoeffectContext key value -> OwnedTable key value provision
restrictOwned (MkCoeffectSpec allowed unique) table =
  let result = restrictEntries allowed unique table in
    MkOwnedTable
      (MkCoeffectContext (restrictedBindings result) (restrictedUnique result))
      (restrictedSound result)

public export
setEffectTable : DecEq name => name -> CoeffectContext key value ->
  EffectState name key value world -> EffectState name key value world
setEffectTable selected table state = MkEffectState (effectAmbient state) next
  where
  next : name -> CoeffectContext key value
  next candidate = case decEq candidate selected of
    Yes Refl => table
    No _ => effectTables state candidate

public export
setEffectAmbient : world -> EffectState name key value world ->
  EffectState name key value world
setEffectAmbient next state = MkEffectState next (effectTables state)

resolveEffectValues : DecEq key => (deps : List key) -> View name deps ->
  EffectState name key value world -> Maybe (DepValues key value deps)
resolveEffectValues [] EmptyView state = Just NoDepValues
resolveEffectValues (k :: ks) (ProviderView provider rest) state =
  case lookupBinding k (effectTables state provider) of
    Nothing => Nothing
    Just v => map (OneDepValue v) (resolveEffectValues ks rest state)

public export
PartialEffectMap : (name, key : Type) -> (value : key -> Type) ->
  (world : Type) -> Type
PartialEffectMap name key value world =
  EffectState name key value world -> Maybe (EffectState name key value world)

||| Full Table-1 effect map. Successful iterator maps and yielded accumulators
||| consume and produce both ambient state and the acting fiber's owned table.
||| Control-only edits are erased; O-Insert/O-Remove set the actor table empty.
public export
partialEffectMapFor : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  Action name key value world error -> RuleTag ->
  SystemState name key value world error -> PartialEffectMap name key value world
partialEffectMapFor nameEq keyEq (OInsert n parent component) tag origin state =
  Just (setEffectTable @{nameEq} n emptyContext state)
partialEffectMapFor nameEq keyEq (ORemove n) tag origin state =
  Just (setEffectTable @{nameEq} n emptyContext state)
partialEffectMapFor nameEq keyEq (LAdvance n) LRaiseTag origin state = Just state
partialEffectMapFor nameEq keyEq (LAdvance n) tag origin state = case tag of
  LIterTag => successfulAdvance
  LFinishTag => successfulAdvance
  LDivertTag => successfulAdvance
  _ => Just state
  where
  successfulAdvance : Maybe (EffectState name key value world)
  successfulAdvance = case lookupFiber @{nameEq} n (registry origin) of
    Nothing => Nothing
    Just fiber => case fiberLifecycle fiber of
      Reloading [] accumulator view => Just state
      Reloading (step :: rest) accumulator view =>
        case resolveEffectValues @{keyEq}
          (dependencies (componentDependencies (fiberComponent fiber))) view state of
          Nothing => Nothing
          Just capability =>
            let owned = restrictOwned @{keyEq}
                  (componentProvisions (fiberComponent fiber)) (effectTables state n) in
            case runStepEffect step capability
              (MkLocalState (effectAmbient state) owned) of
              Left _ => Nothing
              Right (after, undo) => Just
                (setEffectTable @{nameEq} n (ownedValues (localTable after))
                  (setEffectAmbient (localWorld after) state))
      _ => Nothing
partialEffectMapFor nameEq keyEq (LUnload n) tag origin state =
  case lookupFiber @{nameEq} n (registry origin) of
    Nothing => Nothing
    Just fiber => case fiberLifecycle fiber of
      Unloading accumulator view outcome =>
        let owned = restrictOwned @{keyEq}
              (componentProvisions (fiberComponent fiber)) (effectTables state n)
            restored = accumulator (MkLocalState (effectAmbient state) owned) in
          Just (setEffectTable @{nameEq} n (ownedValues (localTable restored))
            (setEffectAmbient (localWorld restored) state))
      _ => Nothing
partialEffectMapFor nameEq keyEq action tag origin state = Just state

public export
partialEffectMap : {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> PartialEffectMap name key value world
partialEffectMap {before} (Fired nameEq keyEq action tag equation) =
  partialEffectMapFor nameEq keyEq action tag before

||| Partial world projection retained only as an executable diagnostic. Recovery
||| hypotheses below use `partialEffectMap` exclusively.
||| Partial Table-1 state map. A moved successful iterator may fail, and that
||| remains `Nothing`; it is never silently totalized to identity.
public export
partialWorldMapFor : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  Action name key value world error -> RuleTag ->
  SystemState name key value world error -> PartialMap world
partialWorldMapFor nameEq keyEq (LAdvance n) LRaiseTag state currentWorld = Just currentWorld
partialWorldMapFor nameEq keyEq (LAdvance n) tag state currentWorld =
  case tag of
    LIterTag => successfulAdvance
    LFinishTag => successfulAdvance
    LDivertTag => successfulAdvance
    _ => Just currentWorld
  where
  successfulAdvance : Maybe world
  successfulAdvance = case lookupFiber @{nameEq} n (registry state) of
    Nothing => Nothing
    Just fiber => case fiberLifecycle fiber of
      Reloading [] accumulator view => Just currentWorld
      Reloading (step :: rest) accumulator view =>
        case resolveCommittedValues @{nameEq} @{keyEq}
          (dependencies (componentDependencies (fiberComponent fiber)))
          view (registry state) of
          Nothing => Nothing
          Just capability => case runStepEffect step capability
            (MkLocalState currentWorld (fiberTable fiber)) of
              Left _ => Nothing
              Right (after, undo) => Just (localWorld after)
      _ => Nothing
partialWorldMapFor nameEq keyEq (LUnload n) tag state world =
  case lookupFiber @{nameEq} n (registry state) of
    Just fiber => case fiberLifecycle fiber of
      Unloading accumulator view outcome =>
        Just (localWorld (accumulator (MkLocalState world (fiberTable fiber))))
      _ => Nothing
    Nothing => Nothing
partialWorldMapFor nameEq keyEq action tag state world = Just world

public export
partialWorldMap : {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> PartialMap world
partialWorldMap {before} (Fired nameEq keyEq action tag equation) =
  partialWorldMapFor nameEq keyEq action tag before

||| Occurrence proof selecting only transformations actually present in a trace.
public export
data OccursIn : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {stepBefore, stepAfter : SystemState name key value world error} ->
  Transition stepBefore stepAfter -> Transitions first last -> Type where
  OccursHere : OccursIn transition (MoreTransitions transition rest)
  OccursLater : OccursIn selected rest ->
    OccursIn selected (MoreTransitions transition rest)

||| Non-vacuous Definition-60 hypothesis over the complete effect state.
||| Every commutation and definedness premise observes ambient state and all
||| owned tables pointwise; no world-only projection exists in this interface.
public export
record TraceIndependent (name, key, world, error : Type)
                        (value : key -> Type) (keyEq : DecEq key)
                        {first, last : SystemState name key value world error}
                        (trace : Transitions first last) where
  constructor MkTraceIndependent
  0 actualMapsCommute :
    {leftBefore, leftAfter, rightBefore, rightAfter :
      SystemState name key value world error} ->
    (left : Transition leftBefore leftAfter) ->
    (right : Transition rightBefore rightAfter) ->
    OccursIn left trace -> OccursIn right trace ->
    Not (transitionActor left = transitionActor right) ->
    PartialCommute (EffectStateEquivalence keyEq)
      (partialEffectMap left) (partialEffectMap right)
  0 definednessStable :
    {leftBefore, leftAfter, rightBefore, rightAfter :
      SystemState name key value world error} ->
    (left : Transition leftBefore leftAfter) ->
    (right : Transition rightBefore rightAfter) ->
    OccursIn left trace -> OccursIn right trace ->
    Not (transitionActor left = transitionActor right) ->
    (origin, moved, result : EffectState name key value world) ->
    partialEffectMap right origin = Just moved ->
    partialEffectMap left origin = Just result ->
    (movedResult : EffectState name key value world **
      partialEffectMap left moved = Just movedResult)

public export
0 noOccurrenceInEmpty : OccursIn transition NoTransitions -> Void
noOccurrenceInEmpty occurrence impossible

||| Concrete non-vacuity witness for every full effect state.
public export
emptyTraceIndependent : (keyEq : DecEq key) ->
  TraceIndependent name key world error value keyEq (NoTransitions {state})
emptyTraceIndependent keyEq = MkTraceIndependent
  (\left, right, leftOccurs, rightOccurs, distinct =>
    void (noOccurrenceInEmpty leftOccurs))
  (\left, right, leftOccurs, rightOccurs, distinct, origin, moved, result,
    rightDefined, leftDefined => void (noOccurrenceInEmpty leftOccurs))

||| Full-effect replay skips the selected actor and propagates foreign failure.
||| Its zero-step case uses pointwise effect-state equality, avoiding function
||| extensionality while retaining every owned table.
public export
data ForeignReplay : (name, key, world, error : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) ->
  {start, end : SystemState name key value world error} ->
  (selected : name) -> Transitions start end ->
  EffectState name key value world -> EffectState name key value world -> Type where
  ReplayDone : EffectStateRelated keyEq initial final ->
    ForeignReplay name key world error value keyEq selected
      NoTransitions initial final
  ReplayOwn : (transition : Transition first middle) ->
    transitionActor transition = selected ->
    ForeignReplay name key world error value keyEq selected rest initial final ->
    ForeignReplay name key world error value keyEq selected
      (MoreTransitions transition rest) initial final
  ReplayForeign : (transition : Transition first middle) ->
    Not (transitionActor transition = selected) ->
    partialEffectMap transition initial = Just nextEffect ->
    ForeignReplay name key world error value keyEq selected rest nextEffect final ->
    ForeignReplay name key world error value keyEq selected
      (MoreTransitions transition rest) initial final

||| A dependent package for the accumulator actually stored in an installed
||| fiber. The provision index determines which table slice it may transform.
public export
data AccumulatorHandle : (key : Type) -> (value : key -> Type) ->
  (world : Type) -> Type where
  MkAccumulatorHandle : (provision : CoeffectSpec key) ->
    OwnedTable key value provision ->
    (LocalState key value world provision ->
     LocalState key value world provision) ->
    AccumulatorHandle key value world

public export
actualAccumulatorAt : DecEq name => name ->
  SystemState name key value world error -> Maybe (AccumulatorHandle key value world)
actualAccumulatorAt selected state = case lookupFiber selected (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Inactive _ => Nothing
    Reloading _ accumulator _ => Just (MkAccumulatorHandle
      (componentProvisions (fiberComponent fiber)) (fiberTable fiber) accumulator)
    Active accumulator _ => Just (MkAccumulatorHandle
      (componentProvisions (fiberComponent fiber)) (fiberTable fiber) accumulator)
    Unloading accumulator _ _ => Just (MkAccumulatorHandle
      (componentProvisions (fiberComponent fiber)) (fiberTable fiber) accumulator)

||| Lift the actual accumulator to the same complete effect state used by
||| independence and replay. The input table is reconstructed from that state,
||| so off-origin table corruption is visible to the commutation premise.
public export
accumulatorEffectMap : (nameEq : DecEq name) -> (keyEq : DecEq key) -> name ->
  AccumulatorHandle key value world -> PartialEffectMap name key value world
accumulatorEffectMap nameEq keyEq selected
  (MkAccumulatorHandle provision captured accumulator) state =
    let owned = restrictOwned @{keyEq} provision (effectTables state selected)
        restored = accumulator (MkLocalState (effectAmbient state) owned) in
      Just (setEffectTable @{nameEq} selected (ownedValues (localTable restored))
        (setEffectAmbient (localWorld restored) state))

||| A trace-specific full-effect accumulator/foreign-map hypothesis.
public export
record PrefixRecoveryIndependent
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {start, current : SystemState name key value world error}
  (trace : Transitions start current)
  (accumulator : PartialEffectMap name key value world) where
  constructor MkPrefixRecoveryIndependent
  0 accumulatorCommutes :
    {before, afterState : SystemState name key value world error} ->
    (foreign : Transition before afterState) ->
    OccursIn foreign trace ->
    Not (transitionActor foreign = selected) ->
    PartialCommute (EffectStateEquivalence keyEq) accumulator
      (partialEffectMap foreign)

||| Theorem 61. Premises and conclusion now range over exactly the same full
||| effect state (ambient plus every owned table).
||| TODO(proof): temporal induction over InstalledTrace and actual accumulators.
public export
recoveryExactnessTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
recoveryExactnessTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, current : SystemState name key value world error) ->
  (episode : EpisodePrefix name key world error value nameEq keyEq n pre current) ->
  (handle : AccumulatorHandle key value world) ->
  actualAccumulatorAt @{nameEq} n current = Just handle ->
  PrefixRecoveryIndependent name key world error value nameEq keyEq n
    (prefixTransitions episode) (accumulatorEffectMap nameEq keyEq n handle) ->
  (restored : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq n handle (projectEffectState @{nameEq} current) =
    Just restored ->
  ForeignReplay name key world error value keyEq n (prefixTransitions episode)
    (projectEffectState @{nameEq} (episodeStartState episode)) restored

||| Corollary 62, as one full-effect replay equation rather than a world replay
||| plus disconnected table fields.
||| TODO(proof): Theorem 61 at lastInstalledState followed by L-Unload.
public export
terminalRecoveryTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
terminalRecoveryTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, afterState : SystemState name key value world error) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq n pre afterState) ->
  TraceIndependent name key world error value keyEq (closedTransitions episode) ->
  ForeignReplay name key world error value keyEq n (closedTransitions episode)
    (projectEffectState @{nameEq} (closedStartState episode))
    (projectEffectState @{nameEq} afterState)

||| Equation 58's exact L-Begin premise, isolated as a tractable theorem.
public export
BeginSatisfied : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> SystemState name key value world error -> Type
BeginSatisfied {name} {key} {world} {error} {value} nameEq keyEq n state =
  isJust (targetAt @{nameEq} @{keyEq} n state) = True

0 beginSatisfiedFromEquation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LBegin n) before =
    Just (LBeginTag, afterState) ->
  BeginSatisfied nameEq keyEq n before
beginSatisfiedFromEquation nameEq keyEq n before afterState equation
  with (lookupFiber @{nameEq} n (registry before)) proof found
  beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Nothing =
    void (nothingIsNotJust equation)
  beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
    with (fiberLifecycle fiber)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Inactive Nothing with (targetFiber @{nameEq} @{keyEq} fiber (registry before)) proof target
      beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Inactive Nothing | Nothing = void (nothingIsNotJust equation)
      beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Inactive Nothing | Just view = Refl
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Inactive (Just err) = void (nothingIsNotJust equation)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Reloading remaining accumulator view = void (nothingIsNotJust equation)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Active accumulator view = void (nothingIsNotJust equation)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Unloading accumulator view outcome = void (nothingIsNotJust equation)

||| Equation 58 is proved directly from the L-Begin evaluator equation.
public export
0 beginSatisfactionTheorem :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (before, afterState : SystemState name key value world error) ->
  BeginStep nameEq keyEq n before afterState ->
  BeginSatisfied nameEq keyEq n before
beginSatisfactionTheorem nameEq keyEq n before afterState opening =
  beginSatisfiedFromEquation nameEq keyEq n before afterState
    (checkedActionProjects nameEq keyEq (LBegin n) before afterState LBeginTag
      (beginEquation opening))

public export
activeEndpoint : DecEq name => name -> SystemState name key value world error -> Bool
activeEndpoint selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => isActive (fiberLifecycle fiber)

public export
reloadingEndpoint : DecEq name => name -> SystemState name key value world error -> Bool
reloadingEndpoint selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => case fiberLifecycle fiber of
    Reloading _ _ _ => True
    _ => False

public export
unloadingEndpoint : DecEq name => name -> SystemState name key value world error -> Bool
unloadingEndpoint selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => case fiberLifecycle fiber of
    Unloading _ _ _ => True
    _ => False

0 lookupReplacedFiber : DecEq name => (selected : name) ->
  (old, next : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  lookupFiber selected fibers = Just old ->
  lookupFiber selected (replaceBinding selected next fibers) = Just next
lookupReplacedFiber selected old next (MkCoeffectContext entries unique) found =
  lookupReplaceEntries selected old next entries found

0 activeAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name =>
  {fibers : Registry name key value world error} -> {worldValue : world} ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  {table : OwnedTable key value (componentProvisions (fiberComponent fiber))} ->
  {accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name (dependencies
    (componentDependencies (fiberComponent fiber)))} ->
  lookupFiber selected fibers = Just fiber ->
  activeEndpoint {key = key} {value = value} {world = world} {error = error} selected
    (MkSystemState worldValue
      (replaceBinding selected
        (setFiberRuntime fiber table (Active accumulator view)) fibers)) = True
activeAfterReplace {table} {accumulator} {view} selected
  fiber@(MkFiber component parent retired oldTable oldLife) found =
  rewrite lookupReplacedFiber selected fiber
    (setFiberRuntime fiber table (Active accumulator view)) fibers found in Refl

0 reloadingAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name =>
  {fibers : Registry name key value world error} -> {worldValue : world} ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  {table : OwnedTable key value (componentProvisions (fiberComponent fiber))} ->
  {remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))} ->
  {accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name (dependencies
    (componentDependencies (fiberComponent fiber)))} ->
  lookupFiber selected fibers = Just fiber ->
  reloadingEndpoint {key = key} {value = value} {world = world} {error = error} selected
    (MkSystemState worldValue
      (replaceBinding selected
        (setFiberRuntime fiber table (Reloading remaining accumulator view)) fibers)) = True
reloadingAfterReplace {table} {remaining} {accumulator} {view} selected
  fiber@(MkFiber component parent retired oldTable oldLife) found =
  rewrite lookupReplacedFiber selected fiber
    (setFiberRuntime fiber table (Reloading remaining accumulator view)) fibers found in Refl

0 unloadingAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name =>
  {fibers : Registry name key value world error} -> {worldValue : world} ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  {table : OwnedTable key value (componentProvisions (fiberComponent fiber))} ->
  {accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name (dependencies
    (componentDependencies (fiberComponent fiber)))} -> {outcome : Maybe error} ->
  lookupFiber selected fibers = Just fiber ->
  unloadingEndpoint {key = key} {value = value} {world = world} {error = error} selected
    (MkSystemState worldValue
      (replaceBinding selected
        (setFiberRuntime fiber table (Unloading accumulator view outcome)) fibers)) = True
unloadingAfterReplace {table} {accumulator} {view} {outcome} selected
  fiber@(MkFiber component parent retired oldTable oldLife) found =
  rewrite lookupReplacedFiber selected fiber
    (setFiberRuntime fiber table (Unloading accumulator view outcome)) fibers found in Refl

||| Structural result for one successful LAdvance. Iter/Finish constructors
||| expose Equation 59; Divert/Raise are the only exits.
public export
data AdvanceStructure : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) -> Type where
  IterAdvance : (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry before) = Just fiber ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) **
     (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
        LocalState key value world (componentProvisions (fiberComponent fiber)) **
      (view : View name
        (dependencies (componentDependencies (fiberComponent fiber))) **
       (fiberLifecycle fiber = Reloading remaining accumulator view,
        targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view = True)))) ->
    reloadingEndpoint @{nameEq} selected afterState = True ->
    AdvanceStructure name key world error value nameEq keyEq selected LIterTag
      before afterState
  FinishAdvance : (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry before) = Just fiber ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) **
     (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
        LocalState key value world (componentProvisions (fiberComponent fiber)) **
      (view : View name
        (dependencies (componentDependencies (fiberComponent fiber))) **
       (fiberLifecycle fiber = Reloading remaining accumulator view,
        targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view = True)))) ->
    activeEndpoint @{nameEq} selected afterState = True ->
    AdvanceStructure name key world error value nameEq keyEq selected LFinishTag
      before afterState
  DivertAdvance : unloadingEndpoint @{nameEq} selected afterState = True ->
    AdvanceStructure name key world error value nameEq keyEq
      selected LDivertTag before afterState
  RaiseAdvance : unloadingEndpoint @{nameEq} selected afterState = True ->
    AdvanceStructure name key world error value nameEq keyEq
      selected LRaiseTag before afterState

0 advanceStructureFromEquation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance n) before = Just (tag, afterState) ->
  AdvanceStructure name key world error value nameEq keyEq n tag before afterState
advanceStructureFromEquation nameEq keyEq n before afterState tag equation
  with (lookupFiber @{nameEq} n (registry before)) proof found
  advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Nothing =
    void (nothingIsNotJust equation)
  advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
    with (fiberLifecycle fiber) proof life
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Inactive outcome = void (nothingIsNotJust equation)
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Active accumulator view = void (nothingIsNotJust equation)
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Unloading accumulator view outcome = void (nothingIsNotJust equation)
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Reloading [] accumulator view
        with (targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view) proof matches
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading [] accumulator view | True =
          case justInjective equation of
            Refl => FinishAdvance fiber found
              ([] ** (accumulator ** (view ** (life, matches))))
              (activeAfterReplace n fiber found)
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading [] accumulator view | False =
          case justInjective equation of
            Refl => DivertAdvance (unloadingAfterReplace n fiber found)
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Reloading (step :: rest) accumulator view
        with (resolveCommittedValues @{nameEq} @{keyEq}
          (dependencies (componentDependencies (fiberComponent fiber)))
          view (registry before))
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading (step :: rest) accumulator view | Nothing =
          void (nothingIsNotJust equation)
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading (step :: rest) accumulator view | Just capability
          with (runStepEffect step capability
            (MkLocalState (worldState before) (fiberTable fiber)))
        advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
          | Reloading (step :: rest) accumulator view | Just capability | Left err =
            case justInjective equation of
              Refl => RaiseAdvance (unloadingAfterReplace n fiber found)
        advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
          | Reloading (step :: rest) accumulator view | Just capability |
            Right (localAfter, undo)
            with (targetMatches @{nameEq}
              (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view) proof matches
          advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
            | Reloading (step :: rest) accumulator view | Just capability |
              Right (localAfter, undo) | False =
                case justInjective equation of
                  Refl => DivertAdvance (unloadingAfterReplace n fiber found)
          advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
            | Reloading (step :: []) accumulator view | Just capability |
              Right (localAfter, undo) | True =
                case justInjective equation of
                  Refl => FinishAdvance fiber found
                    ((step :: []) ** (accumulator **
                      (view ** (life, matches))))
                    (activeAfterReplace n fiber found)
          advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
            | Reloading (step :: next :: more) accumulator view | Just capability |
              Right (localAfter, undo) | True =
                case justInjective equation of
                  Refl => IterAdvance fiber found
                    ((step :: next :: more) ** (accumulator **
                      (view ** (life, matches))))
                    (reloadingAfterReplace n fiber found)

||| Proven structural Equation-59/exit lemma for every successful LAdvance.
public export
0 advanceStructureTheorem :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance n) before = Just (tag, afterState) ->
  AdvanceStructure name key world error value nameEq keyEq n tag before afterState
advanceStructureTheorem = advanceStructureFromEquation

||| Structural shape of the separate aborting L-Divert rule.
public export
record AbortDivertStructure
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (before, afterState : SystemState name key value world error) where
  constructor MkAbortDivertStructure
  divertFiber : Fiber name key value world error
  divertLookup : lookupFiber @{nameEq} selected (registry before) = Just divertFiber
  divertRemaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent divertFiber)))
    (componentProvisions (fiberComponent divertFiber)))
  divertAccumulator : LocalState key value world
      (componentProvisions (fiberComponent divertFiber)) ->
    LocalState key value world (componentProvisions (fiberComponent divertFiber))
  divertView : View name (dependencies
    (componentDependencies (fiberComponent divertFiber)))
  divertReloading : fiberLifecycle divertFiber =
    Reloading divertRemaining divertAccumulator divertView
  targetChanged : targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} divertFiber (registry before)) divertView = False
  divertUnloading : unloadingEndpoint @{nameEq} selected afterState = True

0 abortDivertFromEquation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LDivert n) before =
    Just (LDivertTag, afterState) ->
  AbortDivertStructure name key world error value nameEq keyEq n before afterState
abortDivertFromEquation nameEq keyEq n before afterState equation
  with (lookupFiber @{nameEq} n (registry before)) proof found
  abortDivertFromEquation nameEq keyEq n before afterState equation | Nothing =
    void (nothingIsNotJust equation)
  abortDivertFromEquation nameEq keyEq n before afterState equation | Just fiber
    with (fiberLifecycle fiber) proof life
    abortDivertFromEquation nameEq keyEq n before afterState equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    abortDivertFromEquation nameEq keyEq n before afterState equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    abortDivertFromEquation nameEq keyEq n before afterState equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
    abortDivertFromEquation nameEq keyEq n before afterState equation | Just fiber |
      Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view) proof matches
      abortDivertFromEquation nameEq keyEq n before afterState equation | Just fiber |
        Reloading remaining accumulator view | True = void (nothingIsNotJust equation)
      abortDivertFromEquation nameEq keyEq n before afterState equation | Just fiber |
        Reloading remaining accumulator view | False =
          case justInjective equation of
            Refl => MkAbortDivertStructure fiber found remaining accumulator view
              life matches (unloadingAfterReplace n fiber found)

public export
0 abortDivertStructureTheorem :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LDivert n) before =
    Just (LDivertTag, afterState) ->
  AbortDivertStructure name key world error value nameEq keyEq n before afterState
abortDivertStructureTheorem = abortDivertFromEquation

0 unloadGuardFromEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LUnload n) before =
    Just (LUnloadTag, afterState) ->
  relied @{nameEq} {key = key} {value = value} {world = world} {error = error} n (registry before) = False
unloadGuardFromEquation nameEq keyEq n before afterState equation
  with (lookupFiber @{nameEq} n (registry before))
  unloadGuardFromEquation nameEq keyEq n before afterState equation | Nothing =
    void (nothingIsNotJust equation)
  unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
    with (fiberLifecycle fiber)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Inactive outcome = void (nothingIsNotJust equation)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Reloading remaining accumulator view = void (nothingIsNotJust equation)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Active accumulator view = void (nothingIsNotJust equation)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Unloading accumulator view outcome
        with (relied @{nameEq} {key = key} {value = value} {world = world} {error = error} n (registry before))
      unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Unloading accumulator view outcome | True =
          void (nothingIsNotJust equation)
      unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Unloading accumulator view outcome | False = Refl

||| Proven local ordering guard: a provider cannot L-Unload while any installed
||| committed view still resolves to it.
public export
0 unloadGuardTheorem :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  UnloadStep nameEq keyEq n before afterState ->
  relied @{nameEq} {key = key} {value = value} {world = world} {error = error} n (registry before) = False
unloadGuardTheorem nameEq keyEq n before afterState closing =
  unloadGuardFromEquation nameEq keyEq n before afterState
    (checkedActionProjects nameEq keyEq (LUnload n) before afterState LUnloadTag
      (unloadEquation closing))

||| A nonempty path represents a strict time inequality.
public export
data StrictTransitions : SystemState name key value world error ->
                         SystemState name key value world error -> Type where
  OneOrMore : Transition first middle -> Transitions middle finalState ->
              StrictTransitions first finalState

public export
strictToTransitions : StrictTransitions first finalState ->
  Transitions first finalState
strictToTransitions (OneOrMore step rest) = MoreTransitions step rest

||| Locate a closed episode in one global trace, including its opening boundary.
public export
record LocatedClosedEpisode
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
  {initial, final : SystemState name key value world error}
  (global : Transitions initial final) where
  constructor MkLocatedClosedEpisode
  locatedPreStart : SystemState name key value world error
  locatedAfter : SystemState name key value world error
  traceBeforeOpening : Transitions initial locatedPreStart
  locatedEpisode : ClosedEpisode name key world error value nameEq keyEq n
    locatedPreStart locatedAfter
  traceAfterClosing : Transitions locatedAfter final
  0 locatedDecomposition :
    appendTransitions traceBeforeOpening
      (MoreTransitions (beginTransition (closedOpening locatedEpisode))
        (appendTransitions (closedTransitions locatedEpisode) traceAfterClosing)) = global

public export
prefixThroughOpening :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {initial, final : SystemState name key value world error} ->
  {global : Transitions initial final} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq n global) ->
  Transitions initial (closedStartState (locatedEpisode located))
prefixThroughOpening located = appendTransitions (traceBeforeOpening located)
  (MoreTransitions (beginTransition (closedOpening (locatedEpisode located))) NoTransitions)

public export
prefixThroughClose :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {initial, final : SystemState name key value world error} ->
  {global : Transitions initial final} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq n global) ->
  Transitions initial (locatedAfter located)
prefixThroughClose located = appendTransitions (prefixThroughOpening located)
  (closedTransitions (locatedEpisode located))

||| The selected provider episode is tied to the consumer by prefix equations,
||| so an unrelated earlier/later provider episode cannot be supplied.
public export
record ProviderContainsConsumer
  (providerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq provider global)
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq consumer global) where
  constructor MkProviderContainsConsumer
  providerToConsumer : StrictTransitions
    (closedStartState (locatedEpisode providerEpisode))
    (closedStartState (locatedEpisode consumerEpisode))
  consumerToProviderClose : StrictTransitions
    (locatedAfter consumerEpisode) (locatedAfter providerEpisode)
  0 openingOrderInGlobal :
    prefixThroughOpening consumerEpisode =
      appendTransitions (prefixThroughOpening providerEpisode)
        (strictToTransitions providerToConsumer)
  0 closingOrderInGlobal :
    prefixThroughClose providerEpisode =
      appendTransitions (prefixThroughClose consumerEpisode)
        (strictToTransitions consumerToProviderClose)

||| Proven elimination of the same-global-trace containment witness into the two
||| strict ordering paths b < b' and u' < u.
public export
0 providerOrderingProof :
  (containment : ProviderContainsConsumer providerEpisode consumerEpisode) ->
  (StrictTransitions
     (closedStartState (locatedEpisode providerEpisode))
     (closedStartState (locatedEpisode consumerEpisode)),
   StrictTransitions (locatedAfter consumerEpisode) (locatedAfter providerEpisode))
providerOrderingProof containment =
  (providerToConsumer containment, consumerToProviderClose containment)

public export
resolvedProviderAt : DecEq name => DecEq key => name -> key -> name ->
  SystemState name key value world error -> Bool
resolvedProviderAt consumer k provider state =
  case lookupFiber consumer (registry state) of
    Nothing => False
    Just fiber => case committed (fiberLifecycle fiber) of
      Nothing => False
      Just view => case viewLookup k
        (dependencies (componentDependencies (fiberComponent fiber))) view of
          Nothing => False
          Just actual => case decEq actual provider of
            Yes Refl => True
            No _ => False

0 falseNotTrue : False = True -> Void
falseNotTrue Refl impossible

||| Proven local provider-ordering conclusion. The paper's relied predicate is
||| exactly the certificate that an installed consumer still commits to this
||| provider; while it is true the provider's closing L-Unload cannot exist.
public export
0 reliedProviderCannotUnload :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (before, afterState :
    SystemState name key value world error) ->
  relied @{nameEq} {key = key} {value = value} {world = world} {error = error}
    provider (registry before) = True ->
  UnloadStep nameEq keyEq provider before afterState -> Void
reliedProviderCannotUnload nameEq keyEq provider before afterState reliedTrue closing =
  falseNotTrue (trans (sym (unloadGuardTheorem nameEq keyEq provider before
    afterState closing)) reliedTrue)

public export
data ConsumerResolutionConstant : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> key -> name -> {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ResolutionConstantEnd :
    resolvedProviderAt @{nameEq} @{keyEq} consumer k provider state = True ->
    ConsumerResolutionConstant name key world error value nameEq keyEq
      consumer k provider (NoTransitions {state})
  ResolutionConstantStep :
    (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    resolvedProviderAt @{nameEq} @{keyEq} consumer k provider first = True ->
    ConsumerResolutionConstant name key world error value nameEq keyEq
      consumer k provider rest ->
    ConsumerResolutionConstant name key world error value nameEq keyEq
      consumer k provider (MoreTransitions transition rest)

public export
providerValueAt : DecEq name => DecEq key => name -> (k : key) ->
  SystemState name key value world error -> Maybe (value k)
providerValueAt provider k state = valueFromProvider provider k (registry state)

public export
data ProviderValueConstant : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> (k : key) -> value k ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ValueConstantEnd : providerValueAt @{nameEq} @{keyEq} provider k state = Just v ->
    ProviderValueConstant name key world error value nameEq keyEq
      provider k v (NoTransitions {state})
  ValueConstantStep :
    (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    providerValueAt @{nameEq} @{keyEq} provider k first = Just v ->
    ProviderValueConstant name key world error value nameEq keyEq provider k v rest ->
    ProviderValueConstant name key world error value nameEq keyEq provider k v
      (MoreTransitions transition rest)

public export
record OrderingResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (provider, consumer : name)
  {initial, final : SystemState name key value world error}
  (global : Transitions initial final)
  (providerEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq provider global)
  (consumerEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq consumer global)
  (k : key) where
  constructor MkOrderingResult
  distinctFibers : Not (provider = consumer)
  containment : ProviderContainsConsumer providerEpisode consumerEpisode
  consumerResolution : ConsumerResolutionConstant name key world error value
    nameEq keyEq consumer k provider
    (closedInside (locatedEpisode consumerEpisode))
  providedValue : value k
  providerValueStable : ProviderValueConstant name key world error value
    nameEq keyEq provider k providedValue
    (closedInside (locatedEpisode consumerEpisode))

||| Theorem 63 selects (rather than accepts) the containing provider episode.
||| TODO(proof): global-trace induction using L-Begin and the relied L-Unload guard.
public export
orderingTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
orderingTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, final : SystemState name key value world error) ->
  (global : Transitions initial final) ->
  wellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  (consumer, provider : name) -> (k : key) ->
  installedAt @{nameEq} provider final = False ->
  (consumerEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq consumer global) ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer k provider
    (closedStartState (locatedEpisode consumerEpisode)) = True ->
  (providerEpisode : LocatedClosedEpisode name key world error value
      nameEq keyEq provider global **
    OrderingResult name key world error value nameEq keyEq provider consumer
      global providerEpisode consumerEpisode k)

||| Executable Equation-59 check for the selected fiber.
public export
transitionResolutionCoherent : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Bool
transitionResolutionCoherent nameEq keyEq selected {before}
  (Fired firedNameEq firedKeyEq action tag equation) = case action of
    LAdvance actor => case decEq @{nameEq} actor selected of
      No _ => True
      Yes Refl => case tag of
        LIterTag => currentTarget
        LFinishTag => currentTarget
        _ => True
    _ => True
  where
  currentTarget : Bool
  currentTarget = case lookupFiber @{nameEq} selected (registry before) of
    Nothing => False
    Just fiber => case fiberLifecycle fiber of
      Reloading remaining accumulator view =>
        targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view
      _ => False

public export
data ResolutionCoherent : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  CoherentEnd : ResolutionCoherent name key world error value nameEq keyEq
    selected NoTransitions
  CoherentStep : (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionResolutionCoherent nameEq keyEq selected transition = True ->
    ResolutionCoherent name key world error value nameEq keyEq selected rest ->
    ResolutionCoherent name key world error value nameEq keyEq selected
      (MoreTransitions transition rest)

public export
reloadingAt : DecEq name => name -> SystemState name key value world error -> Bool
reloadingAt selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => case fiberLifecycle fiber of
    Reloading _ _ _ => True
    _ => False

public export
data ReloadingThroughout : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> name ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ReloadingEnd : (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry state) = Just fiber ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) **
     (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
        LocalState key value world
          (componentProvisions (fiberComponent fiber)) **
      (view : View name
        (dependencies (componentDependencies (fiberComponent fiber))) **
       fiberLifecycle fiber = Reloading remaining accumulator view))) ->
    ReloadingThroughout name key world error value nameEq selected
      (NoTransitions {state})
  ReloadingStep : (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    reloadingAt @{nameEq} selected first = True ->
    ReloadingThroughout name key world error value nameEq selected rest ->
    ReloadingThroughout name key world error value nameEq selected
      (MoreTransitions transition rest)

public export
committedProvidersAt : DecEq name => name ->
  SystemState name key value world error -> Maybe (List name)
committedProvidersAt selected state = case lookupFiber selected (registry state) of
  Nothing => Nothing
  Just fiber => map viewProviders (committed (fiberLifecycle fiber))

public export
activeAt : DecEq name => name -> SystemState name key value world error -> Bool
activeAt selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => isActive (fiberLifecycle fiber)

public export
unloadingAt : DecEq name => name -> SystemState name key value world error -> Bool
unloadingAt selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => case fiberLifecycle fiber of
    Unloading _ _ _ => True
    _ => False

public export
data CommittedProvidersConstant : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> name -> List name ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  CommittedProvidersEnd :
    committedProvidersAt @{nameEq} selected state = Just providers ->
    CommittedProvidersConstant name key world error value nameEq selected providers
      (NoTransitions {state})
  CommittedProvidersStep :
    (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    committedProvidersAt @{nameEq} selected first = Just providers ->
    CommittedProvidersConstant name key world error value nameEq selected providers rest ->
    CommittedProvidersConstant name key world error value nameEq selected providers
      (MoreTransitions transition rest)

public export
data StructuralExit : (name, key, world, error : Type) ->
  (value : key -> Type) ->
  {before, afterState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> name -> List name ->
  Transition before afterState -> Type where
  Finishes : transitionAction transition = LAdvance selected ->
    transitionTag transition = LFinishTag ->
    activeAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    committedProvidersAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = Just providers ->
    StructuralExit name key world error value nameEq selected providers transition
  DivertsBefore : transitionAction transition = LDivert selected ->
    transitionTag transition = LDivertTag ->
    unloadingAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    StructuralExit name key world error value nameEq selected providers transition
  DivertsAfter : transitionAction transition = LAdvance selected ->
    transitionTag transition = LDivertTag ->
    unloadingAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    StructuralExit name key world error value nameEq selected providers transition
  Raises : transitionAction transition = LAdvance selected ->
    transitionTag transition = LRaiseTag ->
    unloadingAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    StructuralExit name key world error value nameEq selected providers transition

||| Structural part of Theorem 64, covering open final episodes by `StillReloading`.
public export
data ResolutionStructure : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (openingProviders : List name) ->
  {start, current : SystemState name key value world error} ->
  Transitions start current -> Type where
  StillReloading : ReloadingThroughout name key world error value nameEq selected trace ->
    ResolutionCoherent name key world error value nameEq keyEq selected trace ->
    CommittedProvidersConstant name key world error value nameEq selected
      openingProviders trace ->
    ResolutionStructure name key world error value nameEq keyEq selected
      openingProviders trace
  ExitedReloading :
    (exitBefore, exitAfter : SystemState name key value world error) ->
    (initialPart : Transitions start exitBefore) ->
    (exitStep : Transition exitBefore exitAfter) ->
    (remainingPart : Transitions exitAfter current) ->
    appendTransitions initialPart (MoreTransitions exitStep remainingPart) = trace ->
    ReloadingThroughout name key world error value nameEq selected initialPart ->
    ResolutionCoherent name key world error value nameEq keyEq selected initialPart ->
    CommittedProvidersConstant name key world error value nameEq selected
      openingProviders trace ->
    StructuralExit name key world error value nameEq selected openingProviders exitStep ->
    ResolutionStructure name key world error value nameEq keyEq selected
      openingProviders trace

||| Structural Equation-59/exit theorem. Its input is anchored at L-Begin, so an
||| arbitrary Unloading suffix is unrepresentable.
||| TODO(proof): induction over the anchored InstalledTrace.
public export
resolutionStructureTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
resolutionStructureTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, current : SystemState name key value world error) ->
  (episode : EpisodePrefix name key world error value nameEq keyEq n pre current) ->
  (openingProviders : List name **
    (committedProvidersAt @{nameEq} n (episodeStartState episode) =
       Just openingProviders,
     ResolutionStructure name key world error value nameEq keyEq n
       openingProviders (prefixTransitions episode)))

||| Full Theorem 64 recovery branch over a maximal closed episode. Structural
||| coherence is separated so it can be proved without assuming temporal recovery.
||| TODO(proof): combine resolutionStructureTheorem with terminalRecoveryTheorem.
public export
resolutionCoherenceTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
resolutionCoherenceTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, afterState : SystemState name key value world error) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq n pre afterState) ->
  TraceIndependent name key world error value keyEq (closedTransitions episode) ->
  (openingProviders : List name **
    (committedProvidersAt @{nameEq} n (closedStartState episode) =
       Just openingProviders,
     ResolutionStructure name key world error value nameEq keyEq n
       openingProviders (closedInside episode),
     ForeignReplay name key world error value keyEq n (closedTransitions episode)
       (projectEffectState @{nameEq} (closedStartState episode))
       (projectEffectState @{nameEq} afterState)))
