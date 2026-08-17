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

public export
0 boolAndLeft : (left, right : Bool) -> left && right = True -> left = True
boolAndLeft False right valid = void (falseIsNotTrue valid)
boolAndLeft True right valid = Refl

public export
0 boolAndRight : (left, right : Bool) -> left && right = True -> right = True
boolAndRight False right valid = void (falseIsNotTrue valid)
boolAndRight True False valid = void (falseIsNotTrue valid)
boolAndRight True True valid = Refl

public export
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

public export
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

public export
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

public export
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

||| Public projection of the committed-view conjunct of registry well-formedness.
public export
0 wellFormedViewsInvariant :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error} (MkSystemState ambient fibers) = True ->
  viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
    {error = error}
    (registryFibers {value = value} {world = world} {error = error} fibers)
    fibers = True
wellFormedViewsInvariant {name} {key} {world} {error} {value}
  nameEq keyEq ambient fibers valid =
    andFourFourth
      (parentsInvariant @{nameEq}
        (registryFibers {value = value} {world = world} {error = error} fibers)
        fibers)
      (chainsInvariant @{nameEq}
        (S (length (registryFibers {value = value} {world = world}
          {error = error} fibers)))
        (registryFibers {value = value} {world = world} {error = error} fibers)
        fibers)
      (pairwiseProvisionInvariant @{keyEq}
        (registryFibers {value = value} {world = world} {error = error} fibers))
      (viewsInvariant @{nameEq} @{keyEq} {value = value} {world = world}
        {error = error}
        (registryFibers {value = value} {world = world} {error = error} fibers)
        fibers) valid

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

0 preservationLDivert :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (LDivert n) before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationLDivert {name} {key} {world} {error} {value}
  nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation
  with (lookupFiber @{nameEq} n fibers) proof found
  preservationLDivert {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Nothing = void (nothingIsNotJust equation)
  preservationLDivert {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Inactive outcome)) =
      void (nothingIsNotJust equation)
  preservationLDivert {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Reloading remaining accumulator view))
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retired table
          (Reloading remaining accumulator view)) fibers) view) proof matches
    preservationLDivert {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Reloading remaining accumulator view)) | True =
          void (nothingIsNotJust equation)
    preservationLDivert {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Reloading remaining accumulator view)) | False =
        case justInjective equation of
          Refl =>
            let sourceViews = sourceViewsFromWellFormed nameEq keyEq ambient fibers
                  valid
                entryPresent = lookupFiberEntries nameEq n
                  (MkFiber component parent retired table
                    (Reloading remaining accumulator view)) fibers found
                sourceSelected = viewsInvariantLookup {name = name} {key = key}
                  {world = world} {error = error} {value = value} nameEq keyEq n
                  (MkFiber component parent retired table
                    (Reloading remaining accumulator view))
                  (registryFibers fibers) fibers entryPresent sourceViews
                targetSelected = viewBindingsUnstableRuntime {name = name}
                  {key = key} {world = world} {error = error} {value = value}
                  nameEq keyEq (dependencies (componentDependencies component))
                  view n (MkFiber component parent retired table
                    (Reloading remaining accumulator view)) table
                  (Unloading accumulator view Nothing) fibers found Refl
                  sourceSelected
                targetViews = viewsInvariantUnstableRuntimeReplace {name = name}
                  {key = key} {world = world} {error = error} {value = value}
                  nameEq keyEq n (MkFiber component parent retired table
                    (Reloading remaining accumulator view)) table
                  (Unloading accumulator view Nothing) fibers found Refl
                  targetSelected sourceViews
            in registryWellFormedRuntimeReplace {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq keyEq ambient
              n (MkFiber component parent retired table
                (Reloading remaining accumulator view)) table
              (Unloading accumulator view Nothing) fibers found valid targetViews
  preservationLDivert {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Active accumulator view)) =
      void (nothingIsNotJust equation)
  preservationLDivert {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) = void (nothingIsNotJust equation)

0 preservationReloadingRuntime :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (sourceAmbient, targetAmbient : world) -> (n : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retired : Bool) ->
  (oldTable : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (newTable : OwnedTable key value (componentProvisions component)) ->
  (newLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} n fibers =
    Just (MkFiber component parent retired oldTable
      (Reloading remaining accumulator view)) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (MkSystemState sourceAmbient fibers) = True ->
  fiberViewInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (setFiberRuntime
      (MkFiber component parent retired oldTable
        (Reloading remaining accumulator view)) newTable newLifecycle)
    (replaceBinding @{nameEq} n
      (setFiberRuntime
        (MkFiber component parent retired oldTable
          (Reloading remaining accumulator view)) newTable newLifecycle)
      fibers) =
  viewBindingsInvariant @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view
    (replaceBinding @{nameEq} n
      (setFiberRuntime
        (MkFiber component parent retired oldTable
          (Reloading remaining accumulator view)) newTable newLifecycle)
      fibers) ->
  registryWellFormed @{nameEq} @{keyEq} {value = value} {world = world} {error = error}
    (MkSystemState targetAmbient
      (replaceBinding @{nameEq} n
        (setFiberRuntime
          (MkFiber component parent retired oldTable
            (Reloading remaining accumulator view)) newTable newLifecycle)
        fibers)) = True
preservationReloadingRuntime {name} {key} {world} {error} {value}
  nameEq keyEq sourceAmbient targetAmbient n component parent retired oldTable
  remaining accumulator view newTable newLifecycle fibers found valid
  targetOwnEquation =
  let sourceViews = sourceViewsFromWellFormed nameEq keyEq sourceAmbient fibers
        valid
      entryPresent = lookupFiberEntries nameEq n
        (MkFiber component parent retired oldTable
          (Reloading remaining accumulator view)) fibers found
      sourceSelected = viewsInvariantLookup {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq n
        (MkFiber component parent retired oldTable
          (Reloading remaining accumulator view))
        (registryFibers fibers) fibers entryPresent sourceViews
      targetBindings = viewBindingsUnstableRuntime {name = name} {key = key}
        {world = world} {error = error} {value = value} nameEq keyEq
        (dependencies (componentDependencies component)) view n
        (MkFiber component parent retired oldTable
          (Reloading remaining accumulator view)) newTable newLifecycle fibers
        found Refl sourceSelected
      targetSelected = trans targetOwnEquation targetBindings
      targetViews = viewsInvariantUnstableRuntimeReplace {name = name}
        {key = key} {world = world} {error = error} {value = value} nameEq keyEq n
        (MkFiber component parent retired oldTable
          (Reloading remaining accumulator view)) newTable newLifecycle fibers
        found Refl targetSelected sourceViews
  in registryWellFormedRuntimeReplace {name = name} {key = key}
    {world = world} {error = error} {value = value} nameEq keyEq targetAmbient n
    (MkFiber component parent retired oldTable
      (Reloading remaining accumulator view)) newTable newLifecycle fibers found
    valid targetViews

0 preservationLAdvance :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (LAdvance n) before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationLAdvance {name} {key} {world} {error} {value}
  nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation
  with (lookupFiber @{nameEq} n fibers) proof found
  preservationLAdvance {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Nothing = void (nothingIsNotJust equation)
  preservationLAdvance {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Inactive outcome)) =
      void (nothingIsNotJust equation)
  preservationLAdvance {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Reloading [] accumulator view))
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retired table
          (Reloading [] accumulator view)) fibers) view)
    preservationLAdvance {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Reloading [] accumulator view)) | True =
        case justInjective equation of
          Refl => preservationReloadingRuntime nameEq keyEq ambient ambient n
            component parent retired table [] accumulator view table
            (Active accumulator view) fibers found valid Refl
    preservationLAdvance {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Reloading [] accumulator view)) | False =
        case justInjective equation of
          Refl => preservationReloadingRuntime nameEq keyEq ambient ambient n
            component parent retired table [] accumulator view table
            (Unloading accumulator view Nothing) fibers found valid Refl
  preservationLAdvance {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Reloading (step :: rest) accumulator view))
    with (resolveCommittedValues @{nameEq} @{keyEq}
      (dependencies (componentDependencies component)) view fibers)
    preservationLAdvance {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Reloading (step :: rest) accumulator view)) | Nothing =
        void (nothingIsNotJust equation)
    preservationLAdvance {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Reloading (step :: rest) accumulator view)) | Just capability
      with (runStepEffect step capability (MkLocalState ambient table))
      preservationLAdvance {name} {key} {world} {error} {value}
        nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
        Just (MkFiber component parent retired table
          (Reloading (step :: rest) accumulator view)) | Just capability |
        Left err = case justInjective equation of
          Refl => preservationReloadingRuntime nameEq keyEq ambient ambient n
            component parent retired table (step :: rest) accumulator view table
            (Unloading accumulator view (Just err)) fibers found valid Refl
      preservationLAdvance {name} {key} {world} {error} {value}
        nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
        Just (MkFiber component parent retired table
          (Reloading (step :: rest) accumulator view)) | Just capability |
        Right (localAfter, undo)
        with (targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq}
            (MkFiber component parent retired table
              (Reloading (step :: rest) accumulator view)) fibers) view)
        preservationLAdvance {name} {key} {world} {error} {value}
          nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
          Just (MkFiber component parent retired table
            (Reloading (step :: rest) accumulator view)) | Just capability |
          Right (localAfter, undo) | False =
            case justInjective equation of
              Refl => preservationReloadingRuntime nameEq keyEq ambient
                (localWorld localAfter) n component parent retired table
                (step :: rest) accumulator view (localTable localAfter)
                (Unloading (accumulator . undo) view Nothing) fibers found valid
                Refl
        preservationLAdvance {name} {key} {world} {error} {value}
          nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
          Just (MkFiber component parent retired table
            (Reloading (step :: rest) accumulator view)) | Just capability |
          Right (localAfter, undo) | True with (rest)
          preservationLAdvance {name} {key} {world} {error} {value}
            nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
            Just (MkFiber component parent retired table
              (Reloading (step :: rest) accumulator view)) | Just capability |
            Right (localAfter, undo) | True | [] =
              case justInjective equation of
                Refl => preservationReloadingRuntime nameEq keyEq ambient
                  (localWorld localAfter) n component parent retired table
                  [step] accumulator view (localTable localAfter)
                  (Active (accumulator . undo) view) fibers found valid Refl
          preservationLAdvance {name} {key} {world} {error} {value}
            nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
            Just (MkFiber component parent retired table
              (Reloading (step :: rest) accumulator view)) | Just capability |
            Right (localAfter, undo) | True | (next :: more) =
              case justInjective equation of
                Refl => preservationReloadingRuntime nameEq keyEq ambient
                  (localWorld localAfter) n component parent retired table
                  (step :: next :: more) accumulator view (localTable localAfter)
                  (Reloading (next :: more) (accumulator . undo) view) fibers
                  found valid Refl
  preservationLAdvance {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Active accumulator view)) =
      void (nothingIsNotJust equation)
  preservationLAdvance {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) = void (nothingIsNotJust equation)

0 preservationLLeave :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (LLeave n) before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationLLeave {name} {key} {world} {error} {value}
  nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation
  with (lookupFiber @{nameEq} n fibers) proof found
  preservationLLeave {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Nothing = void (nothingIsNotJust equation)
  preservationLLeave {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Inactive outcome)) =
      void (nothingIsNotJust equation)
  preservationLLeave {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Reloading remaining accumulator view)) = void (nothingIsNotJust equation)
  preservationLLeave {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Active accumulator view))
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retired table (Active accumulator view)) fibers)
      view)
    preservationLLeave {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table (Active accumulator view)) |
      True = void (nothingIsNotJust equation)
    preservationLLeave {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table (Active accumulator view)) |
      False = case justInjective equation of
        Refl =>
          let sourceViews = sourceViewsFromWellFormed nameEq keyEq ambient fibers
                valid
              targetViews = viewsInvariantActiveUnload {name = name} {key = key}
                {world = world} {error = error} {value = value} nameEq keyEq n
                component parent retired table accumulator view fibers found
                sourceViews
          in registryWellFormedRuntimeReplace {name = name} {key = key}
            {world = world} {error = error} {value = value} nameEq keyEq ambient n
            (MkFiber component parent retired table (Active accumulator view))
            table (Unloading accumulator view Nothing) fibers found valid
            targetViews
  preservationLLeave {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) = void (nothingIsNotJust equation)

0 preservationLUnload :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  applyAction @{nameEq} @{keyEq} (LUnload n) before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
preservationLUnload {name} {key} {world} {error} {value}
  nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation
  with (lookupFiber @{nameEq} n fibers) proof found
  preservationLUnload {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Nothing = void (nothingIsNotJust equation)
  preservationLUnload {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Inactive outcome)) =
      void (nothingIsNotJust equation)
  preservationLUnload {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Reloading remaining accumulator view)) = void (nothingIsNotJust equation)
  preservationLUnload {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table (Active accumulator view)) =
      void (nothingIsNotJust equation)
  preservationLUnload {name} {key} {world} {error} {value}
    nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) with (relied @{nameEq} n fibers)
      proof reliedProof
    preservationLUnload {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Unloading accumulator view outcome)) | True =
          void (nothingIsNotJust equation)
    preservationLUnload {name} {key} {world} {error} {value}
      nameEq keyEq n (MkSystemState ambient fibers) afterState tag valid equation |
      Just (MkFiber component parent retired table
        (Unloading accumulator view outcome)) | False =
        case justInjective equation of
          Refl =>
            let sourceViews = sourceViewsFromWellFormed nameEq keyEq ambient fibers
                  valid
                targetViews = viewsInvariantUnloadingInactive {name = name}
                  {key = key} {world = world} {error = error} {value = value}
                  nameEq keyEq n component parent retired table accumulator view
                  outcome
                  (localTable (accumulator (MkLocalState ambient table))) fibers
                  found reliedProof sourceViews
            in registryWellFormedRuntimeReplace {name = name} {key = key}
              {world = world} {error = error} {value = value} nameEq keyEq
              (localWorld (accumulator (MkLocalState ambient table))) n
              (MkFiber component parent retired table
                (Unloading accumulator view outcome))
              (localTable (accumulator (MkLocalState ambient table)))
              (Inactive outcome) fibers found valid targetViews

||| Paper Theorem 59, stated over the raw ten-rule evaluator. Unlike the checked
||| admission fact, this direction cannot hide a malformed endpoint.
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

||| Inhabitant of raw paper Theorem 59, dispatched over every executable action.
public export
0 preservationTheoremProof : preservationTheorem name key value world error
preservationTheoremProof nameEq keyEq (OInsert n parent component) before
  afterState tag valid equation = preservationOInsert nameEq keyEq n parent
    component before afterState tag valid equation
preservationTheoremProof nameEq keyEq (ORetire n) before afterState tag valid
  equation = preservationORetire nameEq keyEq n before afterState tag valid
    equation
preservationTheoremProof nameEq keyEq (ORemove n) before afterState tag valid
  equation = preservationORemove nameEq keyEq n before afterState tag valid
    equation
preservationTheoremProof nameEq keyEq (LBegin n) before afterState tag valid
  equation = preservationLBegin nameEq keyEq n before afterState tag valid equation
preservationTheoremProof nameEq keyEq (LAdvance n) before afterState tag valid
  equation = preservationLAdvance nameEq keyEq n before afterState tag valid
    equation
preservationTheoremProof nameEq keyEq (LDivert n) before afterState tag valid
  equation = preservationLDivert nameEq keyEq n before afterState tag valid
    equation
preservationTheoremProof nameEq keyEq (LLeave n) before afterState tag valid
  equation = preservationLLeave nameEq keyEq n before afterState tag valid equation
preservationTheoremProof nameEq keyEq (LUnload n) before afterState tag valid
  equation = preservationLUnload nameEq keyEq n before afterState tag valid
    equation

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

||| A trace whose transition dictionaries are the episode's dictionaries.
||| This is operationally irrelevant but avoids assuming proof irrelevance for
||| distinct `DecEq` implementations when extracting global episodes.
public export
data AlignedTransitions : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  AlignedEnd : AlignedTransitions name key world error value nameEq keyEq
    NoTransitions
  AlignedStep :
    {first, middle, finalState : SystemState name key value world error} ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (equation : checkedApplyAction @{nameEq} @{keyEq} action first =
      Just (tag, middle)) ->
    (rest : Transitions middle finalState) ->
    AlignedTransitions name key world error value nameEq keyEq rest ->
    AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions (Fired {before = first} {afterState = middle}
        nameEq keyEq action tag equation) rest)

||| Every state in this trace segment, including both endpoints, is installed.
public export
data InstalledTrace : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) ->
  (keyEq : DecEq key) -> (n : name) ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  InstalledEnd : installedAt @{nameEq} n state = True ->
    InstalledTrace name key world error value nameEq keyEq n
      (NoTransitions {state})
  InstalledStep :
    {first, middle, finalState : SystemState name key value world error} ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (equation : checkedApplyAction @{nameEq} @{keyEq} action first =
      Just (tag, middle)) ->
    (rest : Transitions middle finalState) ->
    installedAt @{nameEq} n first = True ->
    InstalledTrace name key world error value nameEq keyEq n rest ->
    InstalledTrace name key world error value nameEq keyEq n
      {start = first} {end = finalState}
      (MoreTransitions (Fired nameEq keyEq action tag equation) rest)

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
  insideInstalled : InstalledTrace name key world error value nameEq keyEq n inside

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
  closedInsideInstalled : InstalledTrace name key world error value nameEq keyEq n closedInside
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

public export
actionOwner : Action name key value world error -> name
actionOwner (OInsert n parent component) = n
actionOwner (ORetire n) = n
actionOwner (ORemove n) = n
actionOwner (LBegin n) = n
actionOwner (LAdvance n) = n
actionOwner (LDivert n) = n
actionOwner (LLeave n) = n
actionOwner (LUnload n) = n

||| Finite-list realization of paper Definition 60's continuation closure.
||| `ReachableSuffix source target` witnesses that `target` is the iterator
||| continuation reached after zero or more yields from `source`.
public export
data ReachableSuffix : List a -> List a -> Type where
  SuffixHere : ReachableSuffix suffix suffix
  SuffixLater : ReachableSuffix rest suffix ->
    ReachableSuffix (discarded :: rest) suffix

||| One reachable nonterminal iterator stage belonging to an actual LAdvance
||| occurrence. Every nonempty suffix is represented, so later continuations
||| are generators even when the supplied trace stops before executing them.
public export
data IteratorStage :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (actor : name) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  StageFromAdvance :
    {before, afterState : SystemState name key value world error} ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
    (tag : RuleTag) ->
    (equation : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) before =
      Just (tag, afterState)) ->
    OccursIn (Fired {before = before} {afterState = afterState}
      nameEq keyEq (LAdvance actor) tag equation) trace ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} actor (registry before) = Just fiber ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber)))) ->
    (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
      LocalState key value world
        (componentProvisions (fiberComponent fiber))) ->
    (view : View name
      (dependencies (componentDependencies (fiberComponent fiber)))) ->
    fiberLifecycle fiber = Reloading remaining accumulator view ->
    (step : StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) ->
    (rest : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber)))) ->
    ReachableSuffix remaining (step :: rest) ->
    IteratorStage name key world error value actor trace

||| Lift one concrete yielded local inverse to the complete effect state.
public export
yieldedInverseEffectMap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (provision : CoeffectSpec key) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  PartialEffectMap name key value world
yieldedInverseEffectMap nameEq keyEq actor provision undo state =
  let owned = restrictOwned @{keyEq} provision (effectTables state actor)
      restored = undo (MkLocalState (effectAmbient state) owned)
  in Just (setEffectTable @{nameEq} actor
    (ownedValues (localTable restored))
    (setEffectAmbient (localWorld restored) state))

||| Evaluate one reachable iterator stage, exposing both its forward result and
||| the exact inverse yielded at this application state. The continuation is
||| the stage's statically fixed `rest`; unlike the paper's general iterator,
||| this finite calculus has no data-dependent continuation constructor.
public export
iteratorStepEffect :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (fiber : Fiber name key value world error) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  EffectState name key value world ->
  Maybe (EffectState name key value world, PartialEffectMap name key value world)
iteratorStepEffect nameEq keyEq actor fiber step view state =
  case resolveEffectValues @{keyEq}
    (dependencies (componentDependencies (fiberComponent fiber))) view state of
    Nothing => Nothing
    Just capability =>
      let owned = restrictOwned @{keyEq}
            (componentProvisions (fiberComponent fiber))
            (effectTables state actor)
      in case runStepEffect step capability
        (MkLocalState (effectAmbient state) owned) of
        Left _ => Nothing
        Right (after, undo) =>
          let next = setEffectTable @{nameEq} actor
                (ownedValues (localTable after))
                (setEffectAmbient (localWorld after) state)
          in Just (next,
            yieldedInverseEffectMap nameEq keyEq actor
              (componentProvisions (fiberComponent fiber)) undo)

public export
data IteratorContinuation : (key : Type) -> (value : key -> Type) ->
  (world, error : Type) -> Type where
  MkIteratorContinuation : {deps : List key} -> {provision : CoeffectSpec key} ->
    List (StepEffect key value world error deps provision) ->
    IteratorContinuation key value world error

public export
iteratorStageEffect :
  IteratorStage name key world error value actor trace ->
  EffectState name key value world ->
  Maybe (EffectState name key value world,
    PartialEffectMap name key value world,
    IteratorContinuation key value world error)
iteratorStageEffect
  (StageFromAdvance nameEq keyEq actor tag equation occurs fiber found remaining
    accumulator view lifecycle step rest suffix) state =
  map (\(after, undo) =>
    (after, undo, MkIteratorContinuation rest))
    (iteratorStepEffect nameEq keyEq actor fiber step view state)

||| Equation 54 generators: actual Table-1 maps, every reachable iterator
||| forward map, and every inverse yielded by such a stage at every origin.
public export
data TraceEffectGenerator :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (actor : name) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  ActualForwardGenerator :
    (before, afterState : SystemState name key value world error) ->
    (nameEq : DecEq name) -> (keyEq : DecEq key) ->
    (action : Action name key value world error) -> (tag : RuleTag) ->
    (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    OccursIn (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag equation) trace ->
    actionOwner action = actor ->
    TraceEffectGenerator name key world error value actor trace
  IteratorForwardGenerator :
    IteratorStage name key world error value actor trace ->
    TraceEffectGenerator name key world error value actor trace
  IteratorYieldedGenerator :
    IteratorStage name key world error value actor trace ->
    EffectState name key value world ->
    TraceEffectGenerator name key world error value actor trace

public export
traceGeneratorMap :
  TraceEffectGenerator name key world error value actor trace ->
  PartialEffectMap name key value world
traceGeneratorMap
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation
    occurs actorMatches) state =
  partialEffectMapFor nameEq keyEq action tag before state
traceGeneratorMap (IteratorForwardGenerator stage) state =
  map (\(after, undo, continuation) => after)
    (iteratorStageEffect stage state)
traceGeneratorMap (IteratorYieldedGenerator stage origin) state =
  case iteratorStageEffect stage origin of
    Nothing => Nothing
    Just (after, undo, continuation) => undo state

||| The partial transformation monoid M(i) generated by Equation 54.
public export
data TraceEffectTransformation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (actor : name) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  TraceIdentity : TraceEffectTransformation name key world error value actor trace
  TraceGenerator : TraceEffectGenerator name key world error value actor trace ->
    TraceEffectTransformation name key world error value actor trace
  TraceCompose :
    TraceEffectTransformation name key world error value actor trace ->
    TraceEffectTransformation name key world error value actor trace ->
    TraceEffectTransformation name key world error value actor trace

public export
runTraceEffectTransformation :
  TraceEffectTransformation name key world error value actor trace ->
  PartialEffectMap name key value world
runTraceEffectTransformation TraceIdentity = partialIdentity
runTraceEffectTransformation (TraceGenerator generator) =
  traceGeneratorMap generator
runTraceEffectTransformation (TraceCompose after before) =
  partialCompose (runTraceEffectTransformation after)
    (runTraceEffectTransformation before)

||| Equation 55 compares the yielded inverse and continuation. In this finite
||| representation the continuation is fixed by `ReachableSuffix`; this family
||| therefore compares the only dynamic yield field, the inverse, at every
||| foreign-moved origin. Undefinedness must agree as well.
public export
data IteratorYieldAgreement :
  (name, key : Type) -> (value : key -> Type) -> (world, error : Type) ->
  (keyEq : DecEq key) ->
  Maybe (EffectState name key value world,
    PartialEffectMap name key value world,
    IteratorContinuation key value world error) ->
  Maybe (EffectState name key value world,
    PartialEffectMap name key value world,
    IteratorContinuation key value world error) -> Type where
  IteratorBothUndefined :
    IteratorYieldAgreement name key value world error keyEq Nothing Nothing
  IteratorYieldsAgree :
    leftContinuation = rightContinuation ->
    PartialMapsEquivalent (EffectStateEquivalence keyEq) leftUndo rightUndo ->
    IteratorYieldAgreement name key value world error keyEq
      (Just (leftAfter, leftUndo, leftContinuation))
      (Just (rightAfter, rightUndo, rightContinuation))

public export
IteratorYieldStableUnder :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {trace : Transitions first last} -> {actor : name} ->
  (keyEq : DecEq key) ->
  IteratorStage name key world error value actor trace ->
  PartialEffectMap name key value world ->
  EffectState name key value world -> Type
IteratorYieldStableUnder {name} {key} {world} {error} {value}
  keyEq stage foreign origin =
  case foreign origin of
    Nothing => Unit
    Just moved => IteratorYieldAgreement name key value world error keyEq
      (iteratorStageEffect stage moved) (iteratorStageEffect stage origin)

||| Full-effect-state Definition 60 / Equation 55. Distinct actors' complete
||| generated monoids commute, including every individual yielded inverse, and
||| moving an iterator by any foreign generated transformation preserves its
||| yielded inverse (and its statically fixed reachable continuation).
public export
record TraceIndependent (name, key, world, error : Type)
                        (value : key -> Type) (keyEq : DecEq key)
                        {first, last : SystemState name key value world error}
                        (trace : Transitions first last) where
  constructor MkTraceIndependent
  0 generatedMonoidsCommute :
    (left, right : name) -> Not (left = right) ->
    (leftT : TraceEffectTransformation name key world error value left trace) ->
    (rightT : TraceEffectTransformation name key world error value right trace) ->
    PartialCommute (EffectStateEquivalence keyEq)
      (runTraceEffectTransformation leftT)
      (runTraceEffectTransformation rightT)
  0 iteratorYieldsStable :
    (left, right : name) -> Not (left = right) ->
    (stage : IteratorStage name key world error value left trace) ->
    (foreign : TraceEffectTransformation name key world error value right trace) ->
    (origin : EffectState name key value world) ->
    IteratorYieldStableUnder keyEq stage
      (runTraceEffectTransformation foreign) origin

||| Direct projection used by recovery: each concrete yielded inverse is a
||| generator in M(i), so final-accumulator cancellation cannot hide it.
public export
0 yieldedInverseCommutes :
  (independent : TraceIndependent name key world error value keyEq trace) ->
  (left, right : name) -> Not (left = right) ->
  (stage : IteratorStage name key world error value left trace) ->
  (origin : EffectState name key value world) ->
  (foreign : TraceEffectTransformation name key world error value right trace) ->
  PartialCommute (EffectStateEquivalence keyEq)
    (traceGeneratorMap (IteratorYieldedGenerator stage origin))
    (runTraceEffectTransformation foreign)
yieldedInverseCommutes independent left right distinct stage origin foreign =
  generatedMonoidsCommute independent left right distinct
    (TraceGenerator (IteratorYieldedGenerator stage origin)) foreign

||| Every statically reachable continuation forward map is likewise a generator.
public export
0 reachableContinuationCommutes :
  (independent : TraceIndependent name key world error value keyEq trace) ->
  (left, right : name) -> Not (left = right) ->
  (stage : IteratorStage name key world error value left trace) ->
  (foreign : TraceEffectTransformation name key world error value right trace) ->
  PartialCommute (EffectStateEquivalence keyEq)
    (traceGeneratorMap (IteratorForwardGenerator stage))
    (runTraceEffectTransformation foreign)
reachableContinuationCommutes independent left right distinct stage foreign =
  generatedMonoidsCommute independent left right distinct
    (TraceGenerator (IteratorForwardGenerator stage)) foreign

public export
0 noOccurrenceInEmpty : OccursIn transition NoTransitions -> Void
noOccurrenceInEmpty occurrence impossible

0 noIteratorStageInEmpty :
  IteratorStage name key world error value actor NoTransitions -> Void
noIteratorStageInEmpty (StageFromAdvance nameEq keyEq actor tag equation occurs
  fiber found remaining accumulator view lifecycle step rest suffix) =
  noOccurrenceInEmpty occurs

0 noTraceGeneratorInEmpty :
  TraceEffectGenerator name key world error value actor NoTransitions -> Void
noTraceGeneratorInEmpty
  (ActualForwardGenerator before afterState nameEq keyEq action tag equation occurs
    actorMatches) = noOccurrenceInEmpty occurs
noTraceGeneratorInEmpty (IteratorForwardGenerator stage) =
  noIteratorStageInEmpty stage
noTraceGeneratorInEmpty (IteratorYieldedGenerator stage origin) =
  noIteratorStageInEmpty stage

0 emptyTraceTransformationMap :
  (transformation : TraceEffectTransformation name key world error value actor
    (NoTransitions {state = systemState})) ->
  (effectState : EffectState name key value world) ->
  runTraceEffectTransformation transformation effectState = Just effectState
emptyTraceTransformationMap TraceIdentity effectState = Refl
emptyTraceTransformationMap (TraceGenerator generator) effectState =
  void (noTraceGeneratorInEmpty generator)
emptyTraceTransformationMap (TraceCompose after before) effectState =
  rewrite emptyTraceTransformationMap before effectState in
    emptyTraceTransformationMap after effectState

0 emptyTraceCompositionMap :
  (after : TraceEffectTransformation name key world error value afterActor
    (NoTransitions {state = systemState})) ->
  (before : TraceEffectTransformation name key world error value beforeActor
    (NoTransitions {state = systemState})) ->
  (effectState : EffectState name key value world) ->
  partialCompose (runTraceEffectTransformation after)
    (runTraceEffectTransformation before) effectState = Just effectState
emptyTraceCompositionMap after before effectState =
  rewrite emptyTraceTransformationMap before effectState in
    emptyTraceTransformationMap after effectState

||| Concrete non-vacuity witness for every full effect state.
public export
emptyTraceIndependent : (keyEq : DecEq key) ->
  TraceIndependent name key world error value keyEq (NoTransitions {state})
emptyTraceIndependent keyEq = MkTraceIndependent
  (\left, right, distinct, leftT, rightT, effectState =>
    rewrite emptyTraceCompositionMap leftT rightT effectState in
    rewrite emptyTraceCompositionMap rightT leftT effectState in
    PartialDefined (effectStateReflexive keyEq effectState))
  (\left, right, distinct, stage, foreign, origin =>
    void (noIteratorStageInEmpty stage))

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

||| Prefix form of paper Definition 60. It is the generated-monoid family
||| condition itself, not a commutation assumption about the final accumulator.
||| The selected accumulator is derived from the individual yielded generators
||| recorded by `IteratorStage` during the eventual Theorem-61 induction.
public export
PrefixRecoveryIndependent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {start, current : SystemState name key value world error} ->
  Transitions start current -> Type
PrefixRecoveryIndependent name key world error value nameEq keyEq selected trace =
  TraceIndependent name key world error value keyEq trace

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
    (prefixTransitions episode) ->
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

public export
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
%inline
lifecycleResolvedProvider : DecEq name => DecEq key =>
  (k : key) -> (provider : name) ->
  (component : Component key value world error) ->
  Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component) -> Bool
lifecycleResolvedProvider k provider component (Inactive outcome) = False
lifecycleResolvedProvider k provider component
  (Reloading remaining accumulator view) =
    case viewLookup k (dependencies (componentDependencies component)) view of
      Nothing => False
      Just actual => case decEq actual provider of
        Yes Refl => True
        No _ => False
lifecycleResolvedProvider k provider component (Active accumulator view) =
  case viewLookup k (dependencies (componentDependencies component)) view of
    Nothing => False
    Just actual => case decEq actual provider of
      Yes Refl => True
      No _ => False
lifecycleResolvedProvider k provider component
  (Unloading accumulator view outcome) =
    case viewLookup k (dependencies (componentDependencies component)) view of
      Nothing => False
      Just actual => case decEq actual provider of
        Yes Refl => True
        No _ => False

public export
%inline
fiberResolvedProvider : DecEq name => DecEq key => key -> name ->
  Fiber name key value world error -> Bool
fiberResolvedProvider k provider
  (MkFiber component parent retired table lifecycle) =
    lifecycleResolvedProvider k provider component lifecycle

public export
resolvedProviderAt : DecEq name => DecEq key => name -> key -> name ->
  SystemState name key value world error -> Bool
resolvedProviderAt consumer k provider state =
  case lookupFiber consumer (registry state) of
    Nothing => False
    Just (MkFiber component parent retired table lifecycle) =>
      case committed lifecycle of
      Nothing => False
      Just view => case viewLookup k
        (dependencies (componentDependencies component)) view of
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
||| Its inhabitant is `DGamma.Ordering.orderingTheoremProof`.
public export
orderingTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
orderingTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, final : SystemState name key value world error) ->
  (global : Transitions initial final) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  wellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  (consumer, provider : name) -> Not (consumer = provider) -> (k : key) ->
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

0 lookupEntriesDecEqCoherent :
  {key : Type} -> {value : key -> Type} ->
  (leftEq, rightEq : DecEq key) -> (wanted : key) ->
  (entries : List (Binding key value)) ->
  lookupEntries @{leftEq} wanted entries = lookupEntries @{rightEq} wanted entries
lookupEntriesDecEqCoherent leftEq rightEq wanted [] = Refl
lookupEntriesDecEqCoherent leftEq rightEq wanted (Bind current observed :: rest)
  with (decEq @{leftEq} wanted current)
  lookupEntriesDecEqCoherent leftEq rightEq current
    (Bind current observed :: rest) | (Yes Refl)
    with (decEq @{rightEq} current current)
    lookupEntriesDecEqCoherent leftEq rightEq current
      (Bind current observed :: rest) | (Yes Refl) | (Yes Refl) = Refl
    lookupEntriesDecEqCoherent leftEq rightEq current
      (Bind current observed :: rest) | (Yes Refl) | (No contra) =
        void (contra Refl)
  lookupEntriesDecEqCoherent leftEq rightEq wanted
    (Bind current observed :: rest) | (No leftDistinct)
    with (decEq @{rightEq} wanted current)
    lookupEntriesDecEqCoherent leftEq rightEq current
      (Bind current observed :: rest) | (No leftDistinct) | (Yes Refl) =
        void (leftDistinct Refl)
    lookupEntriesDecEqCoherent leftEq rightEq wanted
      (Bind current observed :: rest) | (No leftDistinct) | (No rightDistinct) =
        lookupEntriesDecEqCoherent leftEq rightEq wanted rest

public export
0 lookupFiberDecEqCoherent :
  (leftEq, rightEq : DecEq name) -> (wanted : name) ->
  (fibers : Registry name key value world error) ->
  lookupFiber @{leftEq} {key = key} {value = value} {world = world}
    {error = error} wanted fibers =
  lookupFiber @{rightEq} {key = key} {value = value} {world = world}
    {error = error} wanted fibers
lookupFiberDecEqCoherent leftEq rightEq wanted
  (MkCoeffectContext entries unique) =
  lookupEntriesDecEqCoherent leftEq rightEq wanted entries

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

0 setFiberRuntimeReloadingBool :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  (case fiberLifecycle
    (setFiberRuntime fiber table (Reloading remaining accumulator view)) of
      Reloading _ _ _ => True
      _ => False) = True
setFiberRuntimeReloadingBool
  (MkFiber component parent retired oldTable oldLifecycle) table remaining
  accumulator view = Refl

0 setFiberRuntimeCommittedProviders :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  map (\resolved => viewProviders resolved) (committed (fiberLifecycle
    (setFiberRuntime fiber table (Reloading remaining accumulator view)))) =
    Just (viewProviders view)
setFiberRuntimeCommittedProviders
  (MkFiber component parent retired oldTable oldLifecycle) table remaining
  accumulator view = Refl

0 committedReloadingAfterReplace :
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
  committedProvidersAt {key = key} {value = value} {world = world}
    {error = error} selected (MkSystemState worldValue
      (replaceBinding selected
        (setFiberRuntime fiber table
          (Reloading remaining accumulator view)) fibers)) =
    Just (viewProviders view)
committedReloadingAfterReplace {table} {remaining} {accumulator} {view} selected
  fiber@(MkFiber component parent retired oldTable oldLife) found =
  rewrite lookupReplacedFiber selected fiber
    (setFiberRuntime fiber table (Reloading remaining accumulator view)) fibers
    found in Refl


0 committedActiveAfterReplace :
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
  committedProvidersAt {key = key} {value = value} {world = world}
    {error = error} selected (MkSystemState worldValue
      (replaceBinding selected
        (setFiberRuntime fiber table (Active accumulator view)) fibers)) =
    Just (viewProviders view)
committedActiveAfterReplace {table} {accumulator} {view} selected
  fiber@(MkFiber component parent retired oldTable oldLife) found =
  rewrite lookupReplacedFiber selected fiber
    (setFiberRuntime fiber table (Active accumulator view)) fibers found in Refl

0 committedUnloadingAfterReplace :
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
  committedProvidersAt {key = key} {value = value} {world = world}
    {error = error} selected (MkSystemState worldValue
      (replaceBinding selected
        (setFiberRuntime fiber table (Unloading accumulator view outcome)) fibers)) =
    Just (viewProviders view)
committedUnloadingAfterReplace {table} {accumulator} {view} {outcome} selected
  fiber@(MkFiber component parent retired oldTable oldLife) found =
  rewrite lookupReplacedFiber selected fiber
    (setFiberRuntime fiber table (Unloading accumulator view outcome)) fibers found in Refl

public export
record ReloadingSnapshot
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name) (providers : List name)
  (state : SystemState name key value world error) where
  constructor MkReloadingSnapshot
  snapshotFiber : Fiber name key value world error
  snapshotLookup : lookupFiber @{nameEq} selected (registry state) =
    Just snapshotFiber
  snapshotRemaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent snapshotFiber)))
    (componentProvisions (fiberComponent snapshotFiber)))
  snapshotAccumulator : LocalState key value world
      (componentProvisions (fiberComponent snapshotFiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent snapshotFiber))
  snapshotView : View name
    (dependencies (componentDependencies (fiberComponent snapshotFiber)))
  snapshotReloading : fiberLifecycle snapshotFiber =
    Reloading snapshotRemaining snapshotAccumulator snapshotView
  snapshotProviders : viewProviders snapshotView = providers

0 snapshotFromPredicates :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (providers : List name) ->
  (state : SystemState name key value world error) ->
  reloadingAt @{nameEq} selected state = True ->
  committedProvidersAt @{nameEq} selected state = Just providers ->
  ReloadingSnapshot name key world error value nameEq selected providers state
snapshotFromPredicates {name} {key} {world} {error} {value}
  nameEq selected providers state reloading committedProviders
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  snapshotFromPredicates {name} {key} {world} {error} {value}
    nameEq selected providers state reloading committedProviders | Nothing =
      void (falseIsNotTrue reloading)
  snapshotFromPredicates {name} {key} {world} {error} {value}
    nameEq selected providers state reloading committedProviders | Just fiber
    with (fiberLifecycle fiber) proof lifecycle
    snapshotFromPredicates {name} {key} {world} {error} {value}
      nameEq selected providers state reloading committedProviders | Just fiber |
      Inactive outcome = void (falseIsNotTrue reloading)
    snapshotFromPredicates {name} {key} {world} {error} {value}
      nameEq selected providers state reloading committedProviders | Just fiber |
      Active accumulator view = void (falseIsNotTrue reloading)
    snapshotFromPredicates {name} {key} {world} {error} {value}
      nameEq selected providers state reloading committedProviders | Just fiber |
      Unloading accumulator view outcome = void (falseIsNotTrue reloading)
    snapshotFromPredicates {name} {key} {world} {error} {value}
      nameEq selected providers state reloading committedProviders | Just fiber |
      Reloading remaining accumulator view =
        MkReloadingSnapshot fiber found remaining accumulator view lifecycle
          (justInjective committedProviders)

0 systemStateEta : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
systemStateEta (MkSystemState ambient fibers) = Refl

0 beginFiberReloadingSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (fiber : Fiber name key value world error) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  lookupFiber @{nameEq} selected fibers = Just fiber ->
  beginFiberAction @{nameEq} @{keyEq} selected fiber
    (MkSystemState ambient fibers) =
    Just (LBeginTag, afterState) ->
  (providers : List name ** ReloadingSnapshot name key world error value nameEq
    selected providers afterState)
beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
  nameEq keyEq selected fiber ambient fibers afterState found equation
  with (fiberLifecycle fiber)
  beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
    nameEq keyEq selected fiber ambient fibers afterState found equation |
    Inactive Nothing with (targetFiber @{nameEq} @{keyEq} fiber fibers)
    beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
      nameEq keyEq selected fiber ambient fibers afterState found equation |
      Inactive Nothing | Nothing = void (nothingIsNotJust equation)
    beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
      nameEq keyEq selected fiber ambient fibers afterState found equation |
      Inactive Nothing | Just view with (fibers)
      beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
        nameEq keyEq selected fiber ambient fibers afterState found equation |
        Inactive Nothing | Just view | (MkCoeffectContext entries unique) = case justInjective equation of
          Refl =>
            let 0 replacementLookup : (lookupFiber @{nameEq} {key = key}
                  {value = value} {world = world} {error = error} selected
                  (replaceBinding @{nameEq} selected
                    (setFiberRuntime fiber (fiberTable fiber)
                      (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view))
                    (MkCoeffectContext entries unique)) =
                  Just (setFiberRuntime fiber (fiberTable fiber)
                    (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view)))
                replacementLookup = lookupReplaceEntries @{nameEq}
                  {value = FiberAt name key value world error} selected fiber
                  (setFiberRuntime fiber (fiberTable fiber)
                    (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view))
                  entries found
                0 reloadingAfter : (reloadingAt @{nameEq} {key = key}
                  {value = value} {world = world} {error = error} selected
                  (MkSystemState ambient
                    (replaceBinding @{nameEq} selected
                      (setFiberRuntime fiber (fiberTable fiber)
                        (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view))
                      (MkCoeffectContext entries unique))) = True)
                reloadingAfter = rewrite replacementLookup in
                  setFiberRuntimeReloadingBool fiber (fiberTable fiber)
                    (componentProgram (fiberComponent fiber))
                    (\local => local) view
                0 committedAfter : (committedProvidersAt @{nameEq} {key = key}
                  {value = value} {world = world} {error = error} selected
                  (MkSystemState ambient
                    (replaceBinding @{nameEq} selected
                      (setFiberRuntime fiber (fiberTable fiber)
                        (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view))
                      (MkCoeffectContext entries unique))) = Just (viewProviders view))
                committedAfter = rewrite replacementLookup in
                  setFiberRuntimeCommittedProviders fiber (fiberTable fiber)
                    (componentProgram (fiberComponent fiber))
                    (\local => local) view
            in (viewProviders view **
              snapshotFromPredicates nameEq selected (viewProviders view)
                (MkSystemState ambient
                  (replaceBinding @{nameEq} selected
                    (setFiberRuntime fiber (fiberTable fiber)
                      (Reloading (componentProgram (fiberComponent fiber)) (\local => local) view))
                    (MkCoeffectContext entries unique)))
                reloadingAfter committedAfter)
  beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
    nameEq keyEq selected fiber ambient fibers afterState found equation |
    Inactive (Just err) = void (nothingIsNotJust equation)
  beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
    nameEq keyEq selected fiber ambient fibers afterState found equation |
    Reloading remaining accumulator view = void (nothingIsNotJust equation)
  beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
    nameEq keyEq selected fiber ambient fibers afterState found equation |
    Active accumulator view = void (nothingIsNotJust equation)
  beginFiberReloadingSnapshot {name} {key} {world} {error} {value}
    nameEq keyEq selected fiber ambient fibers afterState found equation |
    Unloading accumulator view outcome = void (nothingIsNotJust equation)

0 beginReloadingSnapshotFromEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (LBeginTag, afterState) ->
  (providers : List name ** ReloadingSnapshot name key world error value nameEq
    selected providers afterState)
beginReloadingSnapshotFromEquation {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState equation
  with (lookupFiber @{nameEq} selected (registry before)) proof found
  beginReloadingSnapshotFromEquation {name} {key} {world} {error} {value}
    nameEq keyEq selected before afterState equation | Nothing =
      void (nothingIsNotJust equation)
  beginReloadingSnapshotFromEquation {name} {key} {world} {error} {value}
    nameEq keyEq selected before afterState equation | Just fiber =
      beginFiberReloadingSnapshot nameEq keyEq selected fiber (worldState before) (registry before) afterState
        found (replace {p = \state => beginFiberAction @{nameEq} @{keyEq}
          selected fiber state = Just (LBeginTag, afterState)}
          (sym (systemStateEta before)) equation)

0 beginReloadingSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  BeginStep nameEq keyEq selected before afterState ->
  (providers : List name ** ReloadingSnapshot name key world error value nameEq
    selected providers afterState)
beginReloadingSnapshot nameEq keyEq selected before afterState opening =
  beginReloadingSnapshotFromEquation nameEq keyEq selected before afterState
    (checkedActionProjects nameEq keyEq (LBegin selected) before afterState
      LBeginTag (beginEquation opening))

0 snapshotReloadingAt :
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers state) -> reloadingAt @{nameEq} selected state = True
snapshotReloadingAt snapshot = rewrite snapshotLookup snapshot in
  rewrite snapshotReloading snapshot in Refl

0 snapshotCommittedProviders :
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers state) ->
  committedProvidersAt @{nameEq} selected state = Just providers
snapshotCommittedProviders snapshot = rewrite snapshotLookup snapshot in
  rewrite snapshotReloading snapshot in rewrite snapshotProviders snapshot in Refl

0 snapshotEndThroughout :
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers state) ->
  ReloadingThroughout name key world error value nameEq selected
    (NoTransitions {state})
snapshotEndThroughout snapshot = ReloadingEnd (snapshotFiber snapshot)
  (snapshotLookup snapshot)
  (snapshotRemaining snapshot ** (snapshotAccumulator snapshot **
    (snapshotView snapshot ** snapshotReloading snapshot)))

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
%hint
0 fiberParentRetireHint : (fiber : Fiber name key value world error) ->
  fiberParent (retireFiber fiber) = fiberParent fiber
fiberParentRetireHint (MkFiber component parent retired table lifecycle) = Refl

public export
%hint
0 fiberParentSetLifecycleHint :
  (fiber : Fiber name key value world error) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  fiberParent (setFiberLifecycle fiber life) = fiberParent fiber
fiberParentSetLifecycleHint (MkFiber component parent retired table oldLife)
  life = Refl

public export
%hint
0 fiberParentSetRuntimeHint :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value (componentProvisions (fiberComponent fiber))) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  fiberParent (setFiberRuntime fiber table life) = fiberParent fiber
fiberParentSetRuntimeHint (MkFiber component parent retired oldTable oldLife)
  table life = Refl

public export
data NotReloading : Lifecycle key value world error name deps provision -> Type where
  NotInactive : NotReloading (Inactive outcome)
  NotActive : NotReloading (Active accumulator view)
  NotUnloading : NotReloading (Unloading accumulator view outcome)

public export
data ContinuationUpdate :
  Fiber name key value world error -> Fiber name key value world error -> Type where
  ContinuationPreserved :
    {old, updated : Fiber name key value world error} ->
    fiberContinuationLength updated = fiberContinuationLength old ->
    ContinuationUpdate old updated
  ContinuationStopped :
    {old, updated : Fiber name key value world error} ->
    fiberContinuationLength updated = Nothing -> ContinuationUpdate old updated
  ContinuationAdvanced :
    {old, updated : Fiber name key value world error} ->
    (remainingLength : Nat) ->
    fiberContinuationLength old = Just (S remainingLength) ->
    fiberContinuationLength updated = Just remainingLength ->
    ContinuationUpdate old updated
  ContinuationRestarted :
    {old, updated : Fiber name key value world error} ->
    fiberContinuationLength updated =
      Just (length (componentProgram (fiberComponent old))) ->
    ContinuationUpdate old updated

public export
data RetirementUpdate :
  Fiber name key value world error -> Fiber name key value world error -> Type where
  RetirementStable : {old, updated : Fiber name key value world error} ->
    retired updated = retired old -> RetirementUpdate old updated
  RetirementApplied : {old, updated : Fiber name key value world error} ->
    retired updated = True -> RetirementUpdate old updated

0 continuationAfterRetire : (fiber : Fiber name key value world error) ->
  fiberContinuationLength (retireFiber fiber) = fiberContinuationLength fiber
continuationAfterRetire
  (MkFiber component parent retiredFlag table (Inactive outcome)) = Refl
continuationAfterRetire
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator view)) = Refl
continuationAfterRetire
  (MkFiber component parent retiredFlag table (Active accumulator view)) = Refl
continuationAfterRetire
  (MkFiber component parent retiredFlag table
    (Unloading accumulator view outcome)) = Refl

0 continuationLengthReloading :
  (fiber : Fiber name key value world error) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  fiberContinuationLength fiber = Just (length remaining)
continuationLengthReloading
  (MkFiber component parent retiredFlag table (Inactive outcome)) remaining
  accumulator view life = case life of Refl impossible
continuationLengthReloading
  (MkFiber component parent retiredFlag table
    (Reloading actualRemaining actualAccumulator actualView)) remaining
  accumulator view life = case life of Refl => Refl
continuationLengthReloading
  (MkFiber component parent retiredFlag table (Active actualAccumulator actualView))
  remaining accumulator view life = case life of Refl impossible
continuationLengthReloading
  (MkFiber component parent retiredFlag table
    (Unloading actualAccumulator actualView outcome)) remaining accumulator view
  life = case life of Refl impossible

0 continuationSetLifecycleReloading :
  (fiber : Fiber name key value world error) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  fiberContinuationLength
    (setFiberLifecycle fiber (Reloading remaining accumulator view)) =
      Just (length remaining)
continuationSetLifecycleReloading
  (MkFiber component parent retiredFlag table lifecycle) remaining accumulator
  view = Refl

0 continuationSetLifecycleActive :
  (fiber : Fiber name key value world error) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  fiberContinuationLength (setFiberLifecycle fiber (Active accumulator view)) =
    Nothing
continuationSetLifecycleActive
  (MkFiber component parent retiredFlag table lifecycle) accumulator view = Refl

0 continuationSetLifecycleUnloading :
  (fiber : Fiber name key value world error) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  (outcome : Maybe error) ->
  fiberContinuationLength
    (setFiberLifecycle fiber (Unloading accumulator view outcome)) = Nothing
continuationSetLifecycleUnloading
  (MkFiber component parent retiredFlag table lifecycle) accumulator view
  outcome = Refl

0 continuationSetRuntimeReloading :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value (componentProvisions (fiberComponent fiber))) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  fiberContinuationLength
    (setFiberRuntime fiber table (Reloading remaining accumulator view)) =
      Just (length remaining)
continuationSetRuntimeReloading
  (MkFiber component parent retiredFlag oldTable lifecycle) table remaining
  accumulator view = Refl

0 continuationSetRuntimeStopped :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value (componentProvisions (fiberComponent fiber))) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  NotReloading life ->
  fiberContinuationLength (setFiberRuntime fiber table life) = Nothing
continuationSetRuntimeStopped
  (MkFiber component parent retiredFlag oldTable lifecycle) table
  (Inactive outcome) NotInactive = Refl
continuationSetRuntimeStopped
  (MkFiber component parent retiredFlag oldTable lifecycle) table
  (Active accumulator view) NotActive = Refl
continuationSetRuntimeStopped
  (MkFiber component parent retiredFlag oldTable lifecycle) table
  (Unloading accumulator view outcome) NotUnloading = Refl

0 retiredAfterRetire : (fiber : Fiber name key value world error) ->
  retired (retireFiber fiber) = True
retiredAfterRetire (MkFiber component parent retiredFlag table lifecycle) = Refl

0 retiredAfterSetLifecycle :
  (fiber : Fiber name key value world error) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  retired (setFiberLifecycle fiber life) = retired fiber
retiredAfterSetLifecycle
  (MkFiber component parent retiredFlag table lifecycle) life = Refl

0 retiredAfterSetRuntime :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value (componentProvisions (fiberComponent fiber))) ->
  (life : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  retired (setFiberRuntime fiber table life) = retired fiber
retiredAfterSetRuntime
  (MkFiber component parent retiredFlag oldTable lifecycle) table life = Refl

public export
data RegistryLocalUpdate :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  Registry name key value world error -> Registry name key value world error ->
  Type where
  LocalInsert : (fiber : Fiber name key value world error) ->
    (absent : lookupFiber @{nameEq} actor source = Nothing) ->
    {auto insertedContinuationEmpty : fiberContinuationLength fiber = Nothing} ->
    RegistryLocalUpdate name key world error value nameEq actor source
      (insertBinding @{nameEq} actor fiber source absent)
  LocalReplace : (fiber : Fiber name key value world error) ->
    {oldFiber : Fiber name key value world error} ->
    {auto oldFound : lookupFiber @{nameEq} actor source = Just oldFiber} ->
    {auto staticComponent : fiberComponent fiber = fiberComponent oldFiber} ->
    {auto staticParent : fiberParent fiber = fiberParent oldFiber} ->
    {auto retirementUpdate : RetirementUpdate oldFiber fiber} ->
    {auto continuationUpdate : ContinuationUpdate oldFiber fiber} ->
    RegistryLocalUpdate name key world error value nameEq actor source
      (replaceBinding @{nameEq} actor fiber source)
  LocalDelete :
    {oldFiber : Fiber name key value world error} ->
    {auto oldFound : lookupFiber @{nameEq} actor source = Just oldFiber} ->
    {auto noChild : hasChild @{nameEq} {key = key} {value = value}
      {world = world} {error = error} actor source = False} ->
    RegistryLocalUpdate name key world error value nameEq actor source
      (deleteBinding @{nameEq} actor source)

public export
0 registryLocalUpdateForeign :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (selected = actor) ->
  (source : Registry name key value world error) ->
  {target : Registry name key value world error} ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} selected target = lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} selected source
registryLocalUpdateForeign nameEq selected actor distinct source
  (LocalInsert fiber absent) =
    lookupInsertOther selected actor distinct fiber source absent
registryLocalUpdateForeign nameEq selected actor distinct source
  (LocalReplace fiber) = lookupReplaceOther selected actor distinct fiber source
registryLocalUpdateForeign nameEq selected actor distinct source LocalDelete =
  lookupDeleteOther selected actor distinct source

0 noChildFromRemovalGuard :
  (retiredFlag, inactiveFlag, childPresent : Bool) ->
  retiredFlag && inactiveFlag && not childPresent = True ->
  childPresent = False
noChildFromRemovalGuard retiredFlag inactiveFlag False valid = Refl
noChildFromRemovalGuard False inactiveFlag True valid =
  case valid of Refl impossible
noChildFromRemovalGuard True False True valid =
  case valid of Refl impossible
noChildFromRemovalGuard True True True valid =
  case valid of Refl impossible

public export
record SystemLocalUpdate
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (before, afterState : SystemState name key value world error) where
  constructor MkSystemLocalUpdate
  systemRegistryUpdate : RegistryLocalUpdate name key world error value nameEq
    actor (registry before) (registry afterState)

public export
0 systemLocalUpdateForeign :
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (selected = actor) ->
  (before, afterState : SystemState name key value world error) ->
  SystemLocalUpdate name key world error value nameEq actor before afterState ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} selected (registry afterState) =
    lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} selected (registry before)
systemLocalUpdateForeign nameEq selected actor distinct before afterState update =
  registryLocalUpdateForeign nameEq selected actor distinct (registry before)
    (systemRegistryUpdate update)



public export
0 applyActionLocalUpdate :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  SystemLocalUpdate name key world error value nameEq (actionOwner action)
    before afterState
applyActionLocalUpdate {name} {key} {world} {error} {value}
  nameEq keyEq (OInsert n parent component)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  applyActionLocalUpdate {name} {key} {world} {error} {value}
    nameEq keyEq (OInsert n parent component)
    before@(MkSystemState ambient fibers) afterState tag equation | False =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate {name} {key} {world} {error} {value}
    nameEq keyEq (OInsert n parent component)
    before@(MkSystemState ambient fibers) afterState tag equation | True
    with (setFresh @{nameEq} n (freshFiber component parent) fibers) proof inserted
    applyActionLocalUpdate {name} {key} {world} {error} {value}
      nameEq keyEq (OInsert n parent component)
      before@(MkSystemState ambient fibers) afterState tag equation | True |
      Nothing = void (nothingIsNotJust equation)
    applyActionLocalUpdate {name} {key} {world} {error} {value}
      nameEq keyEq (OInsert n parent component)
      before@(MkSystemState ambient fibers) afterState tag equation | True |
      Just applied = case justInjective equation of
        Refl => rewrite setFreshAfter nameEq n (freshFiber component parent)
          fibers applied inserted in
          MkSystemLocalUpdate (LocalInsert (freshFiber component parent)
            (setFreshAbsent nameEq n (freshFiber component parent)
              fibers applied inserted) @{Refl})
applyActionLocalUpdate nameEq keyEq (ORetire n)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} n fibers) proof found
  applyActionLocalUpdate nameEq keyEq (ORetire n)
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate nameEq keyEq (ORetire n)
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber =
      case justInjective equation of
        Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
          @{fiberComponentRetire fiber} @{fiberParentRetireHint fiber}
          @{RetirementApplied (retiredAfterRetire fiber)}
          @{ContinuationPreserved (continuationAfterRetire fiber)}
          (retireFiber fiber))
applyActionLocalUpdate nameEq keyEq (ORemove n)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} n fibers) proof found
  applyActionLocalUpdate nameEq keyEq (ORemove n)
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate nameEq keyEq (ORemove n)
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (retired fiber && isInactive (fiberLifecycle fiber) &&
      not (hasChild @{nameEq} n fibers)) proof removable
    applyActionLocalUpdate nameEq keyEq (ORemove n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      False = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (ORemove n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      True = case justInjective equation of
        Refl => MkSystemLocalUpdate
          (LocalDelete {oldFiber = fiber} @{found}
            @{noChildFromRemovalGuard (retired fiber)
              (isInactive (fiberLifecycle fiber)) (hasChild @{nameEq} n fibers)
              removable})
applyActionLocalUpdate nameEq keyEq (LBegin n)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} n fibers) proof found
  applyActionLocalUpdate nameEq keyEq (LBegin n)
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate nameEq keyEq (LBegin n)
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    applyActionLocalUpdate nameEq keyEq (LBegin n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive Nothing with (targetFiber @{nameEq} @{keyEq} fiber fibers)
      applyActionLocalUpdate nameEq keyEq (LBegin n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Inactive Nothing | Nothing = void (nothingIsNotJust equation)
      applyActionLocalUpdate nameEq keyEq (LBegin n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Inactive Nothing | Just view = case justInjective equation of
          Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
            @{fiberComponentSetLifecycle fiber
              (Reloading (componentProgram (fiberComponent fiber)) id view)}
            @{fiberParentSetLifecycleHint fiber
              (Reloading (componentProgram (fiberComponent fiber)) id view)}
            @{RetirementStable (retiredAfterSetLifecycle fiber _)}
            @{ContinuationRestarted
              (continuationSetLifecycleReloading fiber
                (componentProgram (fiberComponent fiber)) id view)}
            (setFiberLifecycle fiber
              (Reloading (componentProgram (fiberComponent fiber)) id view)))
    applyActionLocalUpdate nameEq keyEq (LBegin n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive (Just err) = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LBegin n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LBegin n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LBegin n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
applyActionLocalUpdate nameEq keyEq (LAdvance n)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} n fibers) proof found
  applyActionLocalUpdate nameEq keyEq (LAdvance n)
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate nameEq keyEq (LAdvance n)
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber) proof life
    applyActionLocalUpdate nameEq keyEq (LAdvance n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LAdvance n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LAdvance n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LAdvance n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      applyActionLocalUpdate nameEq keyEq (LAdvance n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Reloading [] accumulator view | True = case justInjective equation of
          Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
            @{fiberComponentSetLifecycle fiber (Active accumulator view)}
            @{fiberParentSetLifecycleHint fiber (Active accumulator view)}
            @{RetirementStable (retiredAfterSetLifecycle fiber _)}
            @{ContinuationStopped
              (continuationSetLifecycleActive fiber accumulator view)}
            (setFiberLifecycle fiber (Active accumulator view)))
      applyActionLocalUpdate nameEq keyEq (LAdvance n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Reloading [] accumulator view | False = case justInjective equation of
          Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
            @{fiberComponentSetLifecycle fiber (Unloading accumulator view Nothing)}
            @{fiberParentSetLifecycleHint fiber (Unloading accumulator view Nothing)}
            @{RetirementStable (retiredAfterSetLifecycle fiber _)}
            @{ContinuationStopped
              (continuationSetLifecycleUnloading fiber accumulator view Nothing)}
            (setFiberLifecycle fiber (Unloading accumulator view Nothing)))
    applyActionLocalUpdate nameEq keyEq (LAdvance n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading (step :: rest) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies (fiberComponent fiber)))
        view fibers)
      applyActionLocalUpdate nameEq keyEq (LAdvance n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Reloading (step :: rest) accumulator view | Nothing =
          void (nothingIsNotJust equation)
      applyActionLocalUpdate nameEq keyEq (LAdvance n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Reloading (step :: rest) accumulator view | Just capability
        with (runStepEffect step capability
          (MkLocalState ambient (fiberTable fiber)))
        applyActionLocalUpdate nameEq keyEq (LAdvance n)
          before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
          Reloading (step :: rest) accumulator view | Just capability | Left err =
            case justInjective equation of
              Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
                @{fiberComponentSetLifecycle fiber
                  (Unloading accumulator view (Just err))}
                @{fiberParentSetLifecycleHint fiber
                  (Unloading accumulator view (Just err))}
                @{RetirementStable (retiredAfterSetLifecycle fiber _)}
                @{ContinuationStopped
                  (continuationSetLifecycleUnloading fiber accumulator view
                    (Just err))}
                (setFiberLifecycle fiber
                  (Unloading accumulator view (Just err))))
        applyActionLocalUpdate nameEq keyEq (LAdvance n)
          before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
          Reloading (step :: rest) accumulator view | Just capability |
          Right (localAfter, undo)
          with (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
          applyActionLocalUpdate nameEq keyEq (LAdvance n)
            before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
            Reloading (step :: rest) accumulator view | Just capability |
            Right (localAfter, undo) | False = case justInjective equation of
              Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
                @{fiberComponentSetRuntime fiber _ _}
                @{fiberParentSetRuntimeHint fiber (localTable localAfter)
                  (Unloading (accumulator . undo) view Nothing)}
                @{RetirementStable (retiredAfterSetRuntime fiber _ _)}
                @{ContinuationStopped
                  (continuationSetRuntimeStopped fiber (localTable localAfter)
                    (Unloading (accumulator . undo) view Nothing) NotUnloading)}
                (setFiberRuntime fiber (localTable localAfter)
                  (Unloading (accumulator . undo) view Nothing)))
          applyActionLocalUpdate nameEq keyEq (LAdvance n)
            before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
            Reloading (step :: []) accumulator view | Just capability |
            Right (localAfter, undo) | True = case justInjective equation of
              Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
                @{fiberComponentSetRuntime fiber _ _}
                @{fiberParentSetRuntimeHint fiber (localTable localAfter)
                  (Active (accumulator . undo) view)}
                @{RetirementStable (retiredAfterSetRuntime fiber _ _)}
                @{ContinuationStopped
                  (continuationSetRuntimeStopped fiber (localTable localAfter)
                    (Active (accumulator . undo) view) NotActive)}
                (setFiberRuntime fiber (localTable localAfter)
                  (Active (accumulator . undo) view)))
          applyActionLocalUpdate nameEq keyEq (LAdvance n)
            before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
            Reloading (step :: next :: more) accumulator view | Just capability |
            Right (localAfter, undo) | True = case justInjective equation of
              Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
                @{fiberComponentSetRuntime fiber _ _}
                @{fiberParentSetRuntimeHint fiber (localTable localAfter)
                  (Reloading (next :: more) (accumulator . undo) view)}
                @{RetirementStable (retiredAfterSetRuntime fiber _ _)}
                @{ContinuationAdvanced (length (next :: more))
                  (continuationLengthReloading fiber (step :: next :: more)
                    accumulator view life)
                  (continuationSetRuntimeReloading fiber (localTable localAfter)
                    (next :: more) (accumulator . undo) view)}
                (setFiberRuntime fiber (localTable localAfter)
                  (Reloading (next :: more) (accumulator . undo) view)))
applyActionLocalUpdate nameEq keyEq (LDivert n)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} n fibers) proof found
  applyActionLocalUpdate nameEq keyEq (LDivert n)
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate nameEq keyEq (LDivert n)
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    applyActionLocalUpdate nameEq keyEq (LDivert n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      applyActionLocalUpdate nameEq keyEq (LDivert n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Reloading remaining accumulator view | True =
          void (nothingIsNotJust equation)
      applyActionLocalUpdate nameEq keyEq (LDivert n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Reloading remaining accumulator view | False = case justInjective equation of
          Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
            @{fiberComponentSetLifecycle fiber (Unloading accumulator view Nothing)}
            @{fiberParentSetLifecycleHint fiber (Unloading accumulator view Nothing)}
            @{RetirementStable (retiredAfterSetLifecycle fiber _)}
            @{ContinuationStopped
              (continuationSetLifecycleUnloading fiber accumulator view Nothing)}
            (setFiberLifecycle fiber (Unloading accumulator view Nothing)))
    applyActionLocalUpdate nameEq keyEq (LDivert n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LDivert n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LDivert n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
applyActionLocalUpdate nameEq keyEq (LLeave n)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} n fibers) proof found
  applyActionLocalUpdate nameEq keyEq (LLeave n)
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate nameEq keyEq (LLeave n)
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    applyActionLocalUpdate nameEq keyEq (LLeave n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      applyActionLocalUpdate nameEq keyEq (LLeave n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Active accumulator view | True = void (nothingIsNotJust equation)
      applyActionLocalUpdate nameEq keyEq (LLeave n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Active accumulator view | False = case justInjective equation of
          Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
            @{fiberComponentSetLifecycle fiber (Unloading accumulator view Nothing)}
            @{fiberParentSetLifecycleHint fiber (Unloading accumulator view Nothing)}
            @{RetirementStable (retiredAfterSetLifecycle fiber _)}
            @{ContinuationStopped
              (continuationSetLifecycleUnloading fiber accumulator view Nothing)}
            (setFiberLifecycle fiber (Unloading accumulator view Nothing)))
    applyActionLocalUpdate nameEq keyEq (LLeave n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LLeave n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LLeave n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
applyActionLocalUpdate nameEq keyEq (LUnload n)
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} n fibers) proof found
  applyActionLocalUpdate nameEq keyEq (LUnload n)
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  applyActionLocalUpdate nameEq keyEq (LUnload n)
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    applyActionLocalUpdate nameEq keyEq (LUnload n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome
      with (relied @{nameEq} n fibers)
      applyActionLocalUpdate nameEq keyEq (LUnload n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | True = void (nothingIsNotJust equation)
      applyActionLocalUpdate nameEq keyEq (LUnload n)
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | False = case justInjective equation of
          Refl => MkSystemLocalUpdate (LocalReplace {oldFiber = fiber} @{found}
            @{fiberComponentSetRuntime fiber _ _}
            @{fiberParentSetRuntimeHint fiber
              (localTable (accumulator (MkLocalState ambient (fiberTable fiber))))
              (Inactive outcome)}
            @{RetirementStable (retiredAfterSetRuntime fiber _ _)}
            @{ContinuationStopped
              (continuationSetRuntimeStopped fiber
                (localTable
                  (accumulator (MkLocalState ambient (fiberTable fiber))))
                (Inactive outcome) NotInactive)}
            (setFiberRuntime fiber
              (localTable (accumulator (MkLocalState ambient (fiberTable fiber))))
              (Inactive outcome)))
    applyActionLocalUpdate nameEq keyEq (LUnload n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LUnload n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    applyActionLocalUpdate nameEq keyEq (LUnload n)
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)

public export
record CommittedSnapshot
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name) (providers : List name)
  (state : SystemState name key value world error) where
  constructor MkCommittedSnapshot
  committedFiber : Fiber name key value world error
  committedLookup : lookupFiber @{nameEq} selected (registry state) =
    Just committedFiber
  committedView : View name
    (dependencies (componentDependencies (fiberComponent committedFiber)))
  committedLifecycle : committed (fiberLifecycle committedFiber) =
    Just committedView
  committedProviderNames : viewProviders committedView = providers

0 committedProvidersAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  (selected : name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (oldFiber, nextFiber : Fiber name key value world error) ->
  (view : View name (dependencies
    (componentDependencies (fiberComponent nextFiber)))) ->
  (providers : List name) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} selected fibers = Just oldFiber ->
  committed (fiberLifecycle nextFiber) = Just view ->
  viewProviders view = providers ->
  committedProvidersAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected
    (MkSystemState ambient (replaceBinding @{nameEq} selected nextFiber fibers)) =
    Just providers
committedProvidersAfterReplace selected ambient fibers oldFiber nextFiber view
  providers found lifecycle providerNames =
  rewrite lookupReplacedFiber selected oldFiber nextFiber fibers found in
  rewrite lifecycle in rewrite providerNames in Refl

public export
0 committedSnapshotFrom :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) -> (providers : List name) ->
  (state : SystemState name key value world error) ->
  committedProvidersAt @{nameEq} selected state = Just providers ->
  CommittedSnapshot name key world error value nameEq selected providers state
committedSnapshotFrom {name} {key} {world} {error} {value}
  nameEq selected providers state present
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  committedSnapshotFrom {name} {key} {world} {error} {value}
    nameEq selected providers state present | Nothing =
      void (nothingIsNotJust present)
  committedSnapshotFrom {name} {key} {world} {error} {value}
    nameEq selected providers state present | Just fiber
    with (committed (fiberLifecycle fiber)) proof lifecycle
    committedSnapshotFrom {name} {key} {world} {error} {value}
      nameEq selected providers state present | Just fiber | Nothing =
        void (nothingIsNotJust present)
    committedSnapshotFrom {name} {key} {world} {error} {value}
      nameEq selected providers state present | Just fiber | Just view =
        MkCommittedSnapshot fiber found view lifecycle (justInjective present)

public export
0 committedSnapshotEquation :
  (snapshot : CommittedSnapshot name key world error value nameEq selected
    providers state) ->
  committedProvidersAt @{nameEq} selected state = Just providers
committedSnapshotEquation snapshot = rewrite committedLookup snapshot in
  rewrite committedLifecycle snapshot in rewrite committedProviderNames snapshot in
  Refl

0 committedProvidersOInsertSelected :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  committedProvidersAt @{nameEq} selected before = Just providers ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersOInsertSelected {name} {key} {world} {error} {value}
  nameEq keyEq selected parent component providers
  (MkSystemState ambient fibers) afterState tag beforeCommitted equation
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  committedProvidersOInsertSelected {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component providers
    (MkSystemState ambient fibers) afterState tag beforeCommitted equation |
    False = void (nothingIsNotJust equation)
  committedProvidersOInsertSelected {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component providers
    (MkSystemState ambient fibers) afterState tag beforeCommitted equation |
    True with (setFresh @{nameEq} selected (freshFiber component parent) fibers)
      proof inserted
    committedProvidersOInsertSelected {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component providers
      (MkSystemState ambient fibers) afterState tag beforeCommitted equation |
      True | Nothing = void (nothingIsNotJust equation)
    committedProvidersOInsertSelected {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component providers
      (MkSystemState ambient fibers) afterState tag beforeCommitted equation |
      True | Just applied =
        let snapshot = committedSnapshotFrom nameEq selected providers (MkSystemState ambient fibers)
              beforeCommitted
            absent = setFreshAbsent nameEq selected (freshFiber component parent)
              fibers applied inserted
        in void (nothingIsNotJust
          (trans (sym absent) (committedLookup snapshot)))

0 committedProvidersORetireSelected :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  committedProvidersAt @{nameEq} selected before = Just providers ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersORetireSelected nameEq keyEq selected providers
  before@(MkSystemState ambient fibers) afterState tag beforeCommitted equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  committedProvidersORetireSelected nameEq keyEq selected providers
    before@(MkSystemState ambient fibers) afterState tag beforeCommitted equation |
    Nothing = void (nothingIsNotJust beforeCommitted)
  committedProvidersORetireSelected nameEq keyEq selected providers
    before@(MkSystemState ambient fibers) afterState tag beforeCommitted equation |
    Just fiber@(MkFiber component parent retired table lifecycle)
    with (committed lifecycle) proof lifecycleCommitted
    committedProvidersORetireSelected nameEq keyEq selected providers
      before@(MkSystemState ambient fibers) afterState tag beforeCommitted equation |
      Just fiber@(MkFiber component parent retired table lifecycle) | Nothing =
        void (nothingIsNotJust beforeCommitted)
    committedProvidersORetireSelected nameEq keyEq selected providers
      before@(MkSystemState ambient fibers) afterState tag beforeCommitted equation |
      Just fiber@(MkFiber component parent retired table lifecycle) | Just view =
        case justInjective equation of
          Refl => committedProvidersAfterReplace selected ambient fibers
            (MkFiber component parent retired table lifecycle)
            (retireFiber (MkFiber component parent retired table lifecycle))
            view providers found lifecycleCommitted
            (justInjective beforeCommitted)

0 committedProvidersORemoveSelected :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  committedProvidersAt @{nameEq} selected before = Just providers ->
  applyAction @{nameEq} @{keyEq} (ORemove selected) before =
    Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersORemoveSelected nameEq keyEq selected providers
  before afterState tag beforeCommitted equation
  with (lookupFiber @{nameEq} selected (registry before))
  committedProvidersORemoveSelected nameEq keyEq selected providers
    before afterState tag beforeCommitted equation | Nothing =
      void (nothingIsNotJust beforeCommitted)
  committedProvidersORemoveSelected nameEq keyEq selected providers
    before afterState tag beforeCommitted equation | Just fiber
    with (fiberLifecycle fiber)
    committedProvidersORemoveSelected nameEq keyEq selected providers
      before afterState tag beforeCommitted equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust beforeCommitted)
    committedProvidersORemoveSelected nameEq keyEq selected providers
      before afterState tag beforeCommitted equation | Just fiber |
      Reloading remaining accumulator view with (retired fiber)
      committedProvidersORemoveSelected nameEq keyEq selected providers
        before afterState tag beforeCommitted equation | Just fiber |
        Reloading remaining accumulator view | False = void (nothingIsNotJust equation)
      committedProvidersORemoveSelected nameEq keyEq selected providers
        before afterState tag beforeCommitted equation | Just fiber |
        Reloading remaining accumulator view | True = void (nothingIsNotJust equation)
    committedProvidersORemoveSelected nameEq keyEq selected providers
      before afterState tag beforeCommitted equation | Just fiber |
      Active accumulator view with (retired fiber)
      committedProvidersORemoveSelected nameEq keyEq selected providers
        before afterState tag beforeCommitted equation | Just fiber |
        Active accumulator view | False = void (nothingIsNotJust equation)
      committedProvidersORemoveSelected nameEq keyEq selected providers
        before afterState tag beforeCommitted equation | Just fiber |
        Active accumulator view | True = void (nothingIsNotJust equation)
    committedProvidersORemoveSelected nameEq keyEq selected providers
      before afterState tag beforeCommitted equation | Just fiber |
      Unloading accumulator view outcome with (retired fiber)
      committedProvidersORemoveSelected nameEq keyEq selected providers
        before afterState tag beforeCommitted equation | Just fiber |
        Unloading accumulator view outcome | False = void (nothingIsNotJust equation)
      committedProvidersORemoveSelected nameEq keyEq selected providers
        before afterState tag beforeCommitted equation | Just fiber |
        Unloading accumulator view outcome | True = void (nothingIsNotJust equation)

0 committedProvidersLBeginSelected :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  committedProvidersAt @{nameEq} selected before = Just providers ->
  applyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersLBeginSelected nameEq keyEq selected providers before afterState
  tag beforeCommitted equation
  with (lookupFiber @{nameEq} selected (registry before))
  committedProvidersLBeginSelected nameEq keyEq selected providers before afterState
    tag beforeCommitted equation | Nothing = void (nothingIsNotJust beforeCommitted)
  committedProvidersLBeginSelected nameEq keyEq selected providers before afterState
    tag beforeCommitted equation | Just fiber
    with (fiberLifecycle fiber)
    committedProvidersLBeginSelected nameEq keyEq selected providers before afterState
      tag beforeCommitted equation | Just fiber | Inactive outcome =
        void (nothingIsNotJust beforeCommitted)
    committedProvidersLBeginSelected nameEq keyEq selected providers before afterState
      tag beforeCommitted equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    committedProvidersLBeginSelected nameEq keyEq selected providers before afterState
      tag beforeCommitted equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    committedProvidersLBeginSelected nameEq keyEq selected providers before afterState
      tag beforeCommitted equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)

0 providerNamesFromCommittedViewSnapshot :
  (snapshot : CommittedSnapshot name key world error value nameEq selected
    providers state) ->
  (fiber : Fiber name key value world error) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  committed (fiberLifecycle fiber) = Just view ->
  viewProviders view = providers
providerNamesFromCommittedViewSnapshot snapshot fiber view found currentCommitted =
  case justInjective (trans (sym (committedLookup snapshot)) found) of
    Refl =>
      let 0 sameView : (view = committedView snapshot)
          sameView = justInjective
            (trans (sym currentCommitted) (committedLifecycle snapshot))
      in trans (cong viewProviders sameView) (committedProviderNames snapshot)

0 providerNamesFromReloadingSnapshot :
  (snapshot : CommittedSnapshot name key world error value nameEq selected
    providers state) ->
  (fiber : Fiber name key value world error) ->
  {remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))} ->
  {accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))} ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  viewProviders view = providers
providerNamesFromReloadingSnapshot snapshot fiber found life =
  providerNamesFromCommittedViewSnapshot snapshot fiber view found
    (cong committed life)

0 committedProvidersLAdvanceSelected :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  CommittedSnapshot name key world error value nameEq selected providers before ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersLAdvanceSelected nameEq keyEq selected providers
  (MkSystemState ambient fibers) afterState tag snapshot equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  committedProvidersLAdvanceSelected nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot equation |
    Nothing = void (nothingIsNotJust equation)
  committedProvidersLAdvanceSelected nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot equation |
    Just fiber with (fiberLifecycle fiber) proof lifecycle
    committedProvidersLAdvanceSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation |
      Just fiber | Inactive outcome = void (nothingIsNotJust equation)
    committedProvidersLAdvanceSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation |
      Just fiber | Active accumulator view = void (nothingIsNotJust equation)
    committedProvidersLAdvanceSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation |
      Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust equation)
    committedProvidersLAdvanceSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation |
      Just fiber | Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      committedProvidersLAdvanceSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation |
        Just fiber | Reloading [] accumulator view | True =
          case justInjective equation of
            Refl => trans (committedActiveAfterReplace selected fiber found)
                              (cong Just (providerNamesFromReloadingSnapshot snapshot fiber found lifecycle))
      committedProvidersLAdvanceSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation |
        Just fiber | Reloading [] accumulator view | False =
          case justInjective equation of
            Refl => trans (committedUnloadingAfterReplace selected fiber found)
                              (cong Just (providerNamesFromReloadingSnapshot snapshot fiber found lifecycle))
    committedProvidersLAdvanceSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation |
      Just fiber | Reloading (step :: rest) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies (fiberComponent fiber)))
        view fibers)
      committedProvidersLAdvanceSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation |
        Just fiber | Reloading (step :: rest) accumulator view | Nothing =
          void (nothingIsNotJust equation)
      committedProvidersLAdvanceSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation |
        Just fiber | Reloading (step :: rest) accumulator view | Just capability
        with (runStepEffect step capability
          (MkLocalState ambient (fiberTable fiber)))
        committedProvidersLAdvanceSelected nameEq keyEq selected providers
          (MkSystemState ambient fibers) afterState tag snapshot equation |
          Just fiber | Reloading (step :: rest) accumulator view |
          Just capability | Left err = case justInjective equation of
            Refl => trans (committedUnloadingAfterReplace selected fiber found)
                              (cong Just (providerNamesFromReloadingSnapshot snapshot fiber found lifecycle))
        committedProvidersLAdvanceSelected nameEq keyEq selected providers
          (MkSystemState ambient fibers) afterState tag snapshot equation |
          Just fiber | Reloading (step :: rest) accumulator view |
          Just capability | Right (localAfter, undo)
          with (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
          committedProvidersLAdvanceSelected nameEq keyEq selected providers
            (MkSystemState ambient fibers) afterState tag snapshot equation |
            Just fiber | Reloading (step :: rest) accumulator view |
            Just capability | Right (localAfter, undo) | False =
              case justInjective equation of
                Refl => trans (committedUnloadingAfterReplace selected fiber found)
                              (cong Just (providerNamesFromReloadingSnapshot snapshot fiber found lifecycle))
          committedProvidersLAdvanceSelected nameEq keyEq selected providers
            (MkSystemState ambient fibers) afterState tag snapshot equation |
            Just fiber | Reloading (step :: []) accumulator view |
            Just capability | Right (localAfter, undo) | True =
              case justInjective equation of
                Refl => trans (committedActiveAfterReplace selected fiber found)
                              (cong Just (providerNamesFromReloadingSnapshot snapshot fiber found lifecycle))
          committedProvidersLAdvanceSelected nameEq keyEq selected providers
            (MkSystemState ambient fibers) afterState tag snapshot equation |
            Just fiber | Reloading (step :: next :: more) accumulator view |
            Just capability | Right (localAfter, undo) | True =
              case justInjective equation of
                Refl => trans (committedReloadingAfterReplace selected fiber found)
                              (cong Just (providerNamesFromReloadingSnapshot snapshot fiber found lifecycle))

0 committedProvidersLDivertSelected :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (snapshot : CommittedSnapshot name key world error value nameEq selected
    providers before) ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersLDivertSelected nameEq keyEq selected providers
  (MkSystemState ambient fibers) afterState tag snapshot equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  committedProvidersLDivertSelected nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot equation | Nothing =
      void (nothingIsNotJust equation)
  committedProvidersLDivertSelected nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber
    with (fiberLifecycle fiber) proof lifecycle
    committedProvidersLDivertSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    committedProvidersLDivertSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    committedProvidersLDivertSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
    committedProvidersLDivertSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      committedProvidersLDivertSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
        Reloading remaining accumulator view | True =
          void (nothingIsNotJust equation)
      committedProvidersLDivertSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
        Reloading remaining accumulator view | False =
          case justInjective equation of
            Refl => trans (committedUnloadingAfterReplace selected fiber found)
              (cong Just (providerNamesFromReloadingSnapshot snapshot fiber found
                lifecycle))

0 committedProvidersLLeaveSelected :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (snapshot : CommittedSnapshot name key world error value nameEq selected
    providers before) ->
  applyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersLLeaveSelected nameEq keyEq selected providers
  (MkSystemState ambient fibers) afterState tag snapshot equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  committedProvidersLLeaveSelected nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot equation | Nothing =
      void (nothingIsNotJust equation)
  committedProvidersLLeaveSelected nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber
    with (fiberLifecycle fiber) proof lifecycle
    committedProvidersLLeaveSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    committedProvidersLLeaveSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    committedProvidersLLeaveSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
    committedProvidersLLeaveSelected nameEq keyEq selected providers
      (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
      Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      committedProvidersLLeaveSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
        Active accumulator view | True = void (nothingIsNotJust equation)
      committedProvidersLLeaveSelected nameEq keyEq selected providers
        (MkSystemState ambient fibers) afterState tag snapshot equation | Just fiber |
        Active accumulator view | False = case justInjective equation of
          Refl => trans (committedUnloadingAfterReplace selected fiber found)
            (cong Just (providerNamesFromCommittedViewSnapshot snapshot fiber view
              found (cong committed lifecycle)))

0 inactiveAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} -> DecEq name =>
  {fibers : Registry name key value world error} -> {worldValue : world} ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  {table : OwnedTable key value (componentProvisions (fiberComponent fiber))} ->
  {outcome : Maybe error} ->
  lookupFiber selected fibers = Just fiber ->
  installedAt {key = key} {value = value} {world = world} {error = error} selected
    (MkSystemState worldValue
      (replaceBinding selected
        (setFiberRuntime fiber table (Inactive outcome)) fibers)) = False
inactiveAfterReplace {table} {outcome} selected
  fiber@(MkFiber component parent retired oldTable oldLife) found =
  rewrite lookupReplacedFiber selected fiber
    (setFiberRuntime fiber table (Inactive outcome)) fibers found in Refl

0 successfulLUnloadEndsUninstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected afterState = False
successfulLUnloadEndsUninstalled nameEq keyEq selected
  (MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  successfulLUnloadEndsUninstalled nameEq keyEq selected
    (MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  successfulLUnloadEndsUninstalled nameEq keyEq selected
    (MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    successfulLUnloadEndsUninstalled nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    successfulLUnloadEndsUninstalled nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    successfulLUnloadEndsUninstalled nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    successfulLUnloadEndsUninstalled nameEq keyEq selected
      (MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome
      with (relied @{nameEq} selected fibers)
      successfulLUnloadEndsUninstalled nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | True = void (nothingIsNotJust equation)
      successfulLUnloadEndsUninstalled nameEq keyEq selected
        (MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | False = case justInjective equation of
          Refl => inactiveAfterReplace selected fiber found

public export
0 committedProvidersForeignAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> Not (selected = actionOwner action) ->
  committedProvidersAt @{nameEq} selected before = Just providers ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersForeignAction {name} {key} {world} {error} {value}
  nameEq keyEq selected providers action before afterState tag distinct
  beforeCommitted equation =
  let snapshot = committedSnapshotFrom nameEq selected providers before
        beforeCommitted
      0 foreignLookup = systemLocalUpdateForeign nameEq selected
        (actionOwner action) distinct before afterState
        (applyActionLocalUpdate nameEq keyEq action before afterState tag equation)
      0 targetLookup = trans foreignLookup (committedLookup snapshot)
  in rewrite targetLookup in rewrite committedLifecycle snapshot in
    rewrite committedProviderNames snapshot in Refl

public export
0 committedProvidersSelectedAction :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> actionOwner action = selected ->
  (snapshot : CommittedSnapshot name key world error value nameEq selected
    providers before) ->
  installedAt @{nameEq} selected afterState = True ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  committedProvidersAt @{nameEq} selected afterState = Just providers
committedProvidersSelectedAction nameEq keyEq selected providers
  (OInsert selected parent component) before afterState tag Refl snapshot
  targetInstalled equation = committedProvidersOInsertSelected nameEq keyEq
    selected parent component providers before afterState tag
    (committedSnapshotEquation snapshot) equation
committedProvidersSelectedAction nameEq keyEq selected providers
  (ORetire selected) before afterState tag Refl snapshot targetInstalled equation =
    committedProvidersORetireSelected nameEq keyEq selected providers before
      afterState tag (committedSnapshotEquation snapshot) equation
committedProvidersSelectedAction nameEq keyEq selected providers
  (ORemove selected) before afterState tag Refl snapshot targetInstalled equation =
    committedProvidersORemoveSelected nameEq keyEq selected providers before
      afterState tag (committedSnapshotEquation snapshot) equation
committedProvidersSelectedAction nameEq keyEq selected providers
  (LBegin selected) before afterState tag Refl snapshot targetInstalled equation =
    committedProvidersLBeginSelected nameEq keyEq selected providers before
      afterState tag (committedSnapshotEquation snapshot) equation
committedProvidersSelectedAction nameEq keyEq selected providers
  (LAdvance selected) before afterState tag Refl snapshot targetInstalled equation =
    committedProvidersLAdvanceSelected nameEq keyEq selected providers before
      afterState tag snapshot equation
committedProvidersSelectedAction nameEq keyEq selected providers
  (LDivert selected) before afterState tag Refl snapshot targetInstalled equation =
    committedProvidersLDivertSelected nameEq keyEq selected providers
      before afterState tag snapshot equation
committedProvidersSelectedAction nameEq keyEq selected providers
  (LLeave selected) before afterState tag Refl snapshot targetInstalled equation =
    committedProvidersLLeaveSelected nameEq keyEq selected providers
      before afterState tag snapshot equation
committedProvidersSelectedAction nameEq keyEq selected providers
  (LUnload selected) before afterState tag Refl snapshot targetInstalled equation =
    void (falseIsNotTrue
      (trans (sym (successfulLUnloadEndsUninstalled nameEq keyEq selected before
        afterState tag equation)) targetInstalled))

public export
0 installedTraceStart :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {start, finalState : SystemState name key value world error} ->
  {transitions : Transitions start finalState} ->
  (trace : InstalledTrace name key world error value nameEq keyEq selected
    transitions) -> installedAt @{nameEq} selected start = True
installedTraceStart (InstalledEnd installed) = installed
installedTraceStart (InstalledStep action tag equation rest installed tail) =
  installed

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
0 committedProvidersInstalledTrace :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (providers : List name) ->
  (transitions : Transitions start finalState) ->
  (installedTrace : InstalledTrace name key world error value nameEq keyEq
    selected transitions) ->
  CommittedSnapshot name key world error value nameEq selected providers start ->
  CommittedProvidersConstant name key world error value nameEq selected providers
    transitions
committedProvidersInstalledTrace nameEq keyEq selected providers NoTransitions
  (InstalledEnd installed) snapshot =
    CommittedProvidersEnd (committedSnapshotEquation snapshot)
committedProvidersInstalledTrace nameEq keyEq selected providers
  (MoreTransitions (Fired nameEq keyEq action tag checkedEquation) rest)
  (InstalledStep action tag checkedEquation rest sourceInstalled tail) snapshot =
  let 0 rawEquation = checkedActionProjects nameEq keyEq action _ _ tag
        checkedEquation
      0 targetInstalled = installedTraceStart tail
      0 afterCommitted = case decEq @{nameEq} selected (actionOwner action) of
        No distinct => committedProvidersForeignAction nameEq keyEq selected
          providers action _ _ tag distinct (committedSnapshotEquation snapshot)
          rawEquation
        Yes same => committedProvidersSelectedAction nameEq keyEq selected providers
          action _ _ tag (sym same) snapshot targetInstalled rawEquation
      afterSnapshot = committedSnapshotFrom nameEq selected providers _
        afterCommitted
  in CommittedProvidersStep (Fired nameEq keyEq action tag checkedEquation) rest
    (committedSnapshotEquation snapshot)
    (committedProvidersInstalledTrace nameEq keyEq selected providers rest tail
      afterSnapshot)

0 foreignReloadingSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> Not (selected = actionOwner action) ->
  ReloadingSnapshot name key world error value nameEq selected providers before ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  ReloadingSnapshot name key world error value nameEq selected providers afterState
foreignReloadingSnapshot nameEq keyEq selected providers action before afterState
  tag distinct snapshot equation =
  let 0 foreignLookup = systemLocalUpdateForeign nameEq selected
        (actionOwner action) distinct before afterState
        (applyActionLocalUpdate nameEq keyEq action before afterState tag equation)
      0 targetLookup = trans foreignLookup (snapshotLookup snapshot)
  in MkReloadingSnapshot (snapshotFiber snapshot) targetLookup
    (snapshotRemaining snapshot) (snapshotAccumulator snapshot)
    (snapshotView snapshot) (snapshotReloading snapshot)
    (snapshotProviders snapshot)

0 foreignTransitionCoherent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (equation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  Not (selected = actionOwner action) ->
  transitionResolutionCoherent nameEq keyEq selected {before = before}
    (Fired nameEq keyEq action tag equation) = True
foreignTransitionCoherent nameEq keyEq selected
  (OInsert actor parent component) tag equation distinct = Refl
foreignTransitionCoherent nameEq keyEq selected (ORetire actor) tag equation
  distinct = Refl
foreignTransitionCoherent nameEq keyEq selected (ORemove actor) tag equation
  distinct = Refl
foreignTransitionCoherent nameEq keyEq selected (LBegin actor) tag equation
  distinct = Refl
foreignTransitionCoherent nameEq keyEq selected (LAdvance actor) tag equation
  distinct with (decEq @{nameEq} actor selected)
  foreignTransitionCoherent nameEq keyEq selected (LAdvance selected) tag equation
    distinct | Yes Refl = void (distinct Refl)
  foreignTransitionCoherent nameEq keyEq selected (LAdvance actor) tag equation
    distinct | No actorDistinct = Refl
foreignTransitionCoherent nameEq keyEq selected (LDivert actor) tag equation
  distinct = Refl
foreignTransitionCoherent nameEq keyEq selected (LLeave actor) tag equation
  distinct = Refl
foreignTransitionCoherent nameEq keyEq selected (LUnload actor) tag equation
  distinct = Refl

0 retireReloadingAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {fibers : Registry name key value world error} -> {worldValue : world} ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  {remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))} ->
  {accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber))} ->
  {view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))} ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected fibers = Just fiber ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  reloadingAt @{nameEq} {key = key} {value = value} {world = world}
    {error = error} selected (MkSystemState worldValue
    (replaceBinding @{nameEq} selected (retireFiber fiber) fibers)) = True
retireReloadingAfterReplace selected
  fiber@(MkFiber component parent retired table lifecycle) found reloading =
  rewrite lookupReplacedFiber selected fiber (retireFiber fiber) fibers found in
  rewrite reloading in Refl

0 retireReloadingFromSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  (selected : name) -> (providers : List name) -> (ambient : world) ->
  (fibers : Registry name key value world error) ->
  (fiber : Fiber name key value world error) ->
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers (MkSystemState ambient fibers)) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world} {error = error} selected fibers = Just fiber ->
  reloadingAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected (MkSystemState ambient
    (replaceBinding @{nameEq} selected (retireFiber fiber) fibers)) = True
retireReloadingFromSnapshot selected providers ambient fibers fiber snapshot found =
  case justInjective (trans (sym (snapshotLookup snapshot)) found) of
    Refl => retireReloadingAfterReplace selected fiber found
      (snapshotReloading snapshot)



0 retireReloadingSnapshotFromEquation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  ReloadingSnapshot name key world error value nameEq selected providers before ->
  committedProvidersAt @{nameEq} selected afterState = Just providers ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  ReloadingSnapshot name key world error value nameEq selected providers afterState
retireReloadingSnapshotFromEquation nameEq keyEq selected providers
  (MkSystemState ambient fibers) afterState tag snapshot targetCommitted equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  retireReloadingSnapshotFromEquation nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot targetCommitted equation | Nothing =
      void (nothingIsNotJust equation)
  retireReloadingSnapshotFromEquation nameEq keyEq selected providers
    (MkSystemState ambient fibers) afterState tag snapshot targetCommitted equation | Just fiber =
      case justInjective equation of
        Refl => snapshotFromPredicates nameEq selected providers
          (MkSystemState ambient
            (replaceBinding @{nameEq} selected (retireFiber fiber) fibers))
          (retireReloadingFromSnapshot selected providers ambient fibers fiber
            snapshot found)
          targetCommitted

0 retireReloadingSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  ReloadingSnapshot name key world error value nameEq selected providers before ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  ReloadingSnapshot name key world error value nameEq selected providers afterState
retireReloadingSnapshot nameEq keyEq selected providers before afterState tag
  snapshot equation =
  retireReloadingSnapshotFromEquation nameEq keyEq selected providers before
    afterState tag snapshot
    (committedProvidersORetireSelected nameEq keyEq selected providers before
      afterState tag (snapshotCommittedProviders snapshot) equation)
    equation

public export
0 successfulLDivertTag :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (tag, afterState) ->
  tag = LDivertTag
successfulLDivertTag nameEq keyEq selected before afterState tag equation
  with (lookupFiber @{nameEq} selected (registry before))
  successfulLDivertTag nameEq keyEq selected before afterState tag equation |
    Nothing = void (nothingIsNotJust equation)
  successfulLDivertTag nameEq keyEq selected before afterState tag equation |
    Just fiber with (fiberLifecycle fiber)
    successfulLDivertTag nameEq keyEq selected before afterState tag equation |
      Just fiber | Inactive outcome = void (nothingIsNotJust equation)
    successfulLDivertTag nameEq keyEq selected before afterState tag equation |
      Just fiber | Active accumulator view = void (nothingIsNotJust equation)
    successfulLDivertTag nameEq keyEq selected before afterState tag equation |
      Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust equation)
    successfulLDivertTag nameEq keyEq selected before afterState tag equation |
      Just fiber | Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view)
      successfulLDivertTag nameEq keyEq selected before afterState tag equation |
        Just fiber | Reloading remaining accumulator view | True =
          void (nothingIsNotJust equation)
      successfulLDivertTag nameEq keyEq selected before afterState tag equation |
        Just fiber | Reloading remaining accumulator view | False =
          sym (cong fst (justInjective equation))

0 iterAdvanceCoherent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq}
    (LAdvance selected) before = Just (LIterTag, afterState)) ->
  AdvanceStructure name key world error value nameEq keyEq selected LIterTag
    before afterState ->
  transitionResolutionCoherent nameEq keyEq selected {before = before}
    (Fired nameEq keyEq (LAdvance selected) LIterTag checkedEquation) = True
iterAdvanceCoherent nameEq keyEq selected before afterState checkedEquation
  (IterAdvance fiber found
    (remaining ** (accumulator ** (view ** (life, matches)))) reloading)
  with (decEq @{nameEq} selected selected)
  iterAdvanceCoherent nameEq keyEq selected before afterState checkedEquation
    (IterAdvance fiber found
      (remaining ** (accumulator ** (view ** (life, matches)))) reloading) |
      Yes Refl = rewrite found in rewrite life in matches
  iterAdvanceCoherent nameEq keyEq selected before afterState checkedEquation
    (IterAdvance fiber found
      (remaining ** (accumulator ** (view ** (life, matches)))) reloading) |
      No contra = void (contra Refl)

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
0 snapshotReloadingForLookup :
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers state) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) **
   (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world (componentProvisions (fiberComponent fiber)) **
   (view : View name
      (dependencies (componentDependencies (fiberComponent fiber))) **
    fiberLifecycle fiber = Reloading remaining accumulator view)))
snapshotReloadingForLookup snapshot fiber found =
  case justInjective (trans (sym (snapshotLookup snapshot)) found) of
    Refl => (snapshotRemaining snapshot ** (snapshotAccumulator snapshot **
      (snapshotView snapshot ** snapshotReloading snapshot)))

0 oInsertReloadingImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers before) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) -> Void
oInsertReloadingImpossible {name} {key} {world} {error} {value}
  nameEq keyEq selected parent component (MkSystemState ambient fibers)
  afterState tag snapshot equation
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  oInsertReloadingImpossible {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component (MkSystemState ambient fibers)
    afterState tag snapshot equation | False = void (nothingIsNotJust equation)
  oInsertReloadingImpossible {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component (MkSystemState ambient fibers)
    afterState tag snapshot equation | True
    with (setFresh @{nameEq} selected (freshFiber component parent) fibers)
      proof inserted
    oInsertReloadingImpossible {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component (MkSystemState ambient fibers)
      afterState tag snapshot equation | True | Nothing =
        void (nothingIsNotJust equation)
    oInsertReloadingImpossible {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component (MkSystemState ambient fibers)
      afterState tag snapshot equation | True | Just applied =
        let absent = setFreshAbsent nameEq selected (freshFiber component parent)
              fibers applied inserted
        in void (nothingIsNotJust
          (trans (sym absent) (snapshotLookup snapshot)))

0 oRemoveReloadingImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers before) ->
  applyAction @{nameEq} @{keyEq} (ORemove selected) before =
    Just (tag, afterState) -> Void
oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
  equation with (lookupFiber @{nameEq} selected (registry before)) proof found
  oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Nothing = void (nothingIsNotJust equation)
  oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Just fiber with (fiberLifecycle fiber) proof lifecycle
    oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Inactive outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (accumulator ** (view ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Active accumulator view =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Unloading accumulator view outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Reloading remaining accumulator view
      with (retired fiber)
      oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
        equation | Just fiber | Reloading remaining accumulator view | False =
          void (nothingIsNotJust equation)
      oRemoveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
        equation | Just fiber | Reloading remaining accumulator view | True =
          void (nothingIsNotJust equation)

0 lBeginReloadingImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers before) ->
  applyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (tag, afterState) -> Void
lBeginReloadingImpossible nameEq keyEq selected before afterState tag snapshot
  equation with (lookupFiber @{nameEq} selected (registry before)) proof found
  lBeginReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Nothing = void (nothingIsNotJust equation)
  lBeginReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Just fiber with (fiberLifecycle fiber) proof lifecycle
    lBeginReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Inactive outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (accumulator ** (view ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lBeginReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Active accumulator view =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lBeginReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Unloading accumulator view outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lBeginReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Reloading remaining accumulator view =
        void (nothingIsNotJust equation)

0 lLeaveReloadingImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers before) ->
  applyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (tag, afterState) -> Void
lLeaveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
  equation with (lookupFiber @{nameEq} selected (registry before)) proof found
  lLeaveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Nothing = void (nothingIsNotJust equation)
  lLeaveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Just fiber with (fiberLifecycle fiber) proof lifecycle
    lLeaveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Inactive outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (accumulator ** (view ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lLeaveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Active accumulator view =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lLeaveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Unloading accumulator view outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lLeaveReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Reloading remaining accumulator view =
        void (nothingIsNotJust equation)

0 lUnloadReloadingImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (snapshot : ReloadingSnapshot name key world error value nameEq selected
    providers before) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) -> Void
lUnloadReloadingImpossible nameEq keyEq selected before afterState tag snapshot
  equation with (lookupFiber @{nameEq} selected (registry before)) proof found
  lUnloadReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Nothing = void (nothingIsNotJust equation)
  lUnloadReloadingImpossible nameEq keyEq selected before afterState tag snapshot
    equation | Just fiber with (fiberLifecycle fiber) proof lifecycle
    lUnloadReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Inactive outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (accumulator ** (view ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lUnloadReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Active accumulator view =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lUnloadReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Unloading accumulator view outcome =
        case snapshotReloadingForLookup snapshot fiber found of
          (remaining ** (priorAccumulator ** (priorView ** reloading))) =>
            case trans (sym lifecycle) reloading of Refl impossible
    lUnloadReloadingImpossible nameEq keyEq selected before afterState tag snapshot
      equation | Just fiber | Reloading remaining accumulator view =
        void (nothingIsNotJust equation)

0 reloadingEndpointAt :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingEndpoint @{nameEq} selected state = True ->
  reloadingAt @{nameEq} selected state = True
reloadingEndpointAt nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  reloadingEndpointAt nameEq selected state evidence | Nothing =
    void (falseIsNotTrue evidence)
  reloadingEndpointAt nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    reloadingEndpointAt nameEq selected state evidence | Just fiber |
      Inactive outcome = void (falseIsNotTrue evidence)
    reloadingEndpointAt nameEq selected state evidence | Just fiber |
      Active accumulator view = void (falseIsNotTrue evidence)
    reloadingEndpointAt nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = void (falseIsNotTrue evidence)
    reloadingEndpointAt nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = Refl

0 activeEndpointAt :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeEndpoint @{nameEq} selected state = True ->
  activeAt @{nameEq} selected state = True
activeEndpointAt nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  activeEndpointAt nameEq selected state evidence | Nothing =
    void (falseIsNotTrue evidence)
  activeEndpointAt nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    activeEndpointAt nameEq selected state evidence | Just fiber |
      Inactive outcome = void (falseIsNotTrue evidence)
    activeEndpointAt nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = void (falseIsNotTrue evidence)
    activeEndpointAt nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = void (falseIsNotTrue evidence)
    activeEndpointAt nameEq selected state evidence | Just fiber |
      Active accumulator view = Refl

0 unloadingEndpointAt :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  unloadingEndpoint @{nameEq} selected state = True ->
  unloadingAt @{nameEq} selected state = True
unloadingEndpointAt nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  unloadingEndpointAt nameEq selected state evidence | Nothing =
    void (falseIsNotTrue evidence)
  unloadingEndpointAt nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    unloadingEndpointAt nameEq selected state evidence | Just fiber |
      Inactive outcome = void (falseIsNotTrue evidence)
    unloadingEndpointAt nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = void (falseIsNotTrue evidence)
    unloadingEndpointAt nameEq selected state evidence | Just fiber |
      Active accumulator view = void (falseIsNotTrue evidence)
    unloadingEndpointAt nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = Refl

public export
data ReloadingStepClassification :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Type where
  ReloadingContinues :
    {before, afterState : SystemState name key value world error} ->
    {transition : Transition before afterState} ->
    ReloadingSnapshot name key world error value nameEq selected providers
      afterState ->
    transitionResolutionCoherent nameEq keyEq selected transition = True ->
    ReloadingStepClassification name key world error value nameEq keyEq
      selected providers transition
  ReloadingExits :
    {before, afterState : SystemState name key value world error} ->
    {transition : Transition before afterState} ->
    StructuralExit name key world error value nameEq selected providers
      transition ->
    ReloadingStepClassification name key world error value nameEq keyEq
      selected providers transition

0 classifyReloadingStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  ReloadingSnapshot name key world error value nameEq selected providers before ->
  ReloadingStepClassification name key world error value nameEq keyEq selected
    providers (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checkedEquation)
classifyReloadingStep nameEq keyEq selected providers
  (OInsert actor parent component) tag before afterState checkedEquation
  snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers
    (OInsert actor parent component) tag before afterState checkedEquation
    snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (OInsert actor parent component) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (OInsert actor parent component) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (OInsert actor parent component) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers
    (OInsert actor parent component) tag before afterState checkedEquation
    snapshot | Yes Refl = void (oInsertReloadingImpossible nameEq keyEq actor
      parent component before afterState tag snapshot
      (checkedActionProjects nameEq keyEq (OInsert actor parent component) before afterState tag
        checkedEquation))
classifyReloadingStep nameEq keyEq selected providers (ORetire actor) tag
  before afterState checkedEquation snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers (ORetire actor) tag
    before afterState checkedEquation snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (ORetire actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (ORetire actor) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (ORetire actor) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers (ORetire actor) tag
    before afterState checkedEquation snapshot | Yes Refl =
      let rawEquation = checkedActionProjects nameEq keyEq (ORetire actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (retireReloadingSnapshot nameEq keyEq actor providers before afterState tag
          snapshot rawEquation) Refl
classifyReloadingStep nameEq keyEq selected providers (ORemove actor) tag
  before afterState checkedEquation snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers (ORemove actor) tag
    before afterState checkedEquation snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (ORemove actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (ORemove actor) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (ORemove actor) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers (ORemove actor) tag
    before afterState checkedEquation snapshot | Yes Refl =
      void (oRemoveReloadingImpossible nameEq keyEq actor before afterState tag
        snapshot (checkedActionProjects nameEq keyEq (ORemove actor) before afterState tag
          checkedEquation))
classifyReloadingStep nameEq keyEq selected providers (LBegin actor) tag
  before afterState checkedEquation snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers (LBegin actor) tag
    before afterState checkedEquation snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (LBegin actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (LBegin actor) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (LBegin actor) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers (LBegin actor) tag
    before afterState checkedEquation snapshot | Yes Refl =
      void (lBeginReloadingImpossible nameEq keyEq actor before afterState tag
        snapshot (checkedActionProjects nameEq keyEq (LBegin actor) before afterState tag
          checkedEquation))
classifyReloadingStep nameEq keyEq selected providers (LAdvance actor) tag
  before afterState checkedEquation snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers (LAdvance actor) tag
    before afterState checkedEquation snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (LAdvance actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (LAdvance actor) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (LAdvance actor) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers (LAdvance actor) tag
    before afterState checkedEquation snapshot | Yes Refl =
      let rawEquation = checkedActionProjects nameEq keyEq (LAdvance actor) before afterState
            tag checkedEquation
          structure = advanceStructureTheorem nameEq keyEq actor before afterState
            tag rawEquation
          committedSnapshot = committedSnapshotFrom nameEq actor providers before
            (snapshotCommittedProviders snapshot)
          targetCommitted = committedProvidersLAdvanceSelected nameEq keyEq actor
            providers before afterState tag committedSnapshot rawEquation
      in case structure of
        IterAdvance fiber found shape reloading =>
          ReloadingContinues
            (snapshotFromPredicates nameEq actor providers afterState
              (reloadingEndpointAt nameEq actor afterState reloading)
              targetCommitted)
            (iterAdvanceCoherent nameEq keyEq actor before afterState
              checkedEquation structure)
        FinishAdvance fiber found shape active => ReloadingExits
          (Finishes Refl Refl (activeEndpointAt nameEq actor afterState active)
            targetCommitted)
        DivertAdvance unloading => ReloadingExits
          (DivertsAfter Refl Refl
            (unloadingEndpointAt nameEq actor afterState unloading))
        RaiseAdvance unloading => ReloadingExits
          (Raises Refl Refl
            (unloadingEndpointAt nameEq actor afterState unloading))
classifyReloadingStep nameEq keyEq selected providers (LDivert actor) tag
  before afterState checkedEquation snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers (LDivert actor) tag
    before afterState checkedEquation snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (LDivert actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (LDivert actor) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (LDivert actor) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers (LDivert actor) tag
    before afterState checkedEquation snapshot | Yes Refl =
      let rawEquation = checkedActionProjects nameEq keyEq (LDivert actor) before afterState
            tag checkedEquation
          tagShape = successfulLDivertTag nameEq keyEq actor before afterState tag
            rawEquation
      in case tagShape of
        Refl => let structure = abortDivertStructureTheorem nameEq keyEq actor
                      before afterState rawEquation
                in ReloadingExits (DivertsBefore Refl Refl
                  (unloadingEndpointAt nameEq actor afterState
                    (divertUnloading structure)))
classifyReloadingStep nameEq keyEq selected providers (LLeave actor) tag
  before afterState checkedEquation snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers (LLeave actor) tag
    before afterState checkedEquation snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (LLeave actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (LLeave actor) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (LLeave actor) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers (LLeave actor) tag
    before afterState checkedEquation snapshot | Yes Refl =
      void (lLeaveReloadingImpossible nameEq keyEq actor before afterState tag
        snapshot (checkedActionProjects nameEq keyEq (LLeave actor) before afterState tag
          checkedEquation))
classifyReloadingStep nameEq keyEq selected providers (LUnload actor) tag
  before afterState checkedEquation snapshot with (decEq @{nameEq} selected actor)
  classifyReloadingStep nameEq keyEq selected providers (LUnload actor) tag
    before afterState checkedEquation snapshot | No distinct =
      let rawEquation = checkedActionProjects nameEq keyEq (LUnload actor) before afterState
            tag checkedEquation
      in ReloadingContinues
        (foreignReloadingSnapshot nameEq keyEq selected providers (LUnload actor) before
          afterState tag distinct snapshot rawEquation)
        (foreignTransitionCoherent nameEq keyEq selected (LUnload actor) tag checkedEquation
          distinct)
  classifyReloadingStep nameEq keyEq actor providers (LUnload actor) tag
    before afterState checkedEquation snapshot | Yes Refl =
      void (lUnloadReloadingImpossible nameEq keyEq actor before afterState tag
        snapshot (checkedActionProjects nameEq keyEq (LUnload actor) before afterState tag
          checkedEquation))

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

0 resolutionStructureInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (providers : List name) ->
  (transitions : Transitions start current) ->
  (installedTrace : InstalledTrace name key world error value nameEq keyEq
    selected transitions) ->
  ReloadingSnapshot name key world error value nameEq selected providers start ->
  ResolutionStructure name key world error value nameEq keyEq selected providers
    transitions
resolutionStructureInstalled nameEq keyEq selected providers NoTransitions
  (InstalledEnd installed) snapshot =
    StillReloading (snapshotEndThroughout snapshot) CoherentEnd
      (CommittedProvidersEnd (snapshotCommittedProviders snapshot))
resolutionStructureInstalled nameEq keyEq selected providers
  transitions@(MoreTransitions
    (Fired nameEq keyEq action tag checkedEquation) rest)
  installedTrace@(InstalledStep action tag checkedEquation rest sourceInstalled tail)
  snapshot =
  let sourceCommitted = snapshotCommittedProviders snapshot
      sourceCommittedSnapshot = committedSnapshotFrom nameEq selected providers _
        sourceCommitted
      wholeConstant = committedProvidersInstalledTrace nameEq keyEq selected
        providers transitions installedTrace sourceCommittedSnapshot
      classification = classifyReloadingStep nameEq keyEq selected providers action
        tag _ _ checkedEquation snapshot
  in case classification of
    ReloadingExits exit => ExitedReloading _ _ NoTransitions (Fired nameEq keyEq action tag checkedEquation) rest Refl
      (snapshotEndThroughout snapshot) CoherentEnd wholeConstant exit
    ReloadingContinues nextSnapshot stepCoherent =>
      case resolutionStructureInstalled nameEq keyEq selected providers rest tail
        nextSnapshot of
        StillReloading tailReloading tailCoherent tailConstant =>
          StillReloading
            (ReloadingStep (Fired nameEq keyEq action tag checkedEquation) rest (snapshotReloadingAt snapshot)
              tailReloading)
            (CoherentStep (Fired nameEq keyEq action tag checkedEquation) rest stepCoherent tailCoherent)
            (CommittedProvidersStep (Fired nameEq keyEq action tag checkedEquation) rest sourceCommitted tailConstant)
        ExitedReloading exitBefore exitAfter initialPart exitStep remainingPart
          splitEquation initialReloading initialCoherent tailConstant exit =>
            ExitedReloading exitBefore exitAfter
              (MoreTransitions (Fired nameEq keyEq action tag checkedEquation) initialPart) exitStep remainingPart
              (cong (MoreTransitions (Fired nameEq keyEq action tag checkedEquation)) splitEquation)
              (ReloadingStep (Fired nameEq keyEq action tag checkedEquation) initialPart
                (snapshotReloadingAt snapshot) initialReloading)
              (CoherentStep (Fired nameEq keyEq action tag checkedEquation) initialPart stepCoherent initialCoherent)
              (CommittedProvidersStep (Fired nameEq keyEq action tag checkedEquation) rest sourceCommitted tailConstant)
              exit

||| Structural Equation-59/exit theorem. Its input is anchored at L-Begin, so an
||| arbitrary Unloading suffix is unrepresentable.
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

public export
0 resolutionStructureTheoremProof :
  resolutionStructureTheorem name key value world error
resolutionStructureTheoremProof nameEq keyEq selected pre current episode =
  case beginReloadingSnapshot nameEq keyEq selected pre
    (episodeStartState episode) (opening episode) of
    (providers ** snapshot) =>
      (providers ** (snapshotCommittedProviders snapshot,
        resolutionStructureInstalled nameEq keyEq selected providers
          (prefixTransitions episode) (insideInstalled episode) snapshot))

||| Full Theorem 64 recovery branch over a maximal closed episode. Structural
||| coherence is separated so it can be proved without assuming temporal recovery.
||| TODO(proof): terminal recovery remains open; `DGamma.CP3Support` proves the
||| final combination from `terminalRecoveryTheorem`.
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

public export
0 fiberResolvedProviderInactive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  (outcome : Maybe error) ->
  fiberLifecycle fiber = Inactive outcome ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider fiber = False
fiberResolvedProviderInactive nameEq keyEq wanted provider
  (MkFiber component parent retired table (Inactive outcome)) outcome Refl = Refl

public export
resolvedProviderInView : DecEq name => DecEq key =>
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  View name (dependencies (componentDependencies component)) -> Bool
resolvedProviderInView wanted provider component view =
  case viewLookup wanted (dependencies (componentDependencies component)) view of
    Nothing => False
    Just actual => case decEq actual provider of
      Yes Refl => True
      No _ => False

public export
0 fiberResolvedProviderReloadingView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world
    (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (MkFiber component parent retired table
      (Reloading remaining accumulator view)) =
  resolvedProviderInView @{nameEq} @{keyEq} wanted provider component view
fiberResolvedProviderReloadingView nameEq keyEq wanted provider component
  parent retired table remaining accumulator view with
    (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) view)
  fiberResolvedProviderReloadingView nameEq keyEq wanted provider component
    parent retired table remaining accumulator view | Nothing = Refl
  fiberResolvedProviderReloadingView nameEq keyEq wanted provider component
    parent retired table remaining accumulator view | Just actual with
      (decEq @{nameEq} actual provider)
    fiberResolvedProviderReloadingView nameEq keyEq wanted provider component
      parent retired table remaining accumulator view | Just actual | Yes equal =
        case equal of Refl => Refl
    fiberResolvedProviderReloadingView nameEq keyEq wanted provider component
      parent retired table remaining accumulator view | Just actual | No distinct = Refl

public export
0 fiberResolvedProviderActiveView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world
    (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (MkFiber component parent retired table (Active accumulator view)) =
  resolvedProviderInView @{nameEq} @{keyEq} wanted provider component view
fiberResolvedProviderActiveView nameEq keyEq wanted provider component parent
  retired table accumulator view with (viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view)
  fiberResolvedProviderActiveView nameEq keyEq wanted provider component parent
    retired table accumulator view | Nothing = Refl
  fiberResolvedProviderActiveView nameEq keyEq wanted provider component parent
    retired table accumulator view | Just actual with
      (decEq @{nameEq} actual provider)
    fiberResolvedProviderActiveView nameEq keyEq wanted provider component parent
      retired table accumulator view | Just actual | Yes equal =
        case equal of Refl => Refl
    fiberResolvedProviderActiveView nameEq keyEq wanted provider component parent
      retired table accumulator view | Just actual | No distinct = Refl

public export
0 fiberResolvedProviderUnloadingView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world
    (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (MkFiber component parent retired table
      (Unloading accumulator view outcome)) =
  resolvedProviderInView @{nameEq} @{keyEq} wanted provider component view
fiberResolvedProviderUnloadingView nameEq keyEq wanted provider component parent
  retired table accumulator view outcome with (viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view)
  fiberResolvedProviderUnloadingView nameEq keyEq wanted provider component parent
    retired table accumulator view outcome | Nothing = Refl
  fiberResolvedProviderUnloadingView nameEq keyEq wanted provider component parent
    retired table accumulator view outcome | Just actual with
      (decEq @{nameEq} actual provider)
    fiberResolvedProviderUnloadingView nameEq keyEq wanted provider component parent
      retired table accumulator view outcome | Just actual | Yes equal =
        case equal of Refl => Refl
    fiberResolvedProviderUnloadingView nameEq keyEq wanted provider component parent
      retired table accumulator view outcome | Just actual | No distinct = Refl

public export
0 fiberResolvedProviderSetRuntimeFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  (newTable : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (newLife : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  committed (fiberLifecycle fiber) = Just view ->
  committed newLife = Just view ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (setFiberRuntime fiber newTable newLife) =
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider fiber
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table (Inactive outcome)) newTable newLife
  view sourceCommitted targetCommitted = case sourceCommitted of Refl impossible
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator sourceView)) newTable (Inactive outcome)
  view sourceCommitted targetCommitted = case targetCommitted of Refl impossible
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator sourceView)) newTable
  (Reloading targetRemaining targetAccumulator targetView)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => resolutionSame targetView
  where
    0 resolutionSame : (sameView : View name
      (dependencies (componentDependencies component))) ->
      fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
        (setFiberRuntime
          (MkFiber component parent retiredFlag table
            (Reloading remaining accumulator sameView))
          newTable (Reloading targetRemaining targetAccumulator sameView)) =
      fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
        (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator sameView))
    resolutionSame sameView with (viewLookup @{keyEq} wanted
      (dependencies (componentDependencies component)) sameView)
      resolutionSame sameView | Nothing = Refl
      resolutionSame sameView | Just actual with (decEq @{nameEq} actual provider)
        resolutionSame sameView | Just actual | Yes equal =
          case equal of Refl => Refl
        resolutionSame sameView | Just actual | No distinct = Refl
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator sourceView)) newTable
  (Active targetAccumulator targetView)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderActiveView nameEq keyEq wanted provider component
            parent retiredFlag newTable targetAccumulator targetView)
          (sym (fiberResolvedProviderReloadingView nameEq keyEq wanted provider
            component parent retiredFlag table remaining accumulator targetView))
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator sourceView)) newTable
  (Unloading targetAccumulator targetView outcome)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderUnloadingView nameEq keyEq wanted provider
            component parent retiredFlag newTable targetAccumulator targetView outcome)
          (sym (fiberResolvedProviderReloadingView nameEq keyEq wanted provider
            component parent retiredFlag table remaining accumulator targetView))
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table (Active accumulator sourceView))
  newTable (Inactive outcome) view sourceCommitted targetCommitted =
    case targetCommitted of Refl impossible
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table (Active accumulator sourceView))
  newTable (Reloading targetRemaining targetAccumulator targetView)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderReloadingView nameEq keyEq wanted provider
            component parent retiredFlag newTable targetRemaining targetAccumulator
            targetView)
          (sym (fiberResolvedProviderActiveView nameEq keyEq wanted provider
            component parent retiredFlag table accumulator targetView))
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table (Active accumulator sourceView))
  newTable (Active targetAccumulator targetView)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderActiveView nameEq keyEq wanted provider component
            parent retiredFlag newTable targetAccumulator targetView)
          (sym (fiberResolvedProviderActiveView nameEq keyEq wanted provider
            component parent retiredFlag table accumulator targetView))
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table (Active accumulator sourceView))
  newTable (Unloading targetAccumulator targetView outcome)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderUnloadingView nameEq keyEq wanted provider
            component parent retiredFlag newTable targetAccumulator targetView outcome)
          (sym (fiberResolvedProviderActiveView nameEq keyEq wanted provider
            component parent retiredFlag table accumulator targetView))
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Unloading accumulator sourceView sourceOutcome)) newTable
  (Inactive outcome) view sourceCommitted targetCommitted =
    case targetCommitted of Refl impossible
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Unloading accumulator sourceView sourceOutcome)) newTable
  (Reloading targetRemaining targetAccumulator targetView)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderReloadingView nameEq keyEq wanted provider
            component parent retiredFlag newTable targetRemaining targetAccumulator
            targetView)
          (sym (fiberResolvedProviderUnloadingView nameEq keyEq wanted provider
            component parent retiredFlag table accumulator targetView sourceOutcome))
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Unloading accumulator sourceView sourceOutcome)) newTable
  (Active targetAccumulator targetView)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderActiveView nameEq keyEq wanted provider component
            parent retiredFlag newTable targetAccumulator targetView)
          (sym (fiberResolvedProviderUnloadingView nameEq keyEq wanted provider
            component parent retiredFlag table accumulator targetView sourceOutcome))
fiberResolvedProviderSetRuntimeFrame nameEq keyEq wanted provider
  (MkFiber component parent retiredFlag table
    (Unloading accumulator sourceView sourceOutcome)) newTable
  (Unloading targetAccumulator targetView outcome)
  view sourceCommitted targetCommitted =
    case justInjective sourceCommitted of
      Refl => case justInjective targetCommitted of
        Refl => trans
          (fiberResolvedProviderUnloadingView nameEq keyEq wanted provider
            component parent retiredFlag newTable targetAccumulator targetView outcome)
          (sym (fiberResolvedProviderUnloadingView nameEq keyEq wanted provider
            component parent retiredFlag table accumulator targetView sourceOutcome))

public export
0 fiberResolvedProviderRetireFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (fiber : Fiber name key value world error) ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (retireFiber fiber) =
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider fiber
fiberResolvedProviderRetireFrame nameEq keyEq wanted provider
  (MkFiber component parent retired table (Inactive outcome)) = Refl
fiberResolvedProviderRetireFrame nameEq keyEq wanted provider
  (MkFiber component parent retired table
    (Reloading remaining accumulator view)) = Refl
fiberResolvedProviderRetireFrame nameEq keyEq wanted provider
  (MkFiber component parent retired table (Active accumulator view)) = Refl
fiberResolvedProviderRetireFrame nameEq keyEq wanted provider
  (MkFiber component parent retired table
    (Unloading accumulator view outcome)) = Refl


public export
0 resolvedProviderInViewNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  (view : View name (dependencies (componentDependencies component))) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view = Nothing ->
  resolvedProviderInView @{nameEq} @{keyEq} wanted provider component view = False
resolvedProviderInViewNothing nameEq keyEq wanted provider component view equation
  with (viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view)
  resolvedProviderInViewNothing nameEq keyEq wanted provider component view Refl |
    Nothing = Refl
  resolvedProviderInViewNothing nameEq keyEq wanted provider component view equation |
    Just actual = case equation of Refl impossible

public export
0 resolvedProviderInViewDifferent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider, actual : name) ->
  (component : Component key value world error) ->
  (view : View name (dependencies (componentDependencies component))) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view = Just actual ->
  (distinct : Not (actual = provider)) ->
  resolvedProviderInView @{nameEq} @{keyEq} wanted provider component view = False
resolvedProviderInViewDifferent nameEq keyEq wanted provider actual component view
  found distinct with (viewLookup @{keyEq} wanted
    (dependencies (componentDependencies component)) view)
  resolvedProviderInViewDifferent nameEq keyEq wanted provider actual component view
    Refl distinct | Just actual with (decEq @{nameEq} actual provider)
    resolvedProviderInViewDifferent nameEq keyEq wanted actual actual component view
      Refl distinct | Just actual | Yes Refl = absurd (distinct Refl)
    resolvedProviderInViewDifferent nameEq keyEq wanted provider actual component view
      Refl distinct | Just actual | No _ = Refl

public export
0 fiberResolvedProviderReloadingNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  viewLookup @{keyEq} wanted (dependencies (componentDependencies component)) view = Nothing ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (MkFiber component parent retired table (Reloading remaining accumulator view)) = False
fiberResolvedProviderReloadingNothing nameEq keyEq wanted provider component parent
  retired table remaining accumulator view equation with
    (viewLookup @{keyEq} wanted (dependencies (componentDependencies component)) view)
  fiberResolvedProviderReloadingNothing nameEq keyEq wanted provider component parent
    retired table remaining accumulator view Refl | Nothing = Refl
  fiberResolvedProviderReloadingNothing nameEq keyEq wanted provider component parent
    retired table remaining accumulator view equation | Just actual =
      case equation of Refl impossible

public export
0 fiberResolvedProviderActiveNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  viewLookup @{keyEq} wanted (dependencies (componentDependencies component)) view = Nothing ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (MkFiber component parent retired table (Active accumulator view)) = False
fiberResolvedProviderActiveNothing nameEq keyEq wanted provider component parent retired
  table accumulator view equation with
    (viewLookup @{keyEq} wanted (dependencies (componentDependencies component)) view)
  fiberResolvedProviderActiveNothing nameEq keyEq wanted provider component parent retired
    table accumulator view Refl | Nothing = Refl
  fiberResolvedProviderActiveNothing nameEq keyEq wanted provider component parent retired
    table accumulator view equation | Just actual = case equation of Refl impossible

public export
0 fiberResolvedProviderUnloadingNothing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (wanted : key) -> (provider : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retired : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  viewLookup @{keyEq} wanted (dependencies (componentDependencies component)) view = Nothing ->
  fiberResolvedProvider @{nameEq} @{keyEq} wanted provider
    (MkFiber component parent retired table (Unloading accumulator view outcome)) = False
fiberResolvedProviderUnloadingNothing nameEq keyEq wanted provider component parent retired
  table accumulator view outcome equation with
    (viewLookup @{keyEq} wanted (dependencies (componentDependencies component)) view)
  fiberResolvedProviderUnloadingNothing nameEq keyEq wanted provider component parent retired
    table accumulator view outcome Refl | Nothing = Refl
  fiberResolvedProviderUnloadingNothing nameEq keyEq wanted provider component parent retired
    table accumulator view outcome equation | Just actual = case equation of Refl impossible


