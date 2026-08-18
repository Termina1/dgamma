module DGamma.CP4DeletionSelectedForeignControlCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4DeletionSelectedBoundary
import Data.Maybe
import Decidable.Equality

%default total

0 selectedFiberComponentSame :
  SelectedFiberControlsRelated name key world error value selected actor
    left right ->
  fiberComponent left = fiberComponent right
selectedFiberComponentSame
  (SelectedFiberControls same
    (FibersStaticRelated leftParent rightParent leftRetired rightRetired
      leftTable rightTable leftLifecycle rightLifecycle parentSame
      retiredSame)) = Refl
selectedFiberComponentSame
  (ForeignFiberControls distinct
    (FibersControlRelated leftParent rightParent leftRetired rightRetired
      leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
      lifecycleSame)) = Refl

0 selectedFiberParentSame :
  SelectedFiberControlsRelated name key world error value selected actor
    left right ->
  fiberParent left = fiberParent right
selectedFiberParentSame
  (SelectedFiberControls same
    (FibersStaticRelated leftParent rightParent leftRetired rightRetired
      leftTable rightTable leftLifecycle rightLifecycle parentSame
      retiredSame)) = parentSame
selectedFiberParentSame
  (ForeignFiberControls distinct
    (FibersControlRelated leftParent rightParent leftRetired rightRetired
      leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
      lifecycleSame)) = parentSame

0 parentMatches : (nameEq : DecEq name) -> name -> Parent name -> Bool
parentMatches nameEq parent Root = False
parentMatches nameEq parent (ChildOf candidate) = case decEq @{nameEq} parent candidate of
  Yes Refl => True
  No distinct => False

0 isChildOfUsesParent :
  (nameEq : DecEq name) -> (parent, actor : name) ->
  (fiber : Fiber name key value world error) ->
  isChildOf @{nameEq} parent (Bind actor fiber) =
    parentMatches nameEq parent (fiberParent fiber)
isChildOfUsesParent nameEq parent actor
  (MkFiber component Root retiredFlag table lifecycle) = Refl
isChildOfUsesParent nameEq parent actor
  (MkFiber component (ChildOf candidate) retiredFlag table lifecycle)
  with (decEq @{nameEq} parent candidate)
  isChildOfUsesParent nameEq candidate actor
    (MkFiber component (ChildOf candidate) retiredFlag table lifecycle) |
    Yes Refl = Refl
  isChildOfUsesParent nameEq parent actor
    (MkFiber component (ChildOf candidate) retiredFlag table lifecycle) |
    No distinct = Refl

0 isChildOfRelated :
  (nameEq : DecEq name) -> (parent, actor : name) ->
  (left, right : Fiber name key value world error) ->
  fiberParent left = fiberParent right ->
  isChildOf @{nameEq} parent (Bind actor left) =
    isChildOf @{nameEq} parent (Bind actor right)
isChildOfRelated nameEq parent actor left right parentSame =
  trans (isChildOfUsesParent nameEq parent actor left)
    (trans (cong (parentMatches nameEq parent) parentSame)
      (sym (isChildOfUsesParent nameEq parent actor right)))

||| Exact binding-name order implies exact lookup presence, including at the
||| selected cell whose lifecycle is intentionally unrelated.
public export
0 selectedOrderedLookupPresenceSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} ->
  {left, right : List (Binding name (FiberAt name key value world error))} ->
  (nameEq : DecEq name) -> (wanted : name) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  isJust (lookupEntries @{nameEq} wanted left) =
    isJust (lookupEntries @{nameEq} wanted right)
selectedOrderedLookupPresenceSame nameEq wanted SelectedOrderedControlsNil = Refl
selectedOrderedLookupPresenceSame nameEq wanted
  (SelectedOrderedControlsCons current relation tail)
  with (decEq @{nameEq} wanted current)
  selectedOrderedLookupPresenceSame nameEq current
    (SelectedOrderedControlsCons current relation tail) | Yes Refl = Refl
  selectedOrderedLookupPresenceSame nameEq wanted
    (SelectedOrderedControlsCons current relation tail) | No distinct =
      selectedOrderedLookupPresenceSame nameEq wanted tail

public export
0 selectedOrderedParentPresentSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} ->
  (nameEq : DecEq name) -> (parent : Parent name) ->
  (left, right : Registry name key value world error) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings left) (bindings right) ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent left =
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent right
selectedOrderedParentPresentSame nameEq Root left right related = Refl
selectedOrderedParentPresentSame nameEq (ChildOf parent) left right related =
  trans (cong isJust (lookupFiberAsEntries nameEq parent left))
    (trans (selectedOrderedLookupPresenceSame nameEq parent related)
      (sym (cong isJust (lookupFiberAsEntries nameEq parent right))))

||| Component declarations are identical at every ordered cell, so the global
||| O-Insert provision-disjointness guard is preserved exactly.
public export
0 selectedOrderedProvisionsDisjointSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} ->
  (keyEq : DecEq key) -> (provision : CoeffectSpec key) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision left =
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision right
selectedOrderedProvisionsDisjointSame keyEq provision [] []
  SelectedOrderedControlsNil = Refl
selectedOrderedProvisionsDisjointSame keyEq provision
  (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
  (SelectedOrderedControlsCons actor relation tail) =
    let 0 headSame : (provisionOverlap @{keyEq} provision
          (componentProvisions (fiberComponent leftFiber)) =
        provisionOverlap @{keyEq} provision
          (componentProvisions (fiberComponent rightFiber)))
        headSame = cong
          (\component => provisionOverlap @{keyEq} provision
            (componentProvisions component))
          (selectedFiberComponentSame relation)
        0 tailSame : (provisionsDisjointFrom @{keyEq} {name = name}
          {key = key} {value = value} {world = world} {error = error}
          provision leftRest =
          provisionsDisjointFrom @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} provision rightRest)
        tailSame = selectedOrderedProvisionsDisjointSame keyEq provision
          leftRest rightRest tail
    in rewrite headSame in cong
      (\restGuard => not (provisionOverlap @{keyEq} provision
        (componentProvisions (fiberComponent rightFiber))) && restGuard)
      tailSame

||| Parent fields are exact at every cell, hence O-Remove's no-child guard is
||| preserved despite the selected lifecycle difference.
public export
0 selectedOrderedHasChildInSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} ->
  (nameEq : DecEq name) -> (parent : name) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent left =
  hasChildIn @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent right
selectedOrderedHasChildInSame nameEq parent [] [] SelectedOrderedControlsNil =
  Refl
selectedOrderedHasChildInSame nameEq parent
  (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
  (SelectedOrderedControlsCons actor relation tail) =
    let 0 headSame = isChildOfRelated nameEq parent actor leftFiber rightFiber
          (selectedFiberParentSame relation)
        0 tailSame = selectedOrderedHasChildInSame nameEq parent leftRest
          rightRest tail
    in rewrite headSame in cong
      (\tailChildren => isChildOf @{nameEq} parent (Bind actor rightFiber) ||
        tailChildren) tailSame

public export
0 selectedOrderedHasChildSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} ->
  (nameEq : DecEq name) -> (parent : name) ->
  (left, right : Registry name key value world error) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings left) (bindings right) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent left =
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent right
selectedOrderedHasChildSame nameEq parent left right related =
  selectedOrderedHasChildInSame nameEq parent (bindings left) (bindings right)
    related

public export
0 lifecycleControlIsInactiveSame :
  LifecycleControlRelated left right -> isInactive left = isInactive right
lifecycleControlIsInactiveSame (InactiveControls outcome) = Refl
lifecycleControlIsInactiveSame
  (ReloadingControls remaining accumulator view) = Refl
lifecycleControlIsInactiveSame (ActiveControls accumulator view) = Refl
lifecycleControlIsInactiveSame
  (UnloadingControls accumulator view outcome) = Refl

public export
0 fiberControlRetiredSame :
  FiberControlRelated left right -> retired left = retired right
fiberControlRetiredSame
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) = retiredSame

public export
0 fiberControlIsInactiveSame :
  FiberControlRelated left right ->
  isInactive (fiberLifecycle left) = isInactive (fiberLifecycle right)
fiberControlIsInactiveSame
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) = lifecycleControlIsInactiveSame lifecycleSame

||| O-Retire applies the same retirement edit to fully related foreign fibers.
public export
0 retireFiberControlRelated :
  FiberControlRelated left right ->
  FiberControlRelated (retireFiber left) (retireFiber right)
retireFiberControlRelated
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) =
      FibersControlRelated leftParent rightParent True True leftTable rightTable
        leftLifecycle rightLifecycle parentSame Refl lifecycleSame
