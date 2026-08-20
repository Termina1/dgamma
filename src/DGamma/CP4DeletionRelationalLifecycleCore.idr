module DGamma.CP4DeletionRelationalLifecycleCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalLifecycleSources
import DGamma.CP4DeletionSelectedForeignControlCore
import Decidable.Equality

%default total

||| The two exact owner cells and the complete ordered runtime source relation
||| recovered from one successful lifecycle head.
public export
record RelatedLifecycleOwners
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor : name)
  (left, right : SystemState name key value world error) where
  constructor MkRelatedLifecycleOwners
  leftLifecycleOwner : Fiber name key value world error
  rightLifecycleOwner : Fiber name key value world error
  0 leftLifecycleOwnerFound : lookupFiber @{nameEq} actor (registry left) =
    Just leftLifecycleOwner
  0 rightLifecycleOwnerFound : lookupFiber @{nameEq} actor (registry right) =
    Just rightLifecycleOwner
  0 lifecycleOwnersRelated : FiberControlRelated leftLifecycleOwner
    rightLifecycleOwner
  0 lifecycleRuntimeSources : OrderedRuntimeSourcesRelated name key world error
    value (bindings (registry left)) (bindings (registry right))

||| Full ordered/effect boundaries determine both lifecycle owner cells.  The
||| successful raw head rules out absence on the left; exact ordered domains
||| then rule out absence on the right.
public export
0 relatedLifecycleOwnersAt :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (left, right : SystemState name key value world error) ->
  (tag : RuleTag) -> (leftAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action left = Just (tag, leftAfter) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry left)) (bindings (registry right)) ->
  RelatedLifecycleOwners name key world error value nameEq keyEq
    (actionOwner action) left right
relatedLifecycleOwnersAt nameEq keyEq action lifecycle left right tag leftAfter
  leftRaw effects ordered =
    let (leftOwner ** leftFound) = lifecycleOwnerPresent nameEq keyEq action
          lifecycle left leftAfter tag leftRaw
        maybeRelated = orderedControlsLookup nameEq (actionOwner action)
          (registry left) (registry right) ordered
    in case foreignControlLookupFound nameEq (actionOwner action)
      (registry left) (registry right) leftOwner leftFound maybeRelated of
      MkForeignRelatedFiberFound rightOwner rightFound ownersRelated =>
        MkRelatedLifecycleOwners leftOwner rightOwner leftFound rightFound
          ownersRelated (buildOrderedRuntimeSources nameEq keyEq left right
            effects ordered)

public export
fiberControlRelatedLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Fiber name key value world error} ->
  FiberControlRelated left right -> Fiber name key value world error
fiberControlRelatedLeft
  (FibersControlRelated {name} {key} {value} {world} {error} {component}
    leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) =
      MkFiber component leftParent leftRetired leftTable leftLifecycle

public export
0 fiberControlRelatedLeftIsLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Fiber name key value world error} ->
  (related : FiberControlRelated left right) ->
  fiberControlRelatedLeft related = left
fiberControlRelatedLeftIsLeft
  (FibersControlRelated {name} {key} {value} {world} {error} {component}
    leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) = Refl

||| Reify the right endpoint hidden by an indexed control witness.  Keeping the
||| equality explicit avoids relying on dependent-pattern refinement across a
||| module boundary (an Idris 0.8 elaboration limitation).
public export
fiberControlRelatedRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Fiber name key value world error} ->
  FiberControlRelated left right -> Fiber name key value world error
fiberControlRelatedRight
  (FibersControlRelated {name} {key} {value} {world} {error} {component}
    leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) =
      MkFiber component rightParent rightRetired rightTable rightLifecycle

public export
0 fiberControlRelatedRightIsRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Fiber name key value world error} ->
  (related : FiberControlRelated left right) ->
  fiberControlRelatedRight related = right
fiberControlRelatedRightIsRight
  (FibersControlRelated {name} {key} {value} {world} {error} {component}
    leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) = Refl

||| Concrete survivor lifecycle replay before the generic effect-frame join.
||| The acting cell has been replaced on both ordered registries, and the right
||| evaluator has executed the same observed Table-1 tag.
public export
record RelatedLifecycleRawControlReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (leftBefore, rightBefore : SystemState name key value world error)
  (leftNamed : NamedTransition name key world error value action leftBefore) where
  constructor MkRelatedLifecycleRawControlReplay
  relatedLifecycleAfter : SystemState name key value world error
  0 relatedLifecycleRaw : applyAction @{nameEq} @{keyEq} action rightBefore =
    Just (namedTag leftNamed, relatedLifecycleAfter)
  0 relatedLifecycleControls : OrderedRegistryControlsRelated name key world
    error value (bindings (registry (namedAfter leftNamed)))
    (bindings (registry relatedLifecycleAfter))

||| A full-boundary counterpart of the selected lifecycle replay package.
public export
record FullLifecycleControlReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error) (tag : RuleTag)
  (leftAfter, rightBefore : SystemState name key value world error) where
  constructor MkFullLifecycleControlReplay
  fullLifecycleAfter : SystemState name key value world error
  0 fullLifecycleRaw : applyAction @{nameEq} @{keyEq} action rightBefore =
    Just (tag, fullLifecycleAfter)
  0 fullLifecycleControls : OrderedRegistryControlsRelated name key world error
    value (bindings (registry leftAfter))
    (bindings (registry fullLifecycleAfter))

public export
0 packageFullLifecycleReplacementReplay :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (leftAfter : SystemState name key value world error) ->
  (rightBeforeWorld : world) ->
  (left, right : Registry name key value world error) ->
  (leftNext, rightNext : Fiber name key value world error) ->
  FiberControlRelated leftNext rightNext ->
  OrderedRegistryControlsRelated name key world error value
    (bindings left) (bindings right) ->
  (leftAfterWorld : world) ->
  MkSystemState leftAfterWorld
    (replaceBinding @{nameEq} actor leftNext left) = leftAfter ->
  (rightAfterWorld : world) ->
  applyAction @{nameEq} @{keyEq} action
    (MkSystemState rightBeforeWorld right) =
    Just (tag, MkSystemState rightAfterWorld
      (replaceBinding @{nameEq} actor rightNext right)) ->
  FullLifecycleControlReplay name key world error value nameEq keyEq action tag
    leftAfter (MkSystemState rightBeforeWorld right)
packageFullLifecycleReplacementReplay nameEq keyEq actor action tag leftAfter
  rightBeforeWorld left right leftNext rightNext nextRelated sourceOrdered
  leftAfterWorld leftAfterShape rightAfterWorld rightRaw =
    let rightAfter : SystemState name key value world error
        rightAfter = MkSystemState rightAfterWorld
          (replaceBinding @{nameEq} actor rightNext right)
        0 replaced : OrderedRegistryControlsRelated name key world error value
          (replaceEntries @{nameEq} actor leftNext (bindings left))
          (replaceEntries @{nameEq} actor rightNext (bindings right))
        replaced = orderedControlsReplace nameEq actor leftNext rightNext
          nextRelated (bindings left) (bindings right) sourceOrdered
        0 leftBindings : bindings
          (replaceBinding @{nameEq} actor leftNext left) =
          replaceEntries @{nameEq} actor leftNext (bindings left)
        leftBindings = replaceBindingRuntimeBindings nameEq actor leftNext left
        0 rightBindings : bindings
          (replaceBinding @{nameEq} actor rightNext right) =
          replaceEntries @{nameEq} actor rightNext (bindings right)
        rightBindings = replaceBindingRuntimeBindings nameEq actor rightNext right
        0 concrete : OrderedRegistryControlsRelated name key world error value
          (bindings (replaceBinding @{nameEq} actor leftNext left))
          (bindings (replaceBinding @{nameEq} actor rightNext right))
        concrete = orderedControlsTransport (sym leftBindings)
          (sym rightBindings) replaced
        0 finalControls : OrderedRegistryControlsRelated name key world error
          value (bindings (registry leftAfter))
          (bindings (registry rightAfter))
        finalControls = orderedControlsTransport
          (cong (\state => bindings (registry state)) leftAfterShape) Refl
          concrete
    in MkFullLifecycleControlReplay rightAfter rightRaw finalControls

||| Shared ordered-control packager for every lifecycle branch.  It deliberately
||| compares runtime binding lists rather than erased registry certificates.
public export
0 packageRelatedLifecycleReplacementControls :
  (nameEq : DecEq name) ->
  (action : Action name key value world error) ->
  (actor : name) ->
  (leftBeforeWorld, rightBeforeWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftNamed : NamedTransition name key world error value action
    (MkSystemState leftBeforeWorld leftRegistry)) ->
  (leftNext, rightNext : Fiber name key value world error) ->
  FiberControlRelated leftNext rightNext ->
  OrderedRegistryControlsRelated name key world error value
    (bindings leftRegistry) (bindings rightRegistry) ->
  (leftAfterWorld : world) ->
  MkSystemState leftAfterWorld
    (replaceBinding @{nameEq} actor leftNext leftRegistry) =
      namedAfter leftNamed ->
  (rightAfterWorld : world) ->
  applyAction @{nameEq} @{keyEq} action
    (MkSystemState rightBeforeWorld rightRegistry) =
    Just (namedTag leftNamed,
      MkSystemState rightAfterWorld
        (replaceBinding @{nameEq} actor rightNext rightRegistry)) ->
  RelatedLifecycleRawControlReplay name key world error value nameEq keyEq
    action (MkSystemState leftBeforeWorld leftRegistry)
    (MkSystemState rightBeforeWorld rightRegistry) leftNamed
packageRelatedLifecycleReplacementControls nameEq action actor leftBeforeWorld
  rightBeforeWorld leftRegistry rightRegistry leftNamed leftNext rightNext
  nextRelated sourceOrdered leftAfterWorld leftAfterShape rightAfterWorld
  rightRaw =
    let rightAfter : SystemState name key value world error
        rightAfter = MkSystemState rightAfterWorld
          (replaceBinding @{nameEq} actor rightNext rightRegistry)
        0 replaced : OrderedRegistryControlsRelated name key world error value
          (replaceEntries @{nameEq} actor leftNext (bindings leftRegistry))
          (replaceEntries @{nameEq} actor rightNext (bindings rightRegistry))
        replaced = orderedControlsReplace nameEq actor leftNext rightNext
          nextRelated (bindings leftRegistry) (bindings rightRegistry)
          sourceOrdered
        0 leftBindings : bindings
          (replaceBinding @{nameEq} actor leftNext leftRegistry) =
          replaceEntries @{nameEq} actor leftNext (bindings leftRegistry)
        leftBindings = replaceBindingRuntimeBindings nameEq actor leftNext
          leftRegistry
        0 rightBindings : bindings
          (replaceBinding @{nameEq} actor rightNext rightRegistry) =
          replaceEntries @{nameEq} actor rightNext (bindings rightRegistry)
        rightBindings = replaceBindingRuntimeBindings nameEq actor rightNext
          rightRegistry
        0 concrete : OrderedRegistryControlsRelated name key world error value
          (bindings (replaceBinding @{nameEq} actor leftNext leftRegistry))
          (bindings (replaceBinding @{nameEq} actor rightNext rightRegistry))
        concrete = orderedControlsTransport (sym leftBindings)
          (sym rightBindings) replaced
        0 finalControls : OrderedRegistryControlsRelated name key world error
          value (bindings (registry (namedAfter leftNamed)))
          (bindings (registry rightAfter))
        finalControls = orderedControlsTransport
          (cong (\state => bindings (registry state)) leftAfterShape) Refl
          concrete
    in MkRelatedLifecycleRawControlReplay rightAfter rightRaw finalControls
