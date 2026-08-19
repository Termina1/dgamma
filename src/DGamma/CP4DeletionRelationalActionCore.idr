module DGamma.CP4DeletionRelationalActionCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import Data.Maybe
import Decidable.Equality

%default total

||| Transport only the list indices of an ordered relation.  Runtime fibers and
||| their extensional control evidence remain unchanged.
public export
0 orderedControlsTransport :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  OrderedRegistryControlsRelated name key world error value leftBefore
    rightBefore ->
  OrderedRegistryControlsRelated name key world error value leftAfter rightAfter
orderedControlsTransport Refl Refl related = related

0 orderedLookupEntriesRelated :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : List (Binding name
    (FiberAt name key value world error))} ->
  (nameEq : DecEq name) -> (wanted : name) ->
  OrderedRegistryControlsRelated name key world error value left right ->
  FiberControlMaybeRelated {name = name} {key = key} {value = value}
    {world = world} {error = error}
    (lookupEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} wanted left)
    (lookupEntries @{nameEq} {key = name}
      {value = FiberAt name key value world error} wanted right)
orderedLookupEntriesRelated nameEq wanted OrderedControlsNil = NoControlFibers
orderedLookupEntriesRelated nameEq wanted
  (OrderedControlsCons current fibers tail)
  with (decEq @{nameEq} wanted current)
  orderedLookupEntriesRelated nameEq current
    (OrderedControlsCons current fibers tail) | Yes Refl =
      SomeControlFibers fibers
  orderedLookupEntriesRelated nameEq wanted
    (OrderedControlsCons current fibers tail) | No distinct =
      orderedLookupEntriesRelated nameEq wanted tail

||| Ordered lookup preserves the complete control relation, including the owner
||| accumulator.  Unlike the selected quotient helper, no actor is exempt.
public export
0 orderedControlsLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : Registry name key value world error) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings left) (bindings right) ->
  FiberControlMaybeRelated {name = name} {key = key} {value = value}
    {world = world} {error = error}
    (lookupFiber @{nameEq} actor left) (lookupFiber @{nameEq} actor right)
orderedControlsLookup nameEq actor left right related =
  replace
    {p = \leftLookup => FiberControlMaybeRelated leftLookup
      (lookupFiber @{nameEq} actor right)}
    (sym (lookupFiberAsEntries nameEq actor left))
    (replace
      {p = \rightLookup => FiberControlMaybeRelated
        (lookupEntries @{nameEq} actor (bindings left)) rightLookup}
      (sym (lookupFiberAsEntries nameEq actor right))
      (orderedLookupEntriesRelated nameEq actor related))

0 noControlSomeImpossible :
  FiberControlMaybeRelated {name = name} {key = key} {value = value}
    {world = world} {error = error} Nothing (Just fiber) -> Void
noControlSomeImpossible relation impossible

||| Absence follows immediately from the exact ordered domain.
public export
0 orderedControlsNothingOnRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : Registry name key value world error) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings left) (bindings right) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor left = Nothing ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor right = Nothing
orderedControlsNothingOnRight nameEq actor left right related leftAbsent
  with (lookupFiber @{nameEq} actor right) proof rightFound
  orderedControlsNothingOnRight nameEq actor left right related leftAbsent |
    Nothing = Refl
  orderedControlsNothingOnRight nameEq actor left right related leftAbsent |
    Just rightFiber =
      let 0 lookupRelated = orderedControlsLookup nameEq actor left right related
          0 impossibleRelation : FiberControlMaybeRelated
            {name = name} {key = key} {value = value} {world = world}
            {error = error} Nothing (Just rightFiber)
          impossibleRelation = rewrite sym leftAbsent in
            rewrite sym rightFound in lookupRelated
      in void (noControlSomeImpossible impossibleRelation)

0 fiberControlGivesStatic :
  FiberControlRelated left right ->
  FiberStaticRelated name key world error value left right
fiberControlGivesStatic
  (FibersControlRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) =
      FibersStaticRelated leftParent rightParent leftRetired rightRetired
        leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame

||| Full controls imply the selected quotient's weaker static branch at an
||| arbitrary marker.  This bridge reuses the already-proved ordered guard
||| lemmas without making that marker operationally exceptional.
public export
0 orderedControlsGiveSelectedOrdered :
  (nameEq : DecEq name) -> (selected : name) ->
  OrderedRegistryControlsRelated name key world error value left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right
orderedControlsGiveSelectedOrdered nameEq selected OrderedControlsNil =
  SelectedOrderedControlsNil
orderedControlsGiveSelectedOrdered nameEq selected
  (OrderedControlsCons actor controls tail)
  with (decEq @{nameEq} actor selected)
  orderedControlsGiveSelectedOrdered nameEq actor
    (OrderedControlsCons actor controls tail) | Yes Refl =
      SelectedOrderedControlsCons actor
        (SelectedFiberControls Refl (fiberControlGivesStatic controls))
        (orderedControlsGiveSelectedOrdered nameEq actor tail)
  orderedControlsGiveSelectedOrdered nameEq selected
    (OrderedControlsCons actor controls tail) | No distinct =
      SelectedOrderedControlsCons actor
        (ForeignFiberControls distinct controls)
        (orderedControlsGiveSelectedOrdered nameEq selected tail)

public export
0 orderedControlsParentPresentSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (marker : name) -> (parent : Parent name) ->
  (left, right : Registry name key value world error) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings left) (bindings right) ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent left =
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent right
orderedControlsParentPresentSame nameEq marker parent left right related =
  DGamma.CP4DeletionSelectedForeignControlCore.selectedOrderedParentPresentSame
    nameEq parent left right
    (orderedControlsGiveSelectedOrdered nameEq marker related)

public export
0 orderedControlsProvisionsDisjointSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (marker : name) ->
  (provision : CoeffectSpec key) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  OrderedRegistryControlsRelated name key world error value left right ->
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision left =
  provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} provision right
orderedControlsProvisionsDisjointSame nameEq keyEq marker provision left right
  related =
    DGamma.CP4DeletionSelectedForeignControlCore.selectedOrderedProvisionsDisjointSame
      keyEq provision left right
      (orderedControlsGiveSelectedOrdered nameEq marker related)

public export
0 orderedControlsHasChildSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (marker, parent : name) ->
  (left, right : Registry name key value world error) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings left) (bindings right) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent left =
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent right
orderedControlsHasChildSame nameEq marker parent left right related =
  DGamma.CP4DeletionSelectedForeignControlCore.selectedOrderedHasChildSame
    nameEq parent left right
    (orderedControlsGiveSelectedOrdered nameEq marker related)

||| Apply the same related edit to one exact ordered cell.
public export
0 orderedControlsReplace :
  (nameEq : DecEq name) -> (actor : name) ->
  (nextLeft, nextRight : Fiber name key value world error) ->
  FiberControlRelated nextLeft nextRight ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  OrderedRegistryControlsRelated name key world error value left right ->
  OrderedRegistryControlsRelated name key world error value
    (replaceEntries @{nameEq} actor nextLeft left)
    (replaceEntries @{nameEq} actor nextRight right)
orderedControlsReplace nameEq actor nextLeft nextRight nextControls [] []
  OrderedControlsNil = OrderedControlsNil
orderedControlsReplace nameEq actor nextLeft nextRight nextControls
  (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
  (OrderedControlsCons current controls tail)
  with (decEq @{nameEq} actor current)
  orderedControlsReplace nameEq current nextLeft nextRight nextControls
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    (OrderedControlsCons current controls tail) | Yes Refl =
      OrderedControlsCons current nextControls tail
  orderedControlsReplace nameEq actor nextLeft nextRight nextControls
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    (OrderedControlsCons current controls tail) | No distinct =
      OrderedControlsCons current controls
        (orderedControlsReplace nameEq actor nextLeft nextRight nextControls
          leftRest rightRest tail)

public export
0 orderedControlsDelete :
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  OrderedRegistryControlsRelated name key world error value left right ->
  OrderedRegistryControlsRelated name key world error value
    (deleteEntries @{nameEq} actor left) (deleteEntries @{nameEq} actor right)
orderedControlsDelete nameEq actor [] [] OrderedControlsNil = OrderedControlsNil
orderedControlsDelete nameEq actor
  (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
  (OrderedControlsCons current controls tail)
  with (decEq @{nameEq} actor current)
  orderedControlsDelete nameEq current
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    (OrderedControlsCons current controls tail) | Yes Refl = tail
  orderedControlsDelete nameEq actor
    (Bind current leftFiber :: leftRest) (Bind current rightFiber :: rightRest)
    (OrderedControlsCons current controls tail) | No distinct =
      OrderedControlsCons current controls
        (orderedControlsDelete nameEq actor leftRest rightRest tail)

public export
0 orderedControlsInsert :
  (actor : name) -> FiberControlRelated leftFiber rightFiber ->
  OrderedRegistryControlsRelated name key world error value left right ->
  OrderedRegistryControlsRelated name key world error value
    (Bind actor leftFiber :: left) (Bind actor rightFiber :: right)
orderedControlsInsert actor controls tail =
  OrderedControlsCons actor controls tail

||| Updating corresponding actor tables with equal ordered bindings preserves
||| the exact effect relation.
public export
0 setRelatedEffectTables :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  bindings leftTable = bindings rightTable ->
  EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor leftTable left)
    (setEffectTable @{nameEq} actor rightTable right)
setRelatedEffectTables nameEq keyEq actor leftTable rightTable tablesSame related =
  MkEffectStateRelated (ambientExact related) tables
  where
  0 tables : (wanted : name) ->
    bindings (effectTables (setEffectTable @{nameEq} actor leftTable left) wanted) =
    bindings (effectTables (setEffectTable @{nameEq} actor rightTable right) wanted)
  tables wanted with (decEq @{nameEq} wanted actor)
    tables wanted | Yes same = case same of Refl => tablesSame
    tables wanted | No distinct = tablesExact related wanted

||| Updating ambient values with equal observations preserves all actor tables.
public export
0 setRelatedEffectAmbient :
  (keyEq : DecEq key) -> (leftWorld, rightWorld : world) ->
  leftWorld = rightWorld -> EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq (setEffectAmbient leftWorld left)
    (setEffectAmbient rightWorld right)
setRelatedEffectAmbient keyEq leftWorld rightWorld worldSame related =
  MkEffectStateRelated worldSame (tablesExact related)

||| Project exact ambient equality from the full effect relation.
public export
0 relatedSystemWorldsSame :
  (nameEq : DecEq name) ->
  (left, right : SystemState name key value world error) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  worldState left = worldState right
relatedSystemWorldsSame nameEq left right effects = ambientExact effects

||| Exact actor-table equality projected at a located related owner.
public export
0 relatedLocatedFiberTablesSame :
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry left) = Just leftFiber ->
  lookupFiber @{nameEq} actor (registry right) = Just rightFiber ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  bindings (ownedValues (fiberTable leftFiber)) =
    bindings (ownedValues (fiberTable rightFiber))
relatedLocatedFiberTablesSame nameEq actor left right leftFiber rightFiber
  leftFound rightFound effects =
    trans (cong bindings (sym (projectedActorTable nameEq actor left leftFiber
      leftFound)))
      (trans (tablesExact effects actor)
        (cong bindings (projectedActorTable nameEq actor right rightFiber
          rightFound)))
