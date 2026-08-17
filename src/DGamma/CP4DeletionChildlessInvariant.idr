module DGamma.CP4DeletionChildlessInvariant

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanBoundary
import DGamma.CP4DeletionPlanSuccess
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 justInjectiveChildless : Just left = Just right -> left = right
justInjectiveChildless Refl = Refl

0 childOfInjectiveChildless : ChildOf left = ChildOf right -> left = right
childOfInjectiveChildless Refl = Refl

0 boolAndLeftChildless : (left, right : Bool) ->
  left && right = True -> left = True
boolAndLeftChildless True False equation = case equation of Refl impossible
boolAndLeftChildless True True equation = Refl
boolAndLeftChildless False right equation = case equation of Refl impossible

0 boolAndRightChildless : (left, right : Bool) ->
  left && right = True -> right = True
boolAndRightChildless False right equation = case equation of Refl impossible
boolAndRightChildless True False equation = case equation of Refl impossible
boolAndRightChildless True True equation = Refl

0 boolOrLeftFalseChildless : (left, right : Bool) ->
  left || right = False -> left = False
boolOrLeftFalseChildless False right equation = Refl
boolOrLeftFalseChildless True right equation = case equation of Refl impossible

0 boolOrRightFalseChildless : (left, right : Bool) ->
  left || right = False -> right = False
boolOrRightFalseChildless False False equation = Refl
boolOrRightFalseChildless True False equation = Refl
boolOrRightFalseChildless False True equation = case equation of Refl impossible
boolOrRightFalseChildless True True equation = case equation of Refl impossible

0 andFourFirstChildless : (a, b, c, d : Bool) ->
  a && b && c && d = True -> a = True
andFourFirstChildless a b c d valid =
  boolAndLeftChildless a (b && c && d) valid

||| Parent closure plus absence of a raw name rules out any extant child pointer
||| to that name. This is the well-formedness fact needed when a fresh R
||| generation is born after an older generation of the same raw name.
0 parentsAbsentHaveNoChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected source = Nothing ->
  parentsInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} entries source = True ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected entries = False
parentsAbsentHaveNoChild nameEq selected [] source absent parents = Refl
parentsAbsentHaveNoChild nameEq selected
  (Bind current (MkFiber component Root retiredFlag table lifecycle) :: rest)
  source absent parents =
    let tailParents = boolAndRightChildless
          (parentInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} Root source)
          (parentsInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} rest source) parents
        tailChildless = parentsAbsentHaveNoChild nameEq selected rest source
          absent tailParents
    in rewrite tailChildless in Refl
parentsAbsentHaveNoChild nameEq selected
  (Bind current (MkFiber component (ChildOf candidate) retiredFlag table
    lifecycle) :: rest)
  source absent parents with (decEq @{nameEq} selected candidate) proof sameParent
  parentsAbsentHaveNoChild nameEq candidate
    (Bind current (MkFiber component (ChildOf candidate) retiredFlag table
      lifecycle) :: rest)
    source absent parents | Yes Refl =
      let parentPresent = boolAndLeftChildless
            (parentInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (ChildOf candidate) source)
            (parentsInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} rest source) parents
          contradiction = trans (sym (cong isJust absent)) parentPresent
      in case contradiction of Refl impossible
  parentsAbsentHaveNoChild nameEq selected
    (Bind current (MkFiber component (ChildOf candidate) retiredFlag table
      lifecycle) :: rest)
    source absent parents | No distinct =
      let tailParents = boolAndRightChildless
            (parentInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (ChildOf candidate) source)
            (parentsInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} rest source) parents
          tailChildless = parentsAbsentHaveNoChild nameEq selected rest source
            absent tailParents
      in tailChildless

0 wellFormedAbsentHasNoChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} state = True ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry state) = Nothing ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry state) = False
wellFormedAbsentHasNoChild {name} {key} {world} {error} {value}
  nameEq keyEq selected
  (MkSystemState ambient source@(MkCoeffectContext entries unique))
  wellFormed absent =
    let parentClosure = andFourFirstChildless
          (parentsInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} entries source)
          (chainsInvariant @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (S (length entries)) entries source)
          (pairwiseProvisionInvariant @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} entries)
          (viewsInvariant @{nameEq} @{keyEq} {name = name} {key = key} {value = value} {world = world} {error = error} entries source) wellFormed
    in parentsAbsentHaveNoChild nameEq selected entries source absent
      parentClosure

0 parentDifferentIsChildFalse :
  (nameEq : DecEq name) -> (selected, inserted : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  Not (parent = ChildOf selected) ->
  isChildOf @{nameEq} selected (Bind inserted (freshFiber component parent)) =
    False
parentDifferentIsChildFalse nameEq selected inserted component Root different =
  Refl
parentDifferentIsChildFalse nameEq selected inserted component
  (ChildOf candidate) different with (decEq @{nameEq} selected candidate)
  parentDifferentIsChildFalse nameEq candidate inserted component
    (ChildOf candidate) different | Yes Refl = void (different Refl)
  parentDifferentIsChildFalse nameEq selected inserted component
    (ChildOf candidate) different | No distinct = Refl

0 hasChildInsertFalse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected, inserted : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (source : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} inserted source = Nothing) ->
  Not (parent = ChildOf selected) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected source = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected
    (insertBinding @{nameEq} inserted (freshFiber component parent) source
      absent) = False
hasChildInsertFalse nameEq selected inserted component parent
  (MkCoeffectContext entries unique) absent parentDifferent noChild =
    rewrite parentDifferentIsChildFalse nameEq selected inserted component parent
      parentDifferent in
    rewrite noChild in Refl

0 isSelectedParent : DecEq name -> name -> Parent name -> Bool
isSelectedParent nameEq selected Root = False
isSelectedParent nameEq selected (ChildOf candidate) =
  case decEq @{nameEq} selected candidate of
    Yes Refl => True
    No distinct => False

0 isChildOfParentEquation :
  (nameEq : DecEq name) -> (selected, observed : name) ->
  (fiber : Fiber name key value world error) ->
  isChildOf @{nameEq} selected (Bind observed fiber) =
    isSelectedParent nameEq selected (fiberParent fiber)
isChildOfParentEquation nameEq selected observed
  (MkFiber component Root retiredFlag table lifecycle) = Refl
isChildOfParentEquation nameEq selected observed
  (MkFiber component (ChildOf candidate) retiredFlag table lifecycle)
  with (decEq @{nameEq} selected candidate)
  isChildOfParentEquation nameEq candidate observed
    (MkFiber component (ChildOf candidate) retiredFlag table lifecycle) |
    Yes Refl = Refl
  isChildOfParentEquation nameEq selected observed
    (MkFiber component (ChildOf candidate) retiredFlag table lifecycle) |
    No distinct = Refl

0 isChildOfSameParent :
  (nameEq : DecEq name) -> (selected, observed : name) ->
  (next, old : Fiber name key value world error) ->
  fiberParent next = fiberParent old ->
  isChildOf @{nameEq} selected (Bind observed next) =
    isChildOf @{nameEq} selected (Bind observed old)
isChildOfSameParent nameEq selected observed next old sameParent =
  trans (isChildOfParentEquation nameEq selected observed next)
    (trans (cong (isSelectedParent nameEq selected) sameParent)
      (sym (isChildOfParentEquation nameEq selected observed old)))

0 hasChildInReplaceFalse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected, changed : name) ->
  (next, old : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} changed entries = Just old ->
  fiberParent next = fiberParent old ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected entries = False ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected
    (replaceEntries @{nameEq} changed next entries) = False
hasChildInReplaceFalse nameEq selected changed next old [] found sameParent
  noChild = case found of Refl impossible
hasChildInReplaceFalse nameEq selected changed next old
  (Bind current observed :: rest) found sameParent noChild
  with (decEq @{nameEq} changed current) proof changedCurrent
  hasChildInReplaceFalse nameEq selected current next old
    (Bind current observed :: rest) found sameParent noChild | Yes Refl =
      let sameObserved = justInjectiveChildless found
          nextObservedParent = trans sameParent
            (cong fiberParent (sym sameObserved))
          headSame = isChildOfSameParent nameEq selected current next observed
            nextObservedParent
          oldHeadFalse = boolOrLeftFalseChildless
            (isChildOf @{nameEq} selected (Bind current observed))
            (hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected rest) noChild
          nextHeadFalse = trans headSame oldHeadFalse
          tailFalse = boolOrRightFalseChildless
            (isChildOf @{nameEq} selected (Bind current observed))
            (hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected rest) noChild
      in rewrite nextHeadFalse in rewrite tailFalse in Refl
  hasChildInReplaceFalse nameEq selected changed next old
    (Bind current observed :: rest) found sameParent noChild | No distinct =
      let headFalse = boolOrLeftFalseChildless
            (isChildOf @{nameEq} selected (Bind current observed))
            (hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected rest) noChild
          tailFalse = boolOrRightFalseChildless
            (isChildOf @{nameEq} selected (Bind current observed))
            (hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected rest) noChild
          replacedTailFalse = hasChildInReplaceFalse nameEq selected changed next
            old rest found sameParent tailFalse
      in rewrite headFalse in rewrite replacedTailFalse in Refl

0 hasChildReplaceFalse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected, changed : name) ->
  (next, old : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} changed source = Just old ->
  fiberParent next = fiberParent old ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected source = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (replaceBinding @{nameEq} changed next source) =
    False
hasChildReplaceFalse nameEq selected changed next old
  (MkCoeffectContext entries unique) found sameParent noChild =
    hasChildInReplaceFalse nameEq selected changed next old entries found
      sameParent noChild

0 NonInsertAction : Action name key value world error -> Type
NonInsertAction (OInsert actor parent component) = Void
NonInsertAction (ORetire actor) = ()
NonInsertAction (ORemove actor) = ()
NonInsertAction (LBegin actor) = ()
NonInsertAction (LAdvance actor) = ()
NonInsertAction (LDivert actor) = ()
NonInsertAction (LLeave actor) = ()
NonInsertAction (LUnload actor) = ()

0 successfulNonInsertSource :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  NonInsertAction action ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} (actionOwner action) (registry before) = Just fiber)
successfulNonInsertSource nameEq keyEq (OInsert actor parent component)
  contra before afterState tag equation = void contra
successfulNonInsertSource nameEq keyEq (ORetire actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry before)) proof found
  successfulNonInsertSource nameEq keyEq (ORetire actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulNonInsertSource nameEq keyEq (ORetire actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulNonInsertSource nameEq keyEq (ORemove actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry before)) proof found
  successfulNonInsertSource nameEq keyEq (ORemove actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulNonInsertSource nameEq keyEq (ORemove actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulNonInsertSource nameEq keyEq (LBegin actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry before)) proof found
  successfulNonInsertSource nameEq keyEq (LBegin actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulNonInsertSource nameEq keyEq (LBegin actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulNonInsertSource nameEq keyEq (LAdvance actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry before)) proof found
  successfulNonInsertSource nameEq keyEq (LAdvance actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulNonInsertSource nameEq keyEq (LAdvance actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulNonInsertSource nameEq keyEq (LDivert actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry before)) proof found
  successfulNonInsertSource nameEq keyEq (LDivert actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulNonInsertSource nameEq keyEq (LDivert actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulNonInsertSource nameEq keyEq (LLeave actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry before)) proof found
  successfulNonInsertSource nameEq keyEq (LLeave actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulNonInsertSource nameEq keyEq (LLeave actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulNonInsertSource nameEq keyEq (LUnload actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} actor (registry before)) proof found
  successfulNonInsertSource nameEq keyEq (LUnload actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulNonInsertSource nameEq keyEq (LUnload actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)

data ChildlessRegistryUpdateView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  Registry name key value world error -> Registry name key value world error ->
  Type where
  ChildlessViewedInsert :
    (fiber : Fiber name key value world error) ->
    (absent : lookupFiber @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} actor source = Nothing) ->
    target = insertBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor fiber source absent ->
    ChildlessRegistryUpdateView {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq actor source target
  ChildlessViewedReplace :
    (next, old : Fiber name key value world error) ->
    (found : lookupFiber @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} actor source = Just old) ->
    (sameParent : fiberParent next = fiberParent old) ->
    target = replaceBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor next source ->
    ChildlessRegistryUpdateView {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq actor source target
  ChildlessViewedDelete :
    (old : Fiber name key value world error) ->
    (found : lookupFiber @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} actor source = Just old) ->
    target = deleteBinding @{nameEq} {key = name}
      {value = FiberAt name key value world error} actor source ->
    ChildlessRegistryUpdateView {name = name} {key = key} {value = value}
      {world = world} {error = error} nameEq actor source target

0 childlessRegistryUpdateView :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  ChildlessRegistryUpdateView {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq actor source target
childlessRegistryUpdateView nameEq actor source _
  (LocalInsert fiber absent) = ChildlessViewedInsert fiber absent Refl
childlessRegistryUpdateView nameEq actor source _
  (LocalReplace next {oldFiber} {oldFound} {staticParent}) =
    ChildlessViewedReplace next oldFiber oldFound staticParent Refl
childlessRegistryUpdateView nameEq actor source _
  (LocalDelete {oldFiber} {oldFound}) =
    ChildlessViewedDelete oldFiber oldFound Refl

0 nonInsertPreservesNoChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  NonInsertAction action ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry before) = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry afterState) = False
nonInsertPreservesNoChild {name} {key} {world} {error} {value}
  nameEq keyEq selected action nonInsert before afterState tag raw noChild =
    let update = applyActionLocalUpdate nameEq keyEq action before afterState tag raw
        viewed = childlessRegistryUpdateView nameEq (actionOwner action)
          (registry before) (registry afterState) (systemRegistryUpdate update)
        Property : Registry name key value world error -> Type
        Property target = hasChild @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} selected target = False
    in case viewed of
      ChildlessViewedInsert fiber absent targetShape =>
        let (old ** present) = successfulNonInsertSource nameEq keyEq action
              nonInsert before afterState tag raw
        in void (nothingIsNotJust (trans (sym absent) present))
      ChildlessViewedReplace next old found sameParent targetShape =>
        let replaced = hasChildReplaceFalse nameEq selected
              (actionOwner action) next old (registry before) found sameParent
              noChild
        in replace {p = Property} (sym targetShape) replaced
      ChildlessViewedDelete old found targetShape =>
        let deleted = hasChildDeleteFalse nameEq selected (actionOwner action)
              (registry before) noChild
        in replace {p = Property} (sym targetShape) deleted

0 oInsertSourceAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert inserted parent component) before =
    Just (tag, afterState) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} inserted (registry before) = Nothing
oInsertSourceAbsent {name} {key} {world} {error} {value}
  nameEq keyEq inserted parent component
  (MkSystemState ambient source) afterState tag raw
  with (parentPresent @{nameEq} parent source &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers source)) proof guards
  oInsertSourceAbsent nameEq keyEq inserted parent component
    (MkSystemState ambient source) afterState tag raw | False =
      void (nothingIsNotJust raw)
  oInsertSourceAbsent nameEq keyEq inserted parent component
    (MkSystemState ambient source) afterState tag raw | True
    with (setFresh @{nameEq} inserted (freshFiber component parent) source)
      proof insertedResult
    oInsertSourceAbsent nameEq keyEq inserted parent component
      (MkSystemState ambient source) afterState tag raw | True | Nothing =
        void (nothingIsNotJust raw)
    oInsertSourceAbsent nameEq keyEq inserted parent component
      (MkSystemState ambient source) afterState tag raw | True | Just applied =
        setFreshAbsent nameEq inserted (freshFiber component parent) source
          applied insertedResult

0 oInsertPreservesNoChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert inserted parent component) before =
    Just (tag, afterState) ->
  Not (parent = ChildOf selected) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry before) = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} selected (registry afterState) = False
oInsertPreservesNoChild {name} {key} {world} {error} {value}
  nameEq keyEq selected inserted parent component
  (MkSystemState ambient source) afterState tag raw parentDifferent noChild
  with (parentPresent @{nameEq} parent source &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers source)) proof guards
  oInsertPreservesNoChild nameEq keyEq selected inserted parent component
    (MkSystemState ambient source) afterState tag raw parentDifferent noChild |
    False = void (nothingIsNotJust raw)
  oInsertPreservesNoChild nameEq keyEq selected inserted parent component
    (MkSystemState ambient source) afterState tag raw parentDifferent noChild |
    True with (setFresh @{nameEq} inserted (freshFiber component parent) source)
      proof insertedResult
    oInsertPreservesNoChild nameEq keyEq selected inserted parent component
      (MkSystemState ambient source) afterState tag raw parentDifferent noChild |
      True | Nothing = void (nothingIsNotJust raw)
    oInsertPreservesNoChild nameEq keyEq selected inserted parent component
      (MkSystemState ambient source) afterState tag raw parentDifferent noChild |
      True | Just applied =
        case justInjectiveChildless raw of
          Refl => rewrite setFreshAfter nameEq inserted
            (freshFiber component parent) source applied insertedResult in
            hasChildInsertFalse nameEq selected inserted component parent source
              (setFreshAbsent nameEq inserted (freshFiber component parent)
                source applied insertedResult)
              parentDifferent noChild

0 registrationYieldReloading :
  (nameEq : DecEq name) -> (selected : name) ->
  (before : SystemState name key value world error) ->
  ParentRegistrationYield protocol nameEq selected component before ->
  reloadingAt @{nameEq} selected before = True
registrationYieldReloading nameEq selected before yielded =
  rewrite parentFoundAtYield yielded in
  rewrite parentAtYield yielded in Refl

0 inactiveFiberNotReloading :
  (nameEq : DecEq name) -> (selected : name) ->
  (before : SystemState name key value world error) ->
  InactiveFiberAt name key world error value nameEq selected before ->
  reloadingAt @{nameEq} selected before = False
inactiveFiberNotReloading nameEq selected before
  (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    rewrite found in Refl

0 inactiveCannotLicenseRegistration :
  (nameEq : DecEq name) -> (selected : name) ->
  (before : SystemState name key value world error) ->
  InactiveFiberAt name key world error value nameEq selected before ->
  ParentRegistrationYield protocol nameEq selected component before -> Void
inactiveCannotLicenseRegistration nameEq selected before inactive yielded =
  case trans (sym (inactiveFiberNotReloading nameEq selected before inactive))
    (registrationYieldReloading nameEq selected before yielded) of Refl impossible

0 currentGenerationElemFromLookup :
  (nameEq : DecEq name) -> (selected : name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  lookupCurrentGeneration @{nameEq} selected live = Just generation ->
  Elem (selected, generation) live
currentGenerationElemFromLookup nameEq selected generation [] current =
  case current of Refl impossible
currentGenerationElemFromLookup nameEq selected generation
  ((candidate, observed) :: rest) current
  with (decEq @{nameEq} selected candidate)
  currentGenerationElemFromLookup nameEq candidate generation
    ((candidate, observed) :: rest) current | Yes Refl =
      case justInjectiveChildless current of Refl => Here
  currentGenerationElemFromLookup nameEq selected generation
    ((candidate, observed) :: rest) current | No distinct =
      There (currentGenerationElemFromLookup nameEq selected generation rest
        current)

0 foreignInsertionParentDifferent :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  (selected, inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before : SystemState name key value world error) ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert inserted parent component) before rest ->
  InactiveFiberAt name key world error value nameEq selected before ->
  Not (parent = ChildOf selected)
foreignInsertionParentDifferent protocol nameEq selected inserted Root component
  before discipline inactive = \same => case same of Refl impossible
foreignInsertionParentDifferent protocol nameEq selected inserted
  (ChildOf candidate) component before (yielded, retirement) inactive
  with (decEq @{nameEq} selected candidate)
  foreignInsertionParentDifferent protocol nameEq candidate inserted
    (ChildOf candidate) component before (yielded, retirement) inactive |
    Yes Refl = \same => inactiveCannotLicenseRegistration nameEq candidate before
      inactive yielded
  foreignInsertionParentDifferent protocol nameEq selected inserted
    (ChildOf candidate) component before (yielded, retirement) inactive |
    No distinct = \same => distinct
      (sym (childOfInjectiveChildless same))

0 ownerInsertionParentDifferent :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert selected parent component) before rest ->
  Not (parent = ChildOf selected)
ownerInsertionParentDifferent protocol nameEq keyEq selected Root component
  before afterState tag raw discipline = \same => case same of Refl impossible
ownerInsertionParentDifferent protocol nameEq keyEq selected
  (ChildOf candidate) component before afterState tag raw
  (yielded, retirement) with (decEq @{nameEq} selected candidate)
  ownerInsertionParentDifferent protocol nameEq keyEq candidate
    (ChildOf candidate) component before afterState tag raw
    (yielded, retirement) | Yes Refl = \same =>
      let absent = oInsertSourceAbsent nameEq keyEq candidate
            (ChildOf candidate) component before afterState tag raw
      in nothingIsNotJust
        (trans (sym absent) (parentFoundAtYield yielded))
  ownerInsertionParentDifferent protocol nameEq keyEq selected
    (ChildOf candidate) component before afterState tag raw
    (yielded, retirement) | No distinct = \same => distinct
      (sym (childOfInjectiveChildless same))

public export
0 currentRegisteredChildlessStep :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  RegistrationStepDiscipline protocol nameEq action before rest ->
  registryWellFormed @{nameEq} @{keyEq} before = True ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live before ->
  CurrentRegisteredChildless name key world error value nameEq registered live
    before ->
  CurrentRegisteredChildless name key world error value nameEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) afterState
currentRegisteredChildlessStep protocol nameEq keyEq registered ordinal live
  unique action before afterState tag raw discipline sourceWellFormed noBegin
  sourceInactive sourceChildless selected generation targetPresent member =
    let targetUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
        targetCurrent = lookupCurrentGenerationFromElem nameEq
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          targetUnique targetPresent
    in case decEq @{nameEq} selected (actionOwner action) of
      No distinct =>
        let sourceCurrent = trans
              (sym (lookupAdvanceGenerationOther nameEq ordinal action selected
                distinct live)) targetCurrent
            sourcePresent = currentGenerationElemFromLookup nameEq selected
              generation live sourceCurrent
            inactive = sourceInactive selected generation member sourceCurrent
            noChild = sourceChildless selected generation sourcePresent member
        in case action of
          OInsert inserted parent component =>
            oInsertPreservesNoChild nameEq keyEq selected inserted parent component
              before afterState tag raw
              (foreignInsertionParentDifferent protocol nameEq selected inserted
                parent component before discipline inactive)
              noChild
          ORetire actor => nonInsertPreservesNoChild nameEq keyEq selected
            (ORetire actor) () before afterState tag raw noChild
          ORemove actor => nonInsertPreservesNoChild nameEq keyEq selected
            (ORemove actor) () before afterState tag raw noChild
          LBegin actor => nonInsertPreservesNoChild nameEq keyEq selected
            (LBegin actor) () before afterState tag raw noChild
          LAdvance actor => nonInsertPreservesNoChild nameEq keyEq selected
            (LAdvance actor) () before afterState tag raw noChild
          LDivert actor => nonInsertPreservesNoChild nameEq keyEq selected
            (LDivert actor) () before afterState tag raw noChild
          LLeave actor => nonInsertPreservesNoChild nameEq keyEq selected
            (LLeave actor) () before afterState tag raw noChild
          LUnload actor => nonInsertPreservesNoChild nameEq keyEq selected
            (LUnload actor) () before afterState tag raw noChild
      Yes ownerSame => case ownerSame of
        Refl => case action of
          OInsert selected parent component =>
            let absent = oInsertSourceAbsent nameEq keyEq selected parent component
                  before afterState tag raw
                sourceNoChild = wellFormedAbsentHasNoChild nameEq keyEq selected
                  before sourceWellFormed absent
                parentDifferent = ownerInsertionParentDifferent protocol nameEq
                  keyEq selected parent component before afterState tag raw
                  discipline
            in oInsertPreservesNoChild nameEq keyEq selected selected parent
              component before afterState tag raw parentDifferent sourceNoChild
          ORetire selected =>
            let sourcePresent = currentGenerationElemFromLookup nameEq selected
                  generation live targetCurrent
                noChild = sourceChildless selected generation sourcePresent member
            in nonInsertPreservesNoChild nameEq keyEq selected
              (ORetire selected) () before afterState tag raw noChild
          ORemove selected =>
            void (nothingIsNotJust
              (trans (sym (lookupDeleteCurrentSelf nameEq selected live unique))
                targetCurrent))
          LBegin selected =>
            void (noBegin ItIsLBegin (generation ** (targetCurrent, member)))
          LAdvance selected =>
            let sourcePresent = currentGenerationElemFromLookup nameEq selected
                  generation live targetCurrent
                noChild = sourceChildless selected generation sourcePresent member
            in nonInsertPreservesNoChild nameEq keyEq selected
              (LAdvance selected) () before afterState tag raw noChild
          LDivert selected =>
            let sourcePresent = currentGenerationElemFromLookup nameEq selected
                  generation live targetCurrent
                noChild = sourceChildless selected generation sourcePresent member
            in nonInsertPreservesNoChild nameEq keyEq selected
              (LDivert selected) () before afterState tag raw noChild
          LLeave selected =>
            let sourcePresent = currentGenerationElemFromLookup nameEq selected
                  generation live targetCurrent
                noChild = sourceChildless selected generation sourcePresent member
            in nonInsertPreservesNoChild nameEq keyEq selected
              (LLeave selected) () before afterState tag raw noChild
          LUnload selected =>
            let sourcePresent = currentGenerationElemFromLookup nameEq selected
                  generation live targetCurrent
                noChild = sourceChildless selected generation sourcePresent member
            in nonInsertPreservesNoChild nameEq keyEq selected
              (LUnload selected) () before afterState tag raw noChild

0 emptyCurrentRegisteredInactiveChildless :
  CurrentRegisteredInactiveFibers name key world error value nameEq registered []
    state
emptyCurrentRegisteredInactiveChildless selected generation member current =
  case current of Refl impossible

0 emptyCurrentRegisteredChildless :
  CurrentRegisteredChildless name key world error value nameEq registered [] state
emptyCurrentRegisteredChildless selected generation present member =
  case present of Refl impossible

||| Forward induction combines the already-proved exact-generation Inactive
||| invariant with disciplined registration. A child insertion under a current R
||| generation would require that Inactive parent to be Reloading, while a fresh
||| raw-name reissue is protected by well-formed parent closure.
public export
0 currentRegisteredChildlessTrace :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  RegistrationDiscipline protocol nameEq trace ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  NoRegisteredEpisode nameEq registered ordinal live trace ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live first ->
  CurrentRegisteredChildless name key world error value nameEq registered live
    first ->
  CurrentRegisteredChildless name key world error value nameEq registered
    finalLive finalState
currentRegisteredChildlessTrace protocol nameEq keyEq registered ordinal live
  unique NoTransitions ordinal live GenerationTraceScanEnd AlignedEnd
  RegistrationDisciplineEnd sourceWellFormed NoRegisteredEpisodeEnd
  sourceInactive sourceChildless = sourceChildless
currentRegisteredChildlessTrace protocol nameEq keyEq registered ordinal live
  unique
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  finalOrdinal finalLive
  (GenerationTraceScanStep (Fired nameEq keyEq action tag checked) rest scanTail)
  (AlignedStep action tag checked rest alignedTail)
  (RegistrationDisciplineStep
    (Fired nameEq keyEq action tag checked) rest stepDiscipline tailDiscipline)
  sourceWellFormed
  (NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest noBegin
    noEpisodeTail)
  sourceInactive sourceChildless =
    let raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
        nextInactive = currentRegisteredInactiveStep nameEq keyEq registered
          ordinal live unique action _ _ tag raw noBegin sourceInactive
        nextChildless = currentRegisteredChildlessStep protocol nameEq keyEq
          registered ordinal live unique action _ _ tag raw stepDiscipline
          sourceWellFormed noBegin sourceInactive sourceChildless
        nextWellFormed = preservationTheoremProof nameEq keyEq action _ _ tag
          sourceWellFormed raw
    in currentRegisteredChildlessTrace protocol nameEq keyEq registered
      (S ordinal) (advanceGenerationEnvironment @{nameEq} ordinal action live)
      nextUnique rest finalOrdinal finalLive scanTail alignedTail tailDiscipline
      nextWellFormed noEpisodeTail nextInactive nextChildless

||| Obligation 4(b)(1): at a reached checked boundary, every current exact R
||| generation is childless. `NoRegisteredEpisode` supplies exact-generation
||| selected-episode provenance; `RegistrationDiscipline` prevents any generated
||| child from being licensed by its necessarily Inactive parent. The stronger
||| proof does not need to re-open `RegisteredGenerationsDuring`: that premise is
||| needed to identify R, while this theorem works for any generation list with
||| the same exact no-episode evidence.
public export
0 reachedCurrentRegisteredChildless :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  RegistrationDiscipline protocol nameEq trace ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  NoRegisteredEpisode nameEq registered 0 [] trace ->
  CurrentRegisteredChildless name key world error value nameEq registered
    finalLive finalState
reachedCurrentRegisteredChildless protocol nameEq keyEq registered trace
  finalOrdinal finalLive scan aligned discipline initialWellFormed noEpisodes =
    currentRegisteredChildlessTrace protocol nameEq keyEq registered 0 []
      UniqueNil trace finalOrdinal finalLive scan aligned discipline
      initialWellFormed noEpisodes emptyCurrentRegisteredInactiveChildless
      emptyCurrentRegisteredChildless

||| Closed boundary-plan assembly with childlessness discharged from the public
||| Lemma-72 premises. This is the direct replacement for supplying
||| `CurrentRegisteredChildless` by hand.
public export
0 reachedDisciplinedBoundaryGivesDeletionPlan :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (scan : GenerationTraceScan nameEq 0 [] trace finalOrdinal finalLive) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  RegistrationDiscipline protocol nameEq trace ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  (noEpisodes : NoRegisteredEpisode nameEq registered 0 [] trace) ->
  CurrentRegisteredPlanResult name key world error value nameEq registered
    finalLive (registry finalState)
reachedDisciplinedBoundaryGivesDeletionPlan protocol nameEq keyEq registered
  trace finalOrdinal finalLive scan aligned discipline initialWellFormed
  noEpisodes =
    DGamma.CP4DeletionPlanBoundary.reachedBoundaryGivesDeletionPlan nameEq keyEq
      registered trace finalOrdinal
      finalLive scan aligned noEpisodes
      (reachedCurrentRegisteredChildless protocol nameEq keyEq registered trace
        finalOrdinal finalLive scan aligned discipline initialWellFormed
        noEpisodes)
