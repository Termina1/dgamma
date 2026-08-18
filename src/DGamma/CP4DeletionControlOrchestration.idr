module DGamma.CP4DeletionControlOrchestration

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControl
import DGamma.CP4DeletionControlBegin
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionPlanSuccess
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

falseNotTrueOrchestration : False = True -> Void
falseNotTrueOrchestration Refl impossible

trueNotFalseOrchestration : True = False -> Void
trueNotFalseOrchestration Refl impossible

justInjectiveOrchestration : Just left = Just right -> left = right
justInjectiveOrchestration Refl = Refl

notTrueMeansFalseOrchestration : (flag : Bool) ->
  not flag = True -> flag = False
notTrueMeansFalseOrchestration False valid = Refl
notTrueMeansFalseOrchestration True valid =
  void (falseNotTrueOrchestration valid)

falseMeansNotTrueOrchestration : (flag : Bool) ->
  flag = False -> not flag = True
falseMeansNotTrueOrchestration False Refl = Refl

boolAndLeftOrchestration : (left, right : Bool) ->
  left && right = True -> left = True
boolAndLeftOrchestration False right valid =
  void (falseNotTrueOrchestration valid)
boolAndLeftOrchestration True right valid = Refl

boolAndRightOrchestration : (left, right : Bool) ->
  left && right = True -> right = True
boolAndRightOrchestration False right valid =
  void (falseNotTrueOrchestration valid)
boolAndRightOrchestration True False valid =
  void (falseNotTrueOrchestration valid)
boolAndRightOrchestration True True valid = Refl

andBothTrueOrchestration : (left, right : Bool) ->
  left = True -> right = True -> left && right = True
andBothTrueOrchestration True True Refl Refl = Refl

0 setFreshFromAbsent :
  {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (selected : key) -> (next : value selected) ->
  (before : CoeffectContext key value) ->
  lookupBinding @{keyEq} selected before = Nothing ->
  (applied : CoeffectApplied before **
    setFresh @{keyEq} selected next before = Just applied)
setFreshFromAbsent keyEq selected next before absent
  with (lookupBinding @{keyEq} selected before) proof found
  setFreshFromAbsent keyEq selected next before Refl | Just old impossible
  setFreshFromAbsent keyEq selected next before absent | Nothing = (_ ** Refl)

||| The only extra guard needed to replay O-Insert after deleting a leaf: a
||| child insertion must not name the deleted leaf as its parent. Root insertion
||| and the other orchestration actions carry no parent-side obligation.
public export
ParentOutside : Parent name -> name -> Type
ParentOutside Root removed = ()
ParentOutside (ChildOf parent) removed = Not (parent = removed)

public export
InsertionParentOutside :
  Action name key value world error -> name -> Type
InsertionParentOutside (OInsert inserted parent component) removed =
  ParentOutside parent removed
InsertionParentOutside action removed = ()

0 parentPresentAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  (parent : Parent name) -> (removed : name) ->
  ParentOutside parent removed ->
  (fibers : Registry name key value world error) ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent fibers = True ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent
    (deleteBinding @{nameEq} removed fibers) = True
parentPresentAfterInactiveDelete nameEq Root removed outside fibers present = Refl
parentPresentAfterInactiveDelete nameEq (ChildOf parent) removed distinct fibers
  present =
    rewrite lookupDeleteOther parent removed distinct fibers in present

registryFibersDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (removed : name) ->
  (fibers : Registry name key value world error) ->
  registryFibers {name = name} {key = key} {value = value} {world = world}
    {error = error} (deleteBinding @{nameEq} removed fibers) =
  deleteEntries @{nameEq} {key = name}
    {value = FiberAt name key value world error} removed
    (registryFibers {name = name} {key = key} {value = value} {world = world}
      {error = error} fibers)
registryFibersDelete nameEq removed (MkCoeffectContext entries unique) = Refl

0 insertRawAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (removed : name) -> Not (inserted = removed) ->
  InsertionParentOutside
    (the (Action name key value world error)
      (OInsert inserted parent component)) removed ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} (OInsert inserted parent component)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error)
      (OInsert inserted parent component))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
insertRawAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq inserted parent component removed distinct parentOutside ambient
  fibers raw
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers)) proof sourceGuards
  insertRawAfterInactiveDelete nameEq keyEq inserted parent component removed
    distinct parentOutside ambient fibers raw | False =
      void (nothingIsNotJust raw)
  insertRawAfterInactiveDelete nameEq keyEq inserted parent component removed
    distinct parentOutside ambient fibers raw | True
    with (setFresh @{nameEq} inserted (freshFiber component parent) fibers)
      proof sourceInserted
    insertRawAfterInactiveDelete nameEq keyEq inserted parent component removed
      distinct parentOutside ambient fibers raw | True | Nothing =
        void (nothingIsNotJust raw)
    insertRawAfterInactiveDelete nameEq keyEq inserted parent component removed
      distinct parentOutside ambient fibers raw | True | Just applied =
        let targetFibers : Registry name key value world error
            targetFibers = deleteBinding @{nameEq} removed fibers
            sourceParent = boolAndLeftOrchestration
              (parentPresent @{nameEq} parent fibers)
              (provisionsDisjointFrom @{keyEq} (componentProvisions component)
                (registryFibers fibers)) sourceGuards
            sourceDisjoint = boolAndRightOrchestration
              (parentPresent @{nameEq} parent fibers)
              (provisionsDisjointFrom @{keyEq} (componentProvisions component)
                (registryFibers fibers)) sourceGuards
            0 targetParent : parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              targetFibers = True
            targetParent = parentPresentAfterInactiveDelete nameEq parent removed
              parentOutside fibers sourceParent
            0 deletedDisjoint : provisionsDisjointFrom @{keyEq}
              {name = name} {key = key} {value = value} {world = world}
              {error = error} (componentProvisions component)
              (deleteEntries @{nameEq} {key = name}
                {value = FiberAt name key value world error} removed
                (registryFibers {name = name} {key = key} {value = value}
                  {world = world} {error = error} fibers)) = True
            deletedDisjoint = provisionsDisjointDelete nameEq keyEq
              (componentProvisions component) (registryFibers fibers) removed
              sourceDisjoint
            0 targetDisjoint : provisionsDisjointFrom @{keyEq}
              {name = name} {key = key} {value = value} {world = world}
              {error = error} (componentProvisions component)
              (registryFibers {name = name} {key = key} {value = value}
                {world = world} {error = error} targetFibers) = True
            targetDisjoint = replace
              {p = \entries => provisionsDisjointFrom @{keyEq}
                {name = name} {key = key} {value = value} {world = world}
                {error = error} (componentProvisions component) entries = True}
              (sym (registryFibersDelete nameEq removed fibers)) deletedDisjoint
            0 sourceAbsent : lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} inserted fibers =
              Nothing
            sourceAbsent = setFreshAbsent nameEq inserted
              (freshFiber component parent) fibers applied sourceInserted
            0 targetAbsent : lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} inserted
              targetFibers = Nothing
            targetAbsent = trans
              (lookupDeleteOther inserted removed distinct fibers) sourceAbsent
        in case setFreshFromAbsent nameEq inserted
          (freshFiber component parent) targetFibers targetAbsent of
          (targetApplied ** targetInserted) =>
            let targetRaw : (applyAction @{nameEq} @{keyEq} {name = name}
                  {key = key} {value = value} {world = world} {error = error}
                  (OInsert inserted parent component)
                  (MkSystemState ambient targetFibers) = Just (OInsertTag,
                    MkSystemState ambient (coeffectAfter targetApplied)))
                targetRaw = rewrite targetParent in rewrite targetDisjoint in
                  rewrite targetInserted in Refl
            in MkRawActionResult OInsertTag
              (MkSystemState ambient (coeffectAfter targetApplied)) targetRaw

0 retireRawAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, removed : name) -> Not (selected = removed) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} (ORetire selected)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (ORetire selected))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
retireRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient fibers
  raw with (lookupFiber @{nameEq} selected fibers) proof sourceFound
  retireRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient fibers
    raw | Nothing = void (nothingIsNotJust raw)
  retireRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient fibers
    raw | Just fiber =
      let 0 targetFound : (lookupFiber @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} selected
            (deleteBinding @{nameEq} removed fibers) = Just fiber)
          targetFound = trans (lookupDeleteOther selected removed distinct fibers)
            sourceFound
          targetRaw : (applyAction @{nameEq} @{keyEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} (ORetire selected)
            (MkSystemState ambient (deleteBinding @{nameEq} removed fibers)) =
            Just (ORetireTag, MkSystemState ambient
              (replaceBinding @{nameEq} selected (retireFiber fiber)
                (deleteBinding @{nameEq} removed fibers))))
          targetRaw = rewrite targetFound in Refl
      in MkRawActionResult ORetireTag
        (MkSystemState ambient
          (replaceBinding @{nameEq} selected (retireFiber fiber)
            (deleteBinding @{nameEq} removed fibers))) targetRaw

0 removeRawAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, removed : name) -> Not (selected = removed) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} (ORemove selected)
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq
    (the (Action name key value world error) (ORemove selected))
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
removeRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient fibers
  raw with (lookupFiber @{nameEq} selected fibers) proof sourceFound
  removeRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient fibers
    raw | Nothing = void (nothingIsNotJust raw)
  removeRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient fibers
    raw | Just fiber with (retired fiber && isInactive (fiberLifecycle fiber) &&
      not (hasChild @{nameEq} selected fibers)) proof sourceGuards
    removeRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient
      fibers raw | Just fiber | False = void (nothingIsNotJust raw)
    removeRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient
      fibers raw | Just fiber | True =
        let targetFibers : Registry name key value world error
            targetFibers = deleteBinding @{nameEq} removed fibers
            0 targetFound : lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} selected
              targetFibers = Just fiber
            targetFound = trans (lookupDeleteOther selected removed distinct fibers)
              sourceFound
            sourceRetired = boolAndLeftOrchestration (retired fiber)
              (isInactive (fiberLifecycle fiber) &&
                not (hasChild @{nameEq} selected fibers)) sourceGuards
            sourceTail = boolAndRightOrchestration (retired fiber)
              (isInactive (fiberLifecycle fiber) &&
                not (hasChild @{nameEq} selected fibers)) sourceGuards
            sourceInactive = boolAndLeftOrchestration (isInactive (fiberLifecycle fiber))
              (not (hasChild @{nameEq} selected fibers)) sourceTail
            sourceNotChild = boolAndRightOrchestration (isInactive (fiberLifecycle fiber))
              (not (hasChild @{nameEq} selected fibers)) sourceTail
            sourceNoChild = notTrueMeansFalseOrchestration
              (hasChild @{nameEq} selected fibers) sourceNotChild
            0 targetNoChild : hasChild @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} selected
              targetFibers = False
            targetNoChild = hasChildDeleteFalse {name = name} {key = key}
              {value = value} {world = world} {error = error} nameEq selected
              removed fibers sourceNoChild
            0 targetNotChild : not (hasChild @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} selected
              targetFibers) = True
            targetNotChild = falseMeansNotTrueOrchestration
              (hasChild @{nameEq} selected targetFibers) targetNoChild
            0 targetGuards : (retired fiber && isInactive (fiberLifecycle fiber) &&
              not (hasChild @{nameEq} {name = name} {key = key} {value = value}
                {world = world} {error = error} selected targetFibers) = True)
            targetGuards = andBothTrueOrchestration (retired fiber)
              (isInactive (fiberLifecycle fiber) &&
                not (hasChild @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} selected
                  targetFibers)) sourceRetired
              (andBothTrueOrchestration (isInactive (fiberLifecycle fiber))
                (not (hasChild @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} selected
                  targetFibers)) sourceInactive
                targetNotChild)
            targetRaw : (applyAction @{nameEq} @{keyEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              (ORemove selected) (MkSystemState ambient targetFibers) =
              Just (ORemoveTag, MkSystemState ambient
                (deleteBinding @{nameEq} selected targetFibers)))
            targetRaw = rewrite targetFound in rewrite targetGuards in Refl
        in MkRawActionResult ORemoveTag
          (MkSystemState ambient
            (deleteBinding @{nameEq} selected targetFibers)) targetRaw

||| Exhaustive orchestration applicability after deleting one distinct Inactive
||| leaf. Unlike lifecycle replay, O-Insert exposes its parent-side condition:
||| deleting the very parent of a retained insertion would invalidate the step.
public export
0 orchestrationApplicableAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (removed : name) -> Not (actionOwner action = removed) ->
  InsertionParentOutside action removed ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} action (MkSystemState ambient fibers) =
    Just (tag, afterState) ->
  RawActionResult name key world error value nameEq keyEq action
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
orchestrationApplicableAfterInactiveDelete nameEq keyEq
  (OInsert inserted parent component) orchestration removed distinct
  parentOutside ambient fibers raw =
    insertRawAfterInactiveDelete nameEq keyEq inserted parent component removed
      distinct parentOutside ambient fibers raw
orchestrationApplicableAfterInactiveDelete nameEq keyEq (ORetire selected)
  orchestration removed distinct parentOutside ambient fibers raw =
    retireRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient
      fibers raw
orchestrationApplicableAfterInactiveDelete nameEq keyEq (ORemove selected)
  orchestration removed distinct parentOutside ambient fibers raw =
    removeRawAfterInactiveDelete nameEq keyEq selected removed distinct ambient
      fibers raw
orchestrationApplicableAfterInactiveDelete nameEq keyEq (LBegin selected)
  orchestration removed distinct parentOutside ambient fibers raw =
    void (trueNotFalseOrchestration orchestration)
orchestrationApplicableAfterInactiveDelete nameEq keyEq (LAdvance selected)
  orchestration removed distinct parentOutside ambient fibers raw =
    void (trueNotFalseOrchestration orchestration)
orchestrationApplicableAfterInactiveDelete nameEq keyEq (LDivert selected)
  orchestration removed distinct parentOutside ambient fibers raw =
    void (trueNotFalseOrchestration orchestration)
orchestrationApplicableAfterInactiveDelete nameEq keyEq (LLeave selected)
  orchestration removed distinct parentOutside ambient fibers raw =
    void (trueNotFalseOrchestration orchestration)
orchestrationApplicableAfterInactiveDelete nameEq keyEq (LUnload selected)
  orchestration removed distinct parentOutside ambient fibers raw =
    void (trueNotFalseOrchestration orchestration)

||| Checked companion to the raw orchestration frame. The leaf condition first
||| preserves Definition 58; raw Preservation then admits the replayed target
||| into the checked LTS.
public export
0 checkedOrchestrationAfterInactiveDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (removed : name) -> Not (actionOwner action = removed) ->
  InsertionParentOutside action removed ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (removedComponent : Component key value world error) ->
  (removedParent : Parent name) -> (removedRetired : Bool) ->
  (removedTable : OwnedTable key value
    (componentProvisions removedComponent)) ->
  (removedOutcome : Maybe error) ->
  (removedFound : lookupFiber @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} removed fibers = Just
    (MkFiber removedComponent removedParent removedRetired removedTable
      (Inactive removedOutcome))) ->
  (noChild : hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed fibers = False) ->
  (sourceWellFormed : registryWellFormed @{nameEq} @{keyEq} {name = name}
    {key = key} {value = value} {world = world} {error = error}
    (MkSystemState ambient fibers) = True) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} action
    (MkSystemState ambient fibers) = Just (tag, afterState) ->
  TransitionResult {name = name} {key = key} {value = value} {world = world}
    {error = error}
    (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
checkedOrchestrationAfterInactiveDelete {name} {key} {world} {error} {value}
  nameEq keyEq action orchestration removed distinct parentOutside ambient fibers
  removedComponent removedParent removedRetired removedTable removedOutcome
  removedFound noChild sourceWellFormed checked =
    let 0 raw = checkedActionProjects nameEq keyEq action
          (MkSystemState ambient fibers) _ _ checked
        replayRaw = orchestrationApplicableAfterInactiveDelete nameEq keyEq action
          orchestration removed distinct parentOutside ambient fibers raw
        0 replaySourceWellFormed = registryWellFormedInactiveDelete nameEq keyEq
          ambient removed removedComponent removedParent removedRetired
          removedTable removedOutcome fibers removedFound noChild sourceWellFormed
    in case replayRaw of
      MkRawActionResult replayTag replayAfter replayEquation =>
        let 0 replayTargetWellFormed = preservationTheoremProof nameEq keyEq
              action
              (MkSystemState ambient (deleteBinding @{nameEq} removed fibers))
              replayAfter replayTag replaySourceWellFormed replayEquation
            0 replayChecked : (checkedApplyAction @{nameEq} @{keyEq} action
              (MkSystemState ambient (deleteBinding @{nameEq} removed fibers)) =
              Just (replayTag, replayAfter))
            replayChecked = rewrite replayEquation in
              rewrite replayTargetWellFormed in Refl
        in MkTransitionResult replayAfter replayTag
          (Fired nameEq keyEq action replayTag replayChecked)

||| Per-action proof that both the owner and, for child O-Insert, its parent are
||| outside every leaf erased by a plan. Packaging the two obligations together
||| prevents the plan iterator from silently forgetting O-Insert's parent guard.
public export
data OrchestrationOutsideDeletionPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  (action : Action name key value world error) ->
  {source, target : Registry name key value world error} ->
  InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target -> Type where
  OrchestrationOutsideDeletionEnd :
    OrchestrationOutsideDeletionPlan action NoInactiveLeafDeletion
  OrchestrationOutsideDeletionStep :
    {source, target : Registry name key value world error} ->
    {removed : name} ->
    {component : Component key value world error} ->
    {parent : Parent name} -> {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    {outcome : Maybe error} ->
    {0 found : lookupFiber @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} removed source = Just
      (MkFiber component parent retiredFlag table (Inactive outcome))} ->
    {0 noChild : hasChild @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} removed source = False} ->
    (0 rest : InactiveLeafDeletionPlan {name = name} {key = key}
      {value = value} {world = world} {error = error} nameEq
      (deleteBinding @{nameEq} removed source) target) ->
    (0 ownerOutside : Not (actionOwner action = removed)) ->
    (0 parentOutside : InsertionParentOutside action removed) ->
    OrchestrationOutsideDeletionPlan action rest ->
    OrchestrationOutsideDeletionPlan action
      (DeleteInactiveLeaf {fibers = source} {target = target} removed component
        parent retiredFlag table outcome found noChild rest)

||| Iterated checked applicability for all retained orchestration classes. This
||| complements `checkedLifecycleAfterInactivePlan`: together they cover all
||| eight `Action` constructors that a generation filter may retain.
public export
0 checkedOrchestrationAfterInactivePlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq source target) ->
  OrchestrationOutsideDeletionPlan action plan ->
  (sourceWellFormed : registryWellFormed @{nameEq} @{keyEq} {name = name}
    {key = key} {value = value} {world = world} {error = error}
    (MkSystemState ambient source) = True) ->
  {tag : RuleTag} ->
  {afterState : SystemState name key value world error} ->
  checkedApplyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} action
    (MkSystemState ambient source) = Just (tag, afterState) ->
  TransitionResult {name = name} {key = key} {value = value} {world = world}
    {error = error} (MkSystemState ambient target)
checkedOrchestrationAfterInactivePlan {tag} {afterState} nameEq keyEq action
  orchestration ambient source source NoInactiveLeafDeletion
  OrchestrationOutsideDeletionEnd sourceWellFormed checked =
    MkTransitionResult afterState tag
      (Fired nameEq keyEq action tag checked)
checkedOrchestrationAfterInactivePlan {name} {key} {world} {error} {value}
  nameEq keyEq action orchestration ambient source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (OrchestrationOutsideDeletionStep rest ownerOutside parentOutside outsideRest)
  sourceWellFormed checked =
    let 0 raw = checkedActionProjects nameEq keyEq action
          (MkSystemState ambient source) _ _ checked
        replayRaw = orchestrationApplicableAfterInactiveDelete nameEq keyEq action
          orchestration removed ownerOutside parentOutside ambient source raw
        0 nextWellFormed = registryWellFormedInactiveDelete nameEq keyEq ambient
          removed component parent retiredFlag table outcome source found noChild
          sourceWellFormed
    in case replayRaw of
      MkRawActionResult replayTag replayAfter replayEquation =>
        let 0 replayTargetWellFormed = preservationTheoremProof nameEq keyEq
              action
              (MkSystemState ambient (deleteBinding @{nameEq} removed source))
              replayAfter replayTag nextWellFormed replayEquation
            0 replayChecked : (checkedApplyAction @{nameEq} @{keyEq} action
              (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
              Just (replayTag, replayAfter))
            replayChecked = rewrite replayEquation in
              rewrite replayTargetWellFormed in Refl
        in checkedOrchestrationAfterInactivePlan nameEq keyEq action
          orchestration ambient (deleteBinding @{nameEq} removed source) target
          rest outsideRest nextWellFormed replayChecked
