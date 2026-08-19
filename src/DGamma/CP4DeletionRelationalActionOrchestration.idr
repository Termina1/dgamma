module DGamma.CP4DeletionRelationalActionOrchestration

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedDeletedOrchestration
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedForeignOrchestration
import Data.List.Elem
import Decidable.Equality

%default total

public export
0 effectSymmetric : EffectStateRelated keyEq left right ->
  EffectStateRelated keyEq right left
effectSymmetric (MkEffectStateRelated worldSame tablesSame) =
  MkEffectStateRelated (sym worldSame) (\actor => sym (tablesSame actor))

public export
0 effectTransitive : EffectStateRelated keyEq first middle ->
  EffectStateRelated keyEq middle last -> EffectStateRelated keyEq first last
effectTransitive (MkEffectStateRelated firstWorld firstTables)
  (MkEffectStateRelated secondWorld secondTables) =
    MkEffectStateRelated (trans firstWorld secondWorld)
      (\actor => trans (firstTables actor) (secondTables actor))

0 insertViewTag :
  ForeignInsertPlanView name key world error value nameEq keyEq actor parent
    component ambient source tag afterState -> tag = OInsertTag
insertViewTag (MkForeignInsertPlanView absent guards) = Refl

0 insertViewAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {actor : name} -> {parent : Parent name} ->
  {component : Component key value world error} -> {ambient : world} ->
  {source : Registry name key value world error} ->
  {afterState : SystemState name key value world error} ->
  (view : ForeignInsertPlanView name key world error value nameEq keyEq actor
    parent component ambient source OInsertTag afterState) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Nothing
insertViewAbsent (MkForeignInsertPlanView absent guards) = absent

0 insertViewGuards :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {actor : name} -> {parent : Parent name} ->
  {component : Component key value world error} -> {ambient : world} ->
  {source : Registry name key value world error} ->
  {afterState : SystemState name key value world error} ->
  (view : ForeignInsertPlanView name key world error value nameEq keyEq actor
    parent component ambient source OInsertTag afterState) ->
  parentPresent @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} parent source &&
    provisionsDisjointFrom @{keyEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} (componentProvisions component)
      (bindings source) = True
insertViewGuards (MkForeignInsertPlanView absent guards) = guards

0 insertRawTag :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) -> (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (OInsert actor parent component)
    (MkSystemState ambient source) = Just (tag, afterState) ->
  tag = OInsertTag
insertRawTag nameEq keyEq actor parent component ambient source tag afterState raw =
  insertViewTag (foreignInsertPlanView nameEq keyEq actor parent component
    ambient source tag afterState raw)

0 retireViewTag :
  RetireSuccessView name key world error value nameEq actor ambient source tag
    afterState -> tag = ORetireTag
retireViewTag (MkRetireSuccessView fiber found) = Refl

0 removeViewTag :
  RemoveSuccessView name key world error value nameEq actor ambient source tag
    afterState -> tag = ORemoveTag
removeViewTag (MkRemoveSuccessView fiber found guard noChild) = Refl

retireRelatedAfter :
  (nameEq : DecEq name) -> (actor : name) -> (ambient : world) ->
  Fiber name key value world error -> Registry name key value world error ->
  SystemState name key value world error
retireRelatedAfter nameEq actor ambient fiber source =
  MkSystemState ambient (replaceBinding @{nameEq} actor (retireFiber fiber) source)

removeRelatedAfter :
  (nameEq : DecEq name) -> (actor : name) -> (ambient : world) ->
  Registry name key value world error -> SystemState name key value world error
removeRelatedAfter nameEq actor ambient source =
  MkSystemState ambient (deleteBinding @{nameEq} actor source)

public export
0 packageRelatedReplay :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value action leftBefore) ->
  (rightAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action rightBefore =
    Just (namedTag leftNamed, rightAfter) ->
  registryWellFormed @{nameEq} @{keyEq} rightBefore = True ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq} (namedAfter leftNamed))
    (projectEffectState @{nameEq} rightAfter) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry (namedAfter leftNamed)))
    (bindings (registry rightAfter)) ->
  RelatedNamedActionReplay name key world error value nameEq keyEq action
    leftBefore rightBefore leftNamed
packageRelatedReplay nameEq keyEq action leftBefore rightBefore leftNamed
  rightAfter rightRaw rightWellFormed effects controls =
    let 0 rightAfterWellFormed = preservationTheoremProof nameEq keyEq action
          rightBefore rightAfter (namedTag leftNamed) rightWellFormed rightRaw
        0 rightChecked : (checkedApplyAction @{nameEq} @{keyEq} action
          rightBefore = Just (namedTag leftNamed, rightAfter))
        rightChecked = rewrite rightRaw in rewrite rightAfterWellFormed in Refl
        rightTransition : Transition rightBefore rightAfter
        rightTransition = Fired nameEq keyEq action (namedTag leftNamed)
          rightChecked
        rightNamed : NamedTransition name key world error value action rightBefore
        rightNamed = MkNamedTransition rightAfter (namedTag leftNamed)
          rightTransition Refl
        0 rightFires : fireNamed nameEq keyEq action rightBefore = Just rightNamed
        rightFires = rewrite rightChecked in Refl
    in MkRelatedNamedActionReplay rightNamed rightFires effects controls
      rightAfterWellFormed

0 frameDefined :
  PartialRelated state observedRelation (Just left) (Just right) ->
  observedRelation left right
frameDefined (PartialDefined related) = related

0 setEmptyEffectsRelated :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (left, right : SystemState name key value world error) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq} left))
    (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq} right))
setEmptyEffectsRelated nameEq keyEq actor left right effects =
  setRelatedEffectTables nameEq keyEq actor
    (emptyContext {key = key} {value = value})
    (emptyContext {key = key} {value = value}) Refl effects

0 stateRuntimeEta :
  (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
stateRuntimeEta (MkSystemState ambient fibers) = Refl

0 insertActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (OInsert actor parent component) before =
    Just (OInsertTag, afterState) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq} before))
    (projectEffectState @{nameEq} afterState)
insertActualEffectFrame nameEq keyEq actor parent component before afterState
  checked = case actualTransitionEffectFrame nameEq keyEq
    (OInsert actor parent component) OInsertTag before afterState checked of
    MkActualEffectFrame frame => frameDefined frame

0 retireActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) before =
    Just (ORetireTag, afterState) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} before)
    (projectEffectState @{nameEq} afterState)
retireActualEffectFrame nameEq keyEq actor before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq (ORetire actor) ORetireTag before
    afterState checked of MkActualEffectFrame frame => frameDefined frame

0 removeActualEffectFrame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  checkedApplyAction @{nameEq} @{keyEq} (ORemove actor) before =
    Just (ORemoveTag, afterState) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} actor (emptyContext {key = key} {value = value})
      (projectEffectState @{nameEq} before))
    (projectEffectState @{nameEq} afterState)
removeActualEffectFrame nameEq keyEq actor before afterState checked =
  case actualTransitionEffectFrame nameEq keyEq (ORemove actor) ORemoveTag before
    afterState checked of MkActualEffectFrame frame => frameDefined frame

||| Exact ordered/effect congruence for the three orchestration actions.
public export
0 replayRelatedOrchestrationAction :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value action leftBefore) ->
  (leftRaw : applyAction @{nameEq} @{keyEq} action leftBefore =
    Just (namedTag leftNamed, namedAfter leftNamed)) ->
  (leftWellFormed : registryWellFormed @{nameEq} @{keyEq} leftBefore = True) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry leftBefore)) (bindings (registry rightBefore)) ->
  registryWellFormed @{nameEq} @{keyEq} rightBefore = True ->
  RelatedNamedActionReplay name key world error value nameEq keyEq action
    leftBefore rightBefore leftNamed
replayRelatedOrchestrationAction nameEq keyEq
  (OInsert actor parent component) orchestration
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry) leftNamed leftRaw leftWellFormed
  effects ordered rightWellFormed =
    let 0 leftAfterWellFormed = preservationTheoremProof nameEq keyEq
          (OInsert actor parent component)
          (MkSystemState leftWorld leftRegistry) (namedAfter leftNamed)
          (namedTag leftNamed) leftWellFormed leftRaw
        0 leftChecked : (checkedApplyAction @{nameEq} @{keyEq}
          (OInsert actor parent component)
          (MkSystemState leftWorld leftRegistry) =
          Just (namedTag leftNamed, namedAfter leftNamed))
        leftChecked = rewrite leftRaw in rewrite leftAfterWellFormed in Refl
        0 leftTag : (namedTag leftNamed = OInsertTag)
        leftTag = insertRawTag nameEq keyEq actor parent component leftWorld
          leftRegistry (namedTag leftNamed) (namedAfter leftNamed) leftRaw
        leftView : ForeignInsertPlanView name key world error value nameEq keyEq
          actor parent component leftWorld leftRegistry OInsertTag
          (namedAfter leftNamed)
        leftView = replace
          {p = \observedTag => ForeignInsertPlanView name key world error value
            nameEq keyEq actor parent component leftWorld leftRegistry
            observedTag (namedAfter leftNamed)}
          leftTag (foreignInsertPlanView nameEq keyEq actor parent component
            leftWorld leftRegistry (namedTag leftNamed) (namedAfter leftNamed)
            leftRaw)
     in let 0 rightAbsent : (lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} actor
              rightRegistry = Nothing)
            rightAbsent = orderedControlsNothingOnRight nameEq actor leftRegistry
              rightRegistry ordered (insertViewAbsent leftView)
            0 parentSame : (parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              leftRegistry = parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              rightRegistry)
            parentSame = orderedControlsParentPresentSame nameEq actor parent
              leftRegistry rightRegistry ordered
            0 provisionsSame : (provisionsDisjointFrom @{keyEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              (componentProvisions component) (bindings leftRegistry) =
              provisionsDisjointFrom @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error}
                (componentProvisions component) (bindings rightRegistry))
            provisionsSame = orderedControlsProvisionsDisjointSame nameEq keyEq
              actor (componentProvisions component) (bindings leftRegistry)
              (bindings rightRegistry) ordered
            0 guardsSame : (parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent leftRegistry &&
              provisionsDisjointFrom @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error}
                (componentProvisions component) (bindings leftRegistry) =
              parentPresent @{nameEq} {name = name} {key = key} {value = value}
                {world = world} {error = error} parent rightRegistry &&
              provisionsDisjointFrom @{keyEq} {name = name} {key = key}
                {value = value} {world = world} {error = error}
                (componentProvisions component) (bindings rightRegistry))
            guardsSame = boolAndCong parentSame provisionsSame
            0 rightGuards : (parentPresent @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} parent
              rightRegistry && provisionsDisjointFrom @{keyEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              (componentProvisions component) (bindings rightRegistry) = True)
            rightGuards = trans (sym guardsSame) (insertViewGuards leftView)
        in case setFreshFromAbsent nameEq actor (freshFiber component parent)
          rightRegistry rightAbsent of
          (applied ** inserted) =>
            let rightAfter : SystemState name key value world error
                rightAfter = MkSystemState rightWorld (coeffectAfter applied)
                0 rightRaw : applyAction @{nameEq} @{keyEq}
                  (OInsert actor parent component)
                  (MkSystemState rightWorld rightRegistry) =
                  Just (OInsertTag, rightAfter)
                rightRaw = rewrite rightGuards in rewrite inserted in Refl
                0 canonicalControls : OrderedRegistryControlsRelated name key
                  world error value
                  (Bind actor (freshFiber component parent) ::
                    bindings leftRegistry)
                  (Bind actor (freshFiber component parent) ::
                    bindings rightRegistry)
                canonicalControls = orderedControlsInsert actor
                  (fiberControlReflexive (freshFiber component parent)) ordered
                0 leftObservation : InsertRuntimeObservation name key world
                  error value actor component parent leftWorld leftRegistry
                  (namedTag leftNamed) (namedAfter leftNamed)
                leftObservation = insertRuntimeObservation nameEq keyEq actor
                  parent component leftWorld leftRegistry (namedTag leftNamed)
                  (namedAfter leftNamed) leftRaw
                0 rightBindings : bindings (coeffectAfter applied) =
                  Bind actor (freshFiber component parent) :: bindings rightRegistry
                rightBindings = trans
                  (cong bindings (setFreshAfter nameEq actor
                    (freshFiber component parent) rightRegistry applied inserted))
                  (insertBindingRuntimeBindings nameEq actor
                    (freshFiber component parent) rightRegistry
                    (setFreshAbsent nameEq actor (freshFiber component parent)
                      rightRegistry applied inserted))
                0 nextControls : OrderedRegistryControlsRelated name key world
                  error value (bindings (registry (namedAfter leftNamed)))
                  (bindings (registry rightAfter))
                nextControls = orderedControlsTransport
                  (sym (insertObservedBindings leftObservation))
                  (sym rightBindings) canonicalControls
                0 setRelated : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState leftWorld leftRegistry))))
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState rightWorld rightRegistry))))
                setRelated = setEmptyEffectsRelated nameEq keyEq actor
                  (MkSystemState leftWorld leftRegistry)
                  (MkSystemState rightWorld rightRegistry) effects
                0 taggedLeftChecked : (checkedApplyAction @{nameEq} @{keyEq}
                  (OInsert actor parent component)
                  (MkSystemState leftWorld leftRegistry) =
                  Just (OInsertTag, namedAfter leftNamed))
                taggedLeftChecked = replace
                  {p = \observedTag => checkedApplyAction @{nameEq} @{keyEq}
                    (OInsert actor parent component)
                    (MkSystemState leftWorld leftRegistry) =
                    Just (observedTag, namedAfter leftNamed)}
                  leftTag leftChecked
                0 leftFrame : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState leftWorld leftRegistry))))
                  (projectEffectState @{nameEq} (namedAfter leftNamed))
                leftFrame = insertActualEffectFrame nameEq keyEq actor parent
                  component (MkSystemState leftWorld leftRegistry)
                  (namedAfter leftNamed) taggedLeftChecked
                0 rightAfterValid : registryWellFormed @{nameEq} @{keyEq}
                  rightAfter = True
                rightAfterValid = preservationTheoremProof nameEq keyEq
                  (OInsert actor parent component)
                  (MkSystemState rightWorld rightRegistry) rightAfter OInsertTag
                  rightWellFormed rightRaw
                0 rightCheckedRaw : (checkedApplyAction @{nameEq} @{keyEq}
                  (OInsert actor parent component)
                  (MkSystemState rightWorld rightRegistry) =
                  Just (OInsertTag, rightAfter))
                rightCheckedRaw = rewrite rightRaw in
                  rewrite rightAfterValid in Refl
                0 rightFrame : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState rightWorld rightRegistry))))
                  (projectEffectState @{nameEq} rightAfter)
                rightFrame = insertActualEffectFrame nameEq keyEq actor parent
                  component (MkSystemState rightWorld rightRegistry) rightAfter
                  rightCheckedRaw
                0 nextEffects : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} (namedAfter leftNamed))
                  (projectEffectState @{nameEq} rightAfter)
                nextEffects = effectTransitive (effectSymmetric leftFrame)
                  (effectTransitive setRelated rightFrame)
                0 packageRightRaw : applyAction @{nameEq} @{keyEq}
                  (OInsert actor parent component)
                  (MkSystemState rightWorld rightRegistry) =
                  Just (namedTag leftNamed, rightAfter)
                packageRightRaw = replace
                  {p = \observedTag => applyAction @{nameEq} @{keyEq}
                    (OInsert actor parent component)
                    (MkSystemState rightWorld rightRegistry) =
                    Just (observedTag, rightAfter)}
                  (sym leftTag) rightRaw
            in packageRelatedReplay nameEq keyEq (OInsert actor parent component)
              (MkSystemState leftWorld leftRegistry)
              (MkSystemState rightWorld rightRegistry) leftNamed rightAfter
              packageRightRaw rightWellFormed nextEffects nextControls
replayRelatedOrchestrationAction nameEq keyEq (ORetire actor) orchestration
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry) leftNamed leftRaw leftWellFormed
  effects ordered rightWellFormed =
    let 0 leftAfterWellFormed = preservationTheoremProof nameEq keyEq
          (ORetire actor) (MkSystemState leftWorld leftRegistry)
          (namedAfter leftNamed) (namedTag leftNamed) leftWellFormed leftRaw
        0 leftChecked : (checkedApplyAction @{nameEq} @{keyEq} (ORetire actor)
          (MkSystemState leftWorld leftRegistry) = Just (namedTag leftNamed, namedAfter leftNamed))
        leftChecked = rewrite leftRaw in rewrite leftAfterWellFormed in Refl
        0 leftTag : (namedTag leftNamed = ORetireTag)
        leftTag = retireViewTag (retireSuccessView nameEq keyEq actor leftWorld
          leftRegistry (namedTag leftNamed) (namedAfter leftNamed) leftRaw)
    in case retireSourceView nameEq keyEq actor leftWorld leftRegistry
      (namedTag leftNamed) (namedAfter leftNamed) leftRaw of
      MkRetireSourceView leftFiber leftFound =>
        case foreignControlLookupFound nameEq actor leftRegistry rightRegistry
          leftFiber leftFound
          (orderedControlsLookup nameEq actor leftRegistry rightRegistry ordered) of
          MkForeignRelatedFiberFound rightFiber rightFound controls =>
            let 0 rightRaw : (applyAction @{nameEq} @{keyEq} (ORetire actor)
                  (MkSystemState rightWorld rightRegistry) =
                  Just (ORetireTag, retireRelatedAfter nameEq actor rightWorld
                    rightFiber rightRegistry))
                rightRaw = rewrite rightFound in Refl
                0 replaced : OrderedRegistryControlsRelated name key world
                  error value
                  (replaceEntries @{nameEq} actor (retireFiber leftFiber)
                    (bindings leftRegistry))
                  (replaceEntries @{nameEq} actor (retireFiber rightFiber)
                    (bindings rightRegistry))
                replaced = orderedControlsReplace nameEq actor
                  (retireFiber leftFiber) (retireFiber rightFiber)
                  (retireFiberControlRelated controls) (bindings leftRegistry)
                  (bindings rightRegistry) ordered
                0 leftObservation : OrchestrationRuntimeObservation name key
                  world error value leftWorld
                  (replaceBinding @{nameEq} actor (retireFiber leftFiber)
                    leftRegistry) (namedAfter leftNamed)
                leftObservation = retireRuntimeObservation nameEq keyEq actor
                  leftWorld leftRegistry leftFiber leftFound (namedTag leftNamed)
                  (namedAfter leftNamed) leftRaw
                0 leftControlBindings : replaceEntries @{nameEq} actor
                  (retireFiber leftFiber) (bindings leftRegistry) =
                  bindings (registry (namedAfter leftNamed))
                leftControlBindings = trans
                  (sym (replaceBindingRuntimeBindings nameEq actor
                    (retireFiber leftFiber) leftRegistry))
                  (sym (orchestrationObservedBindings leftObservation))
                0 rightControlBindings : replaceEntries @{nameEq} actor
                  (retireFiber rightFiber) (bindings rightRegistry) =
                  bindings (registry (retireRelatedAfter nameEq actor rightWorld
                    rightFiber rightRegistry))
                rightControlBindings = sym (replaceBindingRuntimeBindings nameEq
                  actor (retireFiber rightFiber) rightRegistry)
                0 nextControls : OrderedRegistryControlsRelated name key world
                  error value (bindings (registry (namedAfter leftNamed)))
                  (bindings (registry (retireRelatedAfter nameEq actor rightWorld
                    rightFiber rightRegistry)))
                nextControls = orderedControlsTransport leftControlBindings
                  rightControlBindings replaced
                0 leftFrame : EffectStateRelated keyEq
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState leftWorld leftRegistry)))
                  (projectEffectState @{nameEq} (namedAfter leftNamed))
                leftFrame = retireActualEffectFrame nameEq keyEq actor
                  (MkSystemState leftWorld leftRegistry) (namedAfter leftNamed)
                  (replace {p = \observedTag => checkedApplyAction @{nameEq}
                    @{keyEq} (ORetire actor)
                    (MkSystemState leftWorld leftRegistry) =
                    Just (observedTag, namedAfter leftNamed)} leftTag leftChecked)
                0 rightCheckedRaw : (checkedApplyAction @{nameEq} @{keyEq}
                  (ORetire actor) (MkSystemState rightWorld rightRegistry) =
                  Just (ORetireTag, retireRelatedAfter nameEq actor rightWorld
                    rightFiber rightRegistry))
                rightCheckedRaw =
                  let 0 wf = preservationTheoremProof nameEq keyEq
                        (ORetire actor) (MkSystemState rightWorld rightRegistry)
                        (retireRelatedAfter nameEq actor rightWorld rightFiber
                          rightRegistry) ORetireTag rightWellFormed rightRaw
                  in rewrite rightRaw in rewrite wf in Refl
                0 rightFrame : EffectStateRelated keyEq
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState rightWorld rightRegistry)))
                  (projectEffectState @{nameEq}
                    (retireRelatedAfter nameEq actor rightWorld rightFiber
                      rightRegistry))
                rightFrame = retireActualEffectFrame nameEq keyEq actor
                  (MkSystemState rightWorld rightRegistry)
                  (retireRelatedAfter nameEq actor rightWorld rightFiber
                    rightRegistry) rightCheckedRaw
                0 nextEffects : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} (namedAfter leftNamed))
                  (projectEffectState @{nameEq}
                    (retireRelatedAfter nameEq actor rightWorld rightFiber
                      rightRegistry))
                nextEffects = effectTransitive (effectSymmetric leftFrame)
                  (effectTransitive effects rightFrame)
                0 packageRightRaw : (applyAction @{nameEq} @{keyEq}
                  (ORetire actor) (MkSystemState rightWorld rightRegistry) =
                  Just (namedTag leftNamed, retireRelatedAfter nameEq actor
                    rightWorld rightFiber rightRegistry))
                packageRightRaw = replace
                  {p = \observedTag => applyAction @{nameEq} @{keyEq}
                    (ORetire actor) (MkSystemState rightWorld rightRegistry) =
                    Just (observedTag, retireRelatedAfter nameEq actor rightWorld
                      rightFiber rightRegistry)} (sym leftTag) rightRaw
            in packageRelatedReplay nameEq keyEq (ORetire actor)
              (MkSystemState leftWorld leftRegistry)
              (MkSystemState rightWorld rightRegistry) leftNamed
              (retireRelatedAfter nameEq actor rightWorld rightFiber rightRegistry)
              packageRightRaw rightWellFormed nextEffects nextControls
replayRelatedOrchestrationAction nameEq keyEq (ORemove actor) orchestration
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry) leftNamed leftRaw leftWellFormed
  effects ordered rightWellFormed =
    let 0 leftAfterWellFormed = preservationTheoremProof nameEq keyEq
          (ORemove actor) (MkSystemState leftWorld leftRegistry)
          (namedAfter leftNamed) (namedTag leftNamed) leftWellFormed leftRaw
        0 leftChecked : (checkedApplyAction @{nameEq} @{keyEq} (ORemove actor)
          (MkSystemState leftWorld leftRegistry) = Just (namedTag leftNamed, namedAfter leftNamed))
        leftChecked = rewrite leftRaw in rewrite leftAfterWellFormed in Refl
        0 leftTag : (namedTag leftNamed = ORemoveTag)
        leftTag = removeViewTag (removeSuccessView nameEq keyEq actor leftWorld
          leftRegistry (namedTag leftNamed) (namedAfter leftNamed) leftRaw)
    in case removeSourceView nameEq keyEq actor leftWorld leftRegistry
      (namedTag leftNamed) (namedAfter leftNamed) leftRaw of
      MkRemoveSourceView leftFiber leftFound leftGuard leftNoChild =>
        case foreignControlLookupFound nameEq actor leftRegistry rightRegistry
          leftFiber leftFound
          (orderedControlsLookup nameEq actor leftRegistry rightRegistry ordered) of
          MkForeignRelatedFiberFound rightFiber rightFound controls =>
            let 0 retiredSame = fiberControlRetiredSame controls
                0 inactiveSame = fiberControlIsInactiveSame controls
                0 childSame = orderedControlsHasChildSame nameEq actor actor
                  leftRegistry rightRegistry ordered
                0 rightNoChild = trans (sym childSame) leftNoChild
                0 normalizedLeftGuard = replace
                  {p = \children => retired leftFiber &&
                    isInactive (fiberLifecycle leftFiber) && not children = True}
                  leftNoChild leftGuard
                0 rightGuard : (retired rightFiber &&
                  isInactive (fiberLifecycle rightFiber) &&
                  not (hasChild @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    rightRegistry) = True)
                rightGuard = rewrite rightNoChild in rewrite sym retiredSame in
                  rewrite sym inactiveSame in normalizedLeftGuard
                0 rightRaw : (applyAction @{nameEq} @{keyEq} (ORemove actor)
                  (MkSystemState rightWorld rightRegistry) =
                  Just (ORemoveTag,
                    the (SystemState name key value world error)
                      (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry)))
                rightRaw = rewrite rightFound in rewrite rightGuard in Refl
                0 deleted : OrderedRegistryControlsRelated name key world
                  error value (deleteEntries @{nameEq} actor
                    (bindings leftRegistry))
                  (deleteEntries @{nameEq} actor (bindings rightRegistry))
                deleted = orderedControlsDelete nameEq actor
                  (bindings leftRegistry) (bindings rightRegistry) ordered
                0 leftObservation : OrchestrationRuntimeObservation name key
                  world error value leftWorld
                  (deleteBinding @{nameEq} actor leftRegistry)
                  (namedAfter leftNamed)
                leftObservation = removeRuntimeObservation nameEq keyEq actor
                  leftWorld leftRegistry leftFiber leftFound leftGuard
                  (namedTag leftNamed) (namedAfter leftNamed) leftRaw
                0 leftControlBindings : deleteEntries @{nameEq} actor
                  (bindings leftRegistry) =
                  bindings (registry (namedAfter leftNamed))
                leftControlBindings = trans
                  (sym (deleteBindingRuntimeBindings nameEq actor leftRegistry))
                  (sym (orchestrationObservedBindings leftObservation))
                0 rightControlBindings : deleteEntries @{nameEq} actor
                  (bindings rightRegistry) = bindings
                    (registry (the (SystemState name key value world error)
                      (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry)))
                rightControlBindings = sym (deleteBindingRuntimeBindings nameEq
                  actor rightRegistry)
                0 nextControls : OrderedRegistryControlsRelated name key world
                  error value (bindings (registry (namedAfter leftNamed)))
                  (bindings (registry
                    (the (SystemState name key value world error)
                      (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry))))
                nextControls = orderedControlsTransport leftControlBindings
                  rightControlBindings deleted
                0 setRelated : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState leftWorld leftRegistry))))
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState rightWorld rightRegistry))))
                setRelated = setEmptyEffectsRelated nameEq keyEq actor
                  (MkSystemState leftWorld leftRegistry)
                  (MkSystemState rightWorld rightRegistry) effects
                0 taggedLeftChecked : (checkedApplyAction @{nameEq} @{keyEq}
                  (ORemove actor) (MkSystemState leftWorld leftRegistry) =
                  Just (ORemoveTag, namedAfter leftNamed))
                taggedLeftChecked = replace
                  {p = \observedTag => checkedApplyAction @{nameEq} @{keyEq}
                    (ORemove actor) (MkSystemState leftWorld leftRegistry) =
                    Just (observedTag, namedAfter leftNamed)} leftTag leftChecked
                0 leftFrame : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState leftWorld leftRegistry))))
                  (projectEffectState @{nameEq} (namedAfter leftNamed))
                leftFrame = removeActualEffectFrame nameEq keyEq actor
                  (MkSystemState leftWorld leftRegistry) (namedAfter leftNamed)
                  taggedLeftChecked
                0 rightAfterValid : registryWellFormed @{nameEq} @{keyEq}
                  (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry) = True
                rightAfterValid = preservationTheoremProof nameEq keyEq
                  (ORemove actor) (MkSystemState rightWorld rightRegistry)
                  (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry)
                  ORemoveTag rightWellFormed rightRaw
                0 rightCheckedRaw : (checkedApplyAction @{nameEq} @{keyEq}
                  (ORemove actor) (MkSystemState rightWorld rightRegistry) =
                  Just (ORemoveTag,
                    removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry))
                rightCheckedRaw = rewrite rightRaw in
                  rewrite rightAfterValid in Refl
                0 rightFrame : EffectStateRelated keyEq
                  (setEffectTable @{nameEq} actor
                    (emptyContext {key = key} {value = value})
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState rightWorld rightRegistry))))
                  (projectEffectState @{nameEq}
                    (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry))
                rightFrame = removeActualEffectFrame nameEq keyEq actor
                  (MkSystemState rightWorld rightRegistry)
                  (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry)
                  rightCheckedRaw
                0 nextEffects : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} (namedAfter leftNamed))
                  (projectEffectState @{nameEq}
                    (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry))
                nextEffects = effectTransitive (effectSymmetric leftFrame)
                  (effectTransitive setRelated rightFrame)
                0 packageRightRaw : (applyAction @{nameEq} @{keyEq}
                  (ORemove actor) (MkSystemState rightWorld rightRegistry) =
                  Just (namedTag leftNamed,
                    removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry))
                packageRightRaw = replace
                  {p = \observedTag => applyAction @{nameEq} @{keyEq}
                    (ORemove actor) (MkSystemState rightWorld rightRegistry) =
                    Just (observedTag,
                      removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry)}
                  (sym leftTag) rightRaw
            in packageRelatedReplay nameEq keyEq (ORemove actor)
              (MkSystemState leftWorld leftRegistry)
              (MkSystemState rightWorld rightRegistry) leftNamed
              (removeRelatedAfter {name = name} {key = key} {value = value} {world = world} {error = error} nameEq actor rightWorld rightRegistry)
              packageRightRaw rightWellFormed nextEffects nextControls
replayRelatedOrchestrationAction nameEq keyEq (LBegin actor) Refl left right named
  raw leftWf effects ordered rightWf impossible
replayRelatedOrchestrationAction nameEq keyEq (LAdvance actor) Refl left right named
  raw leftWf effects ordered rightWf impossible
replayRelatedOrchestrationAction nameEq keyEq (LDivert actor) Refl left right named
  raw leftWf effects ordered rightWf impossible
replayRelatedOrchestrationAction nameEq keyEq (LLeave actor) Refl left right named
  raw leftWf effects ordered rightWf impossible
replayRelatedOrchestrationAction nameEq keyEq (LUnload actor) Refl left right named
  raw leftWf effects ordered rightWf impossible
