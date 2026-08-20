module DGamma.CP4DeletionSelectedForeignOrchestration

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4DeletionSelectedEffectForeign
import DGamma.CP4DeletionSelectedForeignControlCore
import Data.List.Elem
import Decidable.Equality

%default total

0 nothingNotJust : Nothing = Just item -> Void
nothingNotJust Refl impossible

public export
record ForeignOrchestrationControlReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (action : Action name key value world error) (tag : RuleTag)
  (planAfter, survivorBefore : SystemState name key value world error) where
  constructor MkForeignOrchestrationControlReplay
  foreignControlAfter : SystemState name key value world error
  0 foreignControlRaw : applyAction @{nameEq} @{keyEq} action survivorBefore =
    Just (tag, foreignControlAfter)
  0 foreignControlChecked : checkedApplyAction @{nameEq} @{keyEq} action
    survivorBefore = Just (tag, foreignControlAfter)
  0 foreignControlOrdered : SelectedOrderedRegistryControlsRelated name key
    world error value selected (bindings (registry planAfter))
    (bindings (registry foreignControlAfter))

public export
data ForeignInsertPlanView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkForeignInsertPlanView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {actor : name} -> {parent : Parent name} ->
    {component : Component key value world error} -> {ambient : world} ->
    {source : Registry name key value world error} ->
    (absent : lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor source = Nothing) ->
    (guards : parentPresent @{nameEq} {name = name} {key = key}
      {value = value} {world = world} {error = error} parent source &&
      provisionsDisjointFrom @{keyEq} {name = name} {key = key}
        {value = value} {world = world} {error = error}
        (componentProvisions component) (bindings source) = True) ->
    ForeignInsertPlanView name key world error value nameEq keyEq actor parent
      component ambient source OInsertTag
      (MkSystemState ambient
        (insertBinding @{nameEq} actor (freshFiber component parent) source
          absent))

public export
0 foreignInsertPlanView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (OInsert actor parent component)
    (MkSystemState ambient source) = Just (tag, afterState) ->
  ForeignInsertPlanView name key world error value nameEq keyEq actor parent
    component ambient source tag afterState
foreignInsertPlanView nameEq keyEq actor parent component ambient source tag
  afterState raw
  with (parentPresent @{nameEq} parent source &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (bindings source)) proof guards
  foreignInsertPlanView nameEq keyEq actor parent component ambient source tag
    afterState raw | False = void (nothingNotJust raw)
  foreignInsertPlanView nameEq keyEq actor parent component ambient source tag
    afterState raw | True
    with (setFresh @{nameEq} actor (freshFiber component parent) source)
      proof inserted
    foreignInsertPlanView nameEq keyEq actor parent component ambient source tag
      afterState raw | True | Nothing = void (nothingNotJust raw)
    foreignInsertPlanView nameEq keyEq actor parent component ambient source tag
      afterState raw | True | Just applied = case justInjective raw of
        Refl => rewrite setFreshAfter nameEq actor (freshFiber component parent)
          source applied inserted in
          MkForeignInsertPlanView
            (setFreshAbsent nameEq actor (freshFiber component parent) source
              applied inserted)
            guards

public export
0 boolAndCong : leftA = rightA -> leftB = rightB ->
  leftA && leftB = rightA && rightB
boolAndCong Refl Refl = Refl

public export
0 setFreshFromAbsent :
  (keyEq : DecEq key) -> (selected : key) -> (next : value selected) ->
  (before : CoeffectContext key value) ->
  lookupBinding @{keyEq} selected before = Nothing ->
  (applied : CoeffectApplied before **
    setFresh @{keyEq} selected next before = Just applied)
setFreshFromAbsent keyEq selected next before absent
  with (lookupBinding @{keyEq} selected before)
  setFreshFromAbsent keyEq selected next before Refl | Just old impossible
  setFreshFromAbsent keyEq selected next before absent | Nothing = (_ ** Refl)

||| Rebuild retained foreign O-Insert on the recovered survivor.  The ordered
||| skeleton supplies exact freshness/domain, parent presence, and declaration
||| disjointness; no effect equality is used for this control-only rule.
public export
0 replayForeignInsertControls :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected, actor : name) ->
  Not (actor = selected) ->
  (parent : Parent name) ->
  (component : Component key value world error) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (OInsert actor parent component)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignOrchestrationControlReplay name key world error value nameEq keyEq
    selected (OInsert actor parent component) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayForeignInsertControls nameEq keyEq selected actor actorDistinct parent
  component planAmbient survivorAmbient plan survivor ordered tag planAfter planRaw survivorWellFormed
  = case foreignInsertPlanView nameEq keyEq actor parent component planAmbient plan
      tag planAfter planRaw of
      MkForeignInsertPlanView planAbsent planGuards =>
        let 0 survivorAbsent = selectedOrderedNothingOnRight nameEq actor plan
              survivor ordered planAbsent
            0 parentSame = selectedOrderedParentPresentSame nameEq parent plan
              survivor ordered
            0 provisionsSame = selectedOrderedProvisionsDisjointSame keyEq
              (componentProvisions component) (bindings plan)
              (bindings survivor) ordered
            0 guardsSame = boolAndCong parentSame provisionsSame
            0 survivorGuards :
              (parentPresent @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} parent
                  survivor &&
                provisionsDisjointFrom @{keyEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error}
                  (componentProvisions component) (bindings survivor) = True)
            survivorGuards = trans (sym guardsSame) planGuards
        in case setFreshFromAbsent nameEq actor (freshFiber component parent)
          survivor survivorAbsent of
          (applied ** inserted) =>
            let survivorAfter : SystemState name key value world error
                survivorAfter = MkSystemState survivorAmbient (coeffectAfter applied)
                0 survivorRaw : (applyAction @{nameEq} @{keyEq}
                      (OInsert actor parent component)
                      (MkSystemState survivorAmbient survivor) =
                    Just (OInsertTag, survivorAfter))
                survivorRaw = rewrite survivorGuards in rewrite inserted in Refl
                0 survivorAfterWellFormed :
                  (registryWellFormed @{nameEq} @{keyEq} survivorAfter = True)
                survivorAfterWellFormed = preservationTheoremProof nameEq keyEq
                  (OInsert actor parent component)
                  (MkSystemState survivorAmbient survivor) survivorAfter OInsertTag
                  survivorWellFormed survivorRaw
                0 survivorChecked : (checkedApplyAction @{nameEq} @{keyEq}
                      (OInsert actor parent component)
                      (MkSystemState survivorAmbient survivor) =
                    Just (OInsertTag, survivorAfter))
                survivorChecked = rewrite survivorRaw in
                  rewrite survivorAfterWellFormed in Refl
                0 canonicalOrdered : SelectedOrderedRegistryControlsRelated name
                  key world error value selected
                  (Bind actor (freshFiber component parent) :: bindings plan)
                  (Bind actor (freshFiber component parent) :: bindings survivor)
                canonicalOrdered = selectedOrderedInsertForeign selected actor
                  actorDistinct
                  (fiberControlReflexive (freshFiber component parent)) ordered
                0 planBindings : bindings
                      (insertBinding @{nameEq} actor
                        (freshFiber component parent) plan planAbsent) =
                    Bind actor (freshFiber component parent) :: bindings plan
                planBindings = insertBindingRuntimeBindings nameEq actor
                  (freshFiber component parent) plan planAbsent
                0 survivorBindings : bindings (coeffectAfter applied) =
                    Bind actor (freshFiber component parent) :: bindings survivor
                survivorBindings = trans
                  (cong bindings (setFreshAfter nameEq actor
                    (freshFiber component parent) survivor applied inserted))
                  (insertBindingRuntimeBindings nameEq actor
                    (freshFiber component parent) survivor
                    (setFreshAbsent nameEq actor (freshFiber component parent)
                      survivor applied inserted))
                0 nextOrdered : SelectedOrderedRegistryControlsRelated name key
                  world error value selected
                  (bindings (insertBinding @{nameEq} actor
                    (freshFiber component parent) plan planAbsent))
                  (bindings (coeffectAfter applied))
                nextOrdered = selectedOrderedTransport (sym planBindings)
                  (sym survivorBindings) canonicalOrdered
            in MkForeignOrchestrationControlReplay survivorAfter survivorRaw
              survivorChecked nextOrdered

||| Rebuild retained foreign O-Retire and preserve the ordered skeleton by
||| applying the same retirement edit to the related foreign cell.
public export
0 replayForeignRetireControls :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected, actor : name) ->
  Not (actor = selected) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignOrchestrationControlReplay name key world error value nameEq keyEq
    selected (ORetire actor) tag planAfter (MkSystemState survivorAmbient survivor)
replayForeignRetireControls nameEq keyEq selected actor actorDistinct planAmbient survivorAmbient plan
  survivor ordered tag planAfter planRaw survivorWellFormed =
    case retireSuccessView nameEq keyEq actor planAmbient plan tag planAfter planRaw of
      MkRetireSuccessView planFiber planFound =>
        case foreignControlLookupFound nameEq actor plan survivor planFiber
          planFound (selectedOrderedForeignLookupControls nameEq selected actor
            actorDistinct plan survivor ordered) of
          MkForeignRelatedFiberFound survivorFiber survivorFound fibers =>
            let survivorAfter : SystemState name key value world error
                survivorAfter = MkSystemState survivorAmbient
                  (replaceBinding @{nameEq} actor (retireFiber survivorFiber)
                    survivor)
                0 survivorRaw : (applyAction @{nameEq} @{keyEq} (ORetire actor)
                      (MkSystemState survivorAmbient survivor) =
                    Just (ORetireTag, survivorAfter))
                survivorRaw = rewrite survivorFound in Refl
                0 survivorAfterWellFormed :
                  (registryWellFormed @{nameEq} @{keyEq} survivorAfter = True)
                survivorAfterWellFormed = preservationTheoremProof nameEq keyEq
                  (ORetire actor) (MkSystemState survivorAmbient survivor) survivorAfter
                  ORetireTag survivorWellFormed survivorRaw
                0 survivorChecked : (checkedApplyAction @{nameEq} @{keyEq}
                      (ORetire actor) (MkSystemState survivorAmbient survivor) =
                    Just (ORetireTag, survivorAfter))
                survivorChecked = rewrite survivorRaw in
                  rewrite survivorAfterWellFormed in Refl
                0 nextOrdered : SelectedOrderedRegistryControlsRelated name key
                  world error value selected
                  (replaceEntries @{nameEq} actor (retireFiber planFiber)
                    (bindings plan))
                  (replaceEntries @{nameEq} actor (retireFiber survivorFiber)
                    (bindings survivor))
                nextOrdered = selectedOrderedReplaceForeign nameEq selected
                  actor actorDistinct (retireFiber planFiber)
                  (retireFiber survivorFiber) (retireFiberControlRelated fibers)
                  (bindings plan) (bindings survivor) ordered
                0 planBindings : (bindings
                      (replaceBinding @{nameEq} actor (retireFiber planFiber)
                        plan) =
                    replaceEntries @{nameEq} actor (retireFiber planFiber)
                      (bindings plan))
                planBindings = replaceBindingRuntimeBindings nameEq actor
                  (retireFiber planFiber) plan
                0 survivorBindings : (bindings
                      (replaceBinding @{nameEq} actor (retireFiber survivorFiber)
                        survivor) =
                    replaceEntries @{nameEq} actor (retireFiber survivorFiber)
                      (bindings survivor))
                survivorBindings = replaceBindingRuntimeBindings nameEq actor
                  (retireFiber survivorFiber) survivor
                0 finalOrdered : SelectedOrderedRegistryControlsRelated name key
                  world error value selected
                  (bindings (replaceBinding @{nameEq} actor
                    (retireFiber planFiber) plan))
                  (bindings (replaceBinding @{nameEq} actor
                    (retireFiber survivorFiber) survivor))
                finalOrdered = selectedOrderedTransport (sym planBindings)
                  (sym survivorBindings) nextOrdered
            in MkForeignOrchestrationControlReplay survivorAfter survivorRaw
              survivorChecked finalOrdered

||| Rebuild retained foreign O-Remove.  Full foreign control relation preserves
||| retired/Inactive guards, while ordered parent equality preserves no-child.
public export
0 replayForeignRemoveControls :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected, actor : name) ->
  Not (actor = selected) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORemove actor)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignOrchestrationControlReplay name key world error value nameEq keyEq
    selected (ORemove actor) tag planAfter (MkSystemState survivorAmbient survivor)
replayForeignRemoveControls nameEq keyEq selected actor actorDistinct planAmbient survivorAmbient plan
  survivor ordered tag planAfter planRaw survivorWellFormed =
    case removeSuccessView nameEq keyEq actor planAmbient plan tag planAfter planRaw of
      MkRemoveSuccessView planFiber planFound planGuard planNoChild =>
        case foreignControlLookupFound nameEq actor plan survivor planFiber
          planFound (selectedOrderedForeignLookupControls nameEq selected actor
            actorDistinct plan survivor ordered) of
          MkForeignRelatedFiberFound survivorFiber survivorFound fibers =>
            let 0 retiredSame = fiberControlRetiredSame fibers
                0 inactiveSame = fiberControlIsInactiveSame fibers
                0 childSame = selectedOrderedHasChildSame nameEq actor plan
                  survivor ordered
                0 survivorNoChild :
                  (hasChild @{nameEq} {name = name} {key = key}
                    {value = value} {world = world} {error = error} actor
                    survivor = False)
                survivorNoChild = trans (sym childSame) planNoChild
                0 normalizedPlanGuard : (retired planFiber &&
                  isInactive (fiberLifecycle planFiber) && True = True)
                normalizedPlanGuard = replace
                  {p = \children => retired planFiber &&
                    isInactive (fiberLifecycle planFiber) && not children = True}
                  planNoChild planGuard
                0 survivorGuard : (retired survivorFiber &&
                    isInactive (fiberLifecycle survivorFiber) &&
                    not (hasChild @{nameEq} {name = name} {key = key}
                      {value = value} {world = world} {error = error} actor
                      survivor) = True)
                survivorGuard = rewrite survivorNoChild in
                  rewrite sym retiredSame in rewrite sym inactiveSame in
                    normalizedPlanGuard
                survivorAfter : SystemState name key value world error
                survivorAfter = MkSystemState survivorAmbient
                  (deleteBinding @{nameEq} actor survivor)
                0 survivorRaw : (applyAction @{nameEq} @{keyEq} (ORemove actor)
                      (MkSystemState survivorAmbient survivor) =
                    Just (ORemoveTag, survivorAfter))
                survivorRaw = rewrite survivorFound in rewrite survivorGuard in
                  Refl
                0 survivorAfterWellFormed :
                  (registryWellFormed @{nameEq} @{keyEq} survivorAfter = True)
                survivorAfterWellFormed = preservationTheoremProof nameEq keyEq
                  (ORemove actor) (MkSystemState survivorAmbient survivor) survivorAfter
                  ORemoveTag survivorWellFormed survivorRaw
                0 survivorChecked : (checkedApplyAction @{nameEq} @{keyEq}
                      (ORemove actor) (MkSystemState survivorAmbient survivor) =
                    Just (ORemoveTag, survivorAfter))
                survivorChecked = rewrite survivorRaw in
                  rewrite survivorAfterWellFormed in Refl
                0 nextOrdered : SelectedOrderedRegistryControlsRelated name key
                  world error value selected
                  (deleteEntries @{nameEq} actor (bindings plan))
                  (deleteEntries @{nameEq} actor (bindings survivor))
                nextOrdered = selectedOrderedDeleteForeign nameEq selected actor
                  actorDistinct (bindings plan) (bindings survivor) ordered
                0 planBindings : (bindings
                      (deleteBinding @{nameEq} actor plan) =
                    deleteEntries @{nameEq} actor (bindings plan))
                planBindings = deleteBindingRuntimeBindings nameEq actor plan
                0 survivorBindings : (bindings
                      (deleteBinding @{nameEq} actor survivor) =
                    deleteEntries @{nameEq} actor (bindings survivor))
                survivorBindings = deleteBindingRuntimeBindings nameEq actor
                  survivor
                0 finalOrdered : SelectedOrderedRegistryControlsRelated name key
                  world error value selected
                  (bindings (deleteBinding @{nameEq} actor plan))
                  (bindings (deleteBinding @{nameEq} actor survivor))
                finalOrdered = selectedOrderedTransport (sym planBindings)
                  (sym survivorBindings) nextOrdered
            in MkForeignOrchestrationControlReplay survivorAfter survivorRaw
              survivorChecked finalOrdered

0 partialRelatedRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
partialRelatedRewrite Refl Refl related = related

0 orchestrationMapOriginIndependent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False -> (tag : RuleTag) ->
  (leftOrigin, rightOrigin : SystemState name key value world error) ->
  (state : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq action tag leftOrigin state =
    partialEffectMapFor nameEq keyEq action tag rightOrigin state
orchestrationMapOriginIndependent nameEq keyEq
  (OInsert actor parent component) orchestration tag leftOrigin rightOrigin state =
    Refl
orchestrationMapOriginIndependent nameEq keyEq (ORetire actor) orchestration tag
  leftOrigin rightOrigin state = Refl
orchestrationMapOriginIndependent nameEq keyEq (ORemove actor) orchestration tag
  leftOrigin rightOrigin state = Refl
orchestrationMapOriginIndependent nameEq keyEq (LBegin actor) Refl tag leftOrigin
  rightOrigin state impossible
orchestrationMapOriginIndependent nameEq keyEq (LAdvance actor) Refl tag
  leftOrigin rightOrigin state impossible
orchestrationMapOriginIndependent nameEq keyEq (LDivert actor) Refl tag leftOrigin
  rightOrigin state impossible
orchestrationMapOriginIndependent nameEq keyEq (LLeave actor) Refl tag leftOrigin
  rightOrigin state impossible
orchestrationMapOriginIndependent nameEq keyEq (LUnload actor) Refl tag leftOrigin
  rightOrigin state impossible

||| The newly checked orchestration target realizes the exact transposed
||| Definition-60 output.  This is the effect/control join missing from the
||| earlier `ForeignSelectedEffectStep` scaffold.
public export
0 foreignOrchestrationControlMatchesEffectOutput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (tag : RuleTag) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (step : ForeignSelectedEffectStep name key world error value nameEq keyEq
    selected before afterState survivor
    (Fired nameEq keyEq action tag checked) whole) ->
  (planAfter : SystemState name key value world error) ->
  (replay : ForeignOrchestrationControlReplay name key world error value nameEq
    keyEq selected action tag planAfter survivor) ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq} (foreignControlAfter replay))
    (foreignSurvivorOutput step)
foreignOrchestrationControlMatchesEffectOutput nameEq keyEq selected action
  orchestration tag before afterState survivor checked whole step planAfter
  replay =
    case actualTransitionEffectFrame nameEq keyEq action tag survivor
      (foreignControlAfter replay) (foreignControlChecked replay) of
      MkActualEffectFrame actualFrame =>
        let 0 currentRuns : (partialEffectMapFor nameEq keyEq action tag survivor
              (projectEffectState @{nameEq} survivor) =
              Just (foreignSurvivorOutput step))
            currentRuns = trans
              (orchestrationMapOriginIndependent nameEq keyEq action
                orchestration tag survivor before
                (projectEffectState @{nameEq} survivor))
              (foreignMapRunsOnSurvivor step)
            0 atOutputs : PartialRelated (EffectState name key value world)
              (EffectStateRelated keyEq)
              (Just (foreignSurvivorOutput step))
              (Just (projectEffectState @{nameEq} (foreignControlAfter replay)))
            atOutputs = partialRelatedRewrite currentRuns Refl actualFrame
            0 outputToActual : EffectStateRelated keyEq
              (foreignSurvivorOutput step)
              (projectEffectState @{nameEq} (foreignControlAfter replay))
            outputToActual = case atOutputs of PartialDefined related => related
        in symmetric (EffectStateEquivalence keyEq) outputToActual

public export
0 foreignOrchestrationControlGivesNextEffectBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (tag : RuleTag) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (step : ForeignSelectedEffectStep name key world error value nameEq keyEq
    selected before afterState survivor
    (Fired nameEq keyEq action tag checked) whole) ->
  (planAfter : SystemState name key value world error) ->
  (replay : ForeignOrchestrationControlReplay name key world error value nameEq
    keyEq selected action tag planAfter survivor) ->
  SelectedEffectReplayBoundary name key world error value nameEq keyEq selected
    whole afterState (foreignControlAfter replay)
foreignOrchestrationControlGivesNextEffectBoundary nameEq keyEq selected action
  orchestration tag before afterState survivor checked whole step planAfter
  replay = foreignEffectStepGivesNextBoundary nameEq keyEq selected
    (Fired nameEq keyEq action tag checked) whole step
    (foreignOrchestrationControlMatchesEffectOutput nameEq keyEq selected action
      orchestration tag before afterState survivor checked whole step planAfter
      replay)

||| Successful insert views expose the exact fresh endpoint cell.
public export
0 foreignInsertTargetFound :
  (view : ForeignInsertPlanView name key world error value nameEq keyEq actor
    parent component ambient source tag afterState) ->
  lookupFiber @{nameEq} actor (registry afterState) =
    Just (freshFiber component parent)
foreignInsertTargetFound (MkForeignInsertPlanView absent guards) =
  lookupInserted actor (freshFiber component parent) source absent

public export
0 foreignInsertViewAbsent :
  (view : ForeignInsertPlanView name key world error value nameEq keyEq actor
    parent component ambient source tag afterState) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Nothing
foreignInsertViewAbsent (MkForeignInsertPlanView absent guards) = absent
