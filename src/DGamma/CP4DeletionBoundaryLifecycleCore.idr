module DGamma.CP4DeletionBoundaryLifecycleCore

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionPlanCommute
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanRuntime
import DGamma.CP4DeletionPlanSuccess
import Data.List.Elem
import Decidable.Equality

%default total

0 nothingNotJustLifecycleBoundary : Nothing = Just item -> Void
nothingNotJustLifecycleBoundary Refl impossible

0 unequalSymmetricLifecycleBoundary : Not (left = right) -> Not (right = left)
unequalSymmetricLifecycleBoundary distinct Refl = distinct Refl

||| Exact host-observable comparison for commuting one retained lifecycle action
||| past one distinct Inactive leaf.  The result deliberately compares ambient
||| state and ordered bindings, never the erased `UniqueKeys` certificate.
public export
record LifecycleDeleteRuntimeCommute
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error) (tag : RuleTag)
  (removed : name)
  (originalAfter, deletedBefore : SystemState name key value world error) where
  constructor MkLifecycleDeleteRuntimeCommute
  lifecycleDeleteReplayAfter : SystemState name key value world error
  0 lifecycleDeleteReplayRaw : applyAction @{nameEq} @{keyEq} action
    deletedBefore = Just (tag, lifecycleDeleteReplayAfter)
  0 lifecycleDeleteWorld : worldState originalAfter =
    worldState lifecycleDeleteReplayAfter
  0 lifecycleDeleteBindings :
    bindings (deleteBinding @{nameEq} removed (registry originalAfter)) =
    bindings (registry lifecycleDeleteReplayAfter)

||| Common constructor for every lifecycle evaluator branch: all five action
||| forms replace their owner's fiber and preserve its parent.  Distinct
||| replacement/deletion commutation supplies the exact ordered-binding result.
public export
0 replacementDeleteRuntimeCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (actor, removed : name) -> Not (actor = removed) ->
  (beforeWorld, afterWorld : world) ->
  (source : Registry name key value world error) ->
  (next : Fiber name key value world error) ->
  applyAction @{nameEq} @{keyEq} action
    (MkSystemState beforeWorld (deleteBinding @{nameEq} removed source)) =
    Just (tag, MkSystemState afterWorld
      (replaceBinding @{nameEq} actor next
        (deleteBinding @{nameEq} removed source))) ->
  LifecycleDeleteRuntimeCommute name key world error value nameEq keyEq action
    tag removed
    (MkSystemState afterWorld (replaceBinding @{nameEq} actor next source))
    (MkSystemState beforeWorld (deleteBinding @{nameEq} removed source))
replacementDeleteRuntimeCommute nameEq keyEq action tag actor removed distinct
  beforeWorld afterWorld source next replayRaw =
    MkLifecycleDeleteRuntimeCommute
      (MkSystemState afterWorld
        (replaceBinding @{nameEq} actor next
          (deleteBinding @{nameEq} removed source)))
      replayRaw Refl
      (trans
        (deleteBindingAfterDistinctReplaceBindings nameEq actor removed distinct
          next source)
        (sym (replaceBindingRuntimeBindings nameEq actor next
          (deleteBinding @{nameEq} removed source))))

public export
data RegistryUpdateRuntimeView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  Registry name key value world error -> Registry name key value world error ->
  Type where
  RuntimeViewedInsert :
    (inserted : Fiber name key value world error) ->
    (absent : lookupFiber @{nameEq} actor source = Nothing) ->
    target = insertBinding @{nameEq} actor inserted source absent ->
    RegistryUpdateRuntimeView name key world error value nameEq actor source
      target
  RuntimeViewedReplace :
    (next, oldFiber : Fiber name key value world error) ->
    (oldFound : lookupFiber @{nameEq} actor source = Just oldFiber) ->
    (sameParent : fiberParent next = fiberParent oldFiber) ->
    target = replaceBinding @{nameEq} actor next source ->
    RegistryUpdateRuntimeView name key world error value nameEq actor source
      target
  RuntimeViewedDelete :
    (oldFiber : Fiber name key value world error) ->
    (oldFound : lookupFiber @{nameEq} actor source = Just oldFiber) ->
    target = deleteBinding @{nameEq} actor source ->
    RegistryUpdateRuntimeView name key world error value nameEq actor source
      target

0 registryUpdateRuntimeView :
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  RegistryUpdateRuntimeView name key world error value nameEq actor source
    target
registryUpdateRuntimeView nameEq actor source _
  (LocalInsert inserted absent) = RuntimeViewedInsert inserted absent Refl
registryUpdateRuntimeView nameEq actor source _
  (LocalReplace next {oldFiber} {oldFound} {staticParent}) =
    RuntimeViewedReplace next oldFiber oldFound staticParent Refl
registryUpdateRuntimeView nameEq actor source _
  (LocalDelete {oldFiber} {oldFound}) =
    RuntimeViewedDelete oldFiber oldFound Refl

public export
0 lifecycleOwnerPresent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} (actionOwner action) (registry before) = Just fiber)
lifecycleOwnerPresent nameEq keyEq (OInsert actor parent component) Refl before
  afterState tag raw impossible
lifecycleOwnerPresent nameEq keyEq (ORetire actor) Refl before afterState tag raw
  impossible
lifecycleOwnerPresent nameEq keyEq (ORemove actor) Refl before afterState tag raw
  impossible
lifecycleOwnerPresent nameEq keyEq (LBegin actor) lifecycle
  (MkSystemState ambient source) afterState tag raw
  with (lookupFiber @{nameEq} actor source) proof found
  lifecycleOwnerPresent nameEq keyEq (LBegin actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Nothing =
      void (nothingNotJustLifecycleBoundary raw)
  lifecycleOwnerPresent nameEq keyEq (LBegin actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Just fiber =
      (fiber ** Refl)
lifecycleOwnerPresent nameEq keyEq (LAdvance actor) lifecycle
  (MkSystemState ambient source) afterState tag raw
  with (lookupFiber @{nameEq} actor source) proof found
  lifecycleOwnerPresent nameEq keyEq (LAdvance actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Nothing =
      void (nothingNotJustLifecycleBoundary raw)
  lifecycleOwnerPresent nameEq keyEq (LAdvance actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Just fiber =
      (fiber ** Refl)
lifecycleOwnerPresent nameEq keyEq (LDivert actor) lifecycle
  (MkSystemState ambient source) afterState tag raw
  with (lookupFiber @{nameEq} actor source) proof found
  lifecycleOwnerPresent nameEq keyEq (LDivert actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Nothing =
      void (nothingNotJustLifecycleBoundary raw)
  lifecycleOwnerPresent nameEq keyEq (LDivert actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Just fiber =
      (fiber ** Refl)
lifecycleOwnerPresent nameEq keyEq (LLeave actor) lifecycle
  (MkSystemState ambient source) afterState tag raw
  with (lookupFiber @{nameEq} actor source) proof found
  lifecycleOwnerPresent nameEq keyEq (LLeave actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Nothing =
      void (nothingNotJustLifecycleBoundary raw)
  lifecycleOwnerPresent nameEq keyEq (LLeave actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Just fiber =
      (fiber ** Refl)
lifecycleOwnerPresent nameEq keyEq (LUnload actor) lifecycle
  (MkSystemState ambient source) afterState tag raw
  with (lookupFiber @{nameEq} actor source) proof found
  lifecycleOwnerPresent nameEq keyEq (LUnload actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Nothing =
      void (nothingNotJustLifecycleBoundary raw)
  lifecycleOwnerPresent nameEq keyEq (LUnload actor) lifecycle
    (MkSystemState ambient source) afterState tag raw | Just fiber =
      (fiber ** Refl)

public export
record InactiveLeafSurvivesLifecycle
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (removed : name)
  (component : Component key value world error) (parent : Parent name)
  (retiredFlag : Bool)
  (table : OwnedTable key value (componentProvisions component))
  (outcome : Maybe error)
  (afterState : SystemState name key value world error) where
  constructor MkInactiveLeafSurvivesLifecycle
  0 survivingInactiveFound : lookupFiber @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} removed
    (registry afterState) =
    Just (MkFiber component parent retiredFlag table (Inactive outcome))
  0 survivingInactiveChildless : hasChild @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} removed
    (registry afterState) = False

||| Local-update metadata proves that a distinct lifecycle owner cannot disturb
||| an Inactive leaf or create a child for it.  The impossible insertion view is
||| refuted from successful lifecycle owner presence.
public export
0 inactiveLeafSurvivesLifecycle :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (removed : name) -> Not (actionOwner action = removed) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed (registry before) =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} removed (registry before) = False ->
  InactiveLeafSurvivesLifecycle name key world error value nameEq removed
    component parent retiredFlag table outcome afterState
inactiveLeafSurvivesLifecycle {name} {key} {world} {error} {value}
  nameEq keyEq action lifecycle
  before@(MkSystemState beforeWorld source)
  afterState@(MkSystemState afterWorld target) tag raw removed ownerDistinct
  component parent retiredFlag table outcome removedFound removedNoChild =
    let update = applyActionLocalUpdate nameEq keyEq action before afterState tag
          raw
        view = registryUpdateRuntimeView nameEq (actionOwner action) source target
          (systemRegistryUpdate update)
    in case view of
      RuntimeViewedInsert inserted absent targetShape =>
        let (ownerFiber ** ownerFound) = lifecycleOwnerPresent nameEq keyEq action
              lifecycle (MkSystemState beforeWorld source)
              (MkSystemState afterWorld target) tag raw
        in void (nothingNotJustLifecycleBoundary
          (trans (sym absent) ownerFound))
      RuntimeViewedReplace next oldFiber oldFound sameParent targetShape =>
        let 0 removedDifferentOwner : Not (removed = actionOwner action)
            removedDifferentOwner = unequalSymmetricLifecycleBoundary ownerDistinct
            0 targetFound : lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} removed target =
              Just (MkFiber component parent retiredFlag table
                (Inactive outcome))
            targetFound = trans (cong (lookupFiber @{nameEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              removed) targetShape)
              (trans (lookupReplaceOther removed (actionOwner action)
                removedDifferentOwner next source) removedFound)
            0 targetNoChild : hasChild @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} removed target =
              False
            targetNoChild = trans (cong (hasChild @{nameEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              removed) targetShape)
              (hasChildReplaceFalse nameEq removed (actionOwner action) next
                oldFiber source oldFound sameParent removedNoChild)
        in MkInactiveLeafSurvivesLifecycle targetFound targetNoChild
      RuntimeViewedDelete oldFiber oldFound targetShape =>
        let 0 removedDifferentOwner : Not (removed = actionOwner action)
            removedDifferentOwner = unequalSymmetricLifecycleBoundary ownerDistinct
            0 targetFound : lookupFiber @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} removed target =
              Just (MkFiber component parent retiredFlag table
                (Inactive outcome))
            targetFound = trans (cong (lookupFiber @{nameEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              removed) targetShape)
              (trans (lookupDeleteOther removed (actionOwner action)
                removedDifferentOwner source) removedFound)
            0 targetNoChild : hasChild @{nameEq} {name = name} {key = key}
              {value = value} {world = world} {error = error} removed target =
              False
            targetNoChild = trans (cong (hasChild @{nameEq} {name = name}
              {key = key} {value = value} {world = world} {error = error}
              removed) targetShape)
              (hasChildDeleteFalse nameEq removed (actionOwner action) source
                removedNoChild)
        in MkInactiveLeafSurvivesLifecycle targetFound targetNoChild

0 actorOutsideNotElem :
  {plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target} ->
  ActorOutsideDeletionPlan actor plan ->
  Not (Elem actor (inactivePlanActors plan))
actorOutsideNotElem ActorOutsideDeletionEnd member = case member of
  Here impossible
  There later impossible
actorOutsideNotElem
  (ActorOutsideDeletionStep rest headDistinct outsideRest) Here =
    headDistinct Refl
actorOutsideNotElem
  (ActorOutsideDeletionStep rest headDistinct outsideRest) (There later) =
    actorOutsideNotElem outsideRest later

0 actorOutsideFromNotElem :
  (actor : name) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  Not (Elem actor (inactivePlanActors plan)) ->
  ActorOutsideDeletionPlan actor plan
actorOutsideFromNotElem actor NoInactiveLeafDeletion absent =
  ActorOutsideDeletionEnd
actorOutsideFromNotElem actor
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) absent =
      ActorOutsideDeletionStep rest (\same => absent (replace
        {p = \observed => Elem actor (observed :: inactivePlanActors rest)}
        same Here))
        (actorOutsideFromNotElem actor rest (\later => absent (There later)))

||| Per-rule callback consumed by the structural whole-plan fold below.
public export
0 LifecycleOneDeleteCommuter :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) -> Type
LifecycleOneDeleteCommuter name key world error value nameEq keyEq action tag =
  (ambient : world) ->
  (source : Registry name key value world error) ->
  (removed : name) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} removed source =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  hasChild @{nameEq} removed source = False ->
  Not (actionOwner action = removed) ->
  registryWellFormed @{nameEq} @{keyEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient source)) = True ->
  {originalAfter : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} action (MkSystemState ambient source) =
    Just (tag, originalAfter) ->
  LifecycleDeleteRuntimeCommute name key world error value nameEq keyEq action
    tag removed originalAfter
    (MkSystemState ambient (deleteBinding @{nameEq} removed source))

||| Whole-plan commutation result.  The transformed plan starts at the original
||| evaluator endpoint, while the retained replay starts at the old plan target.
public export
record LifecyclePlanActionCommute
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error) (tag : RuleTag)
  {oldSource, oldTarget : Registry name key value world error}
  (oldPlan : InactiveLeafDeletionPlan {name = name} {key = key}
    {value = value} {world = world} {error = error} nameEq oldSource oldTarget)
  (ambient : world)
  (originalAfter : SystemState name key value world error) where
  constructor MkLifecyclePlanActionCommute
  lifecyclePlanReplayAfter : SystemState name key value world error
  0 lifecyclePlanReplayRaw : applyAction @{nameEq} @{keyEq} action
    (MkSystemState ambient oldTarget) =
    Just (tag, lifecyclePlanReplayAfter)
  lifecycleAfterCommute : InactivePlanPreservingUpdateCommute name key world
    error value nameEq oldPlan (registry originalAfter)
    (bindings (registry lifecyclePlanReplayAfter))
  0 lifecyclePlanWorld : worldState originalAfter =
    worldState lifecyclePlanReplayAfter

||| Structural fold of one-delete runtime commutation through a complete
||| Inactive-leaf plan.  Runtime plan transport bridges proof-distinct registry
||| certificates between consecutive recursive heads.
public export
0 lifecycleActionThroughInactivePlan :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (tag : RuleTag) ->
  (commuteOne : LifecycleOneDeleteCommuter name key world error value nameEq
    keyEq action tag) ->
  (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  ActorOutsideDeletionPlan (actionOwner action) plan ->
  registryWellFormed @{nameEq} @{keyEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient source)) = True ->
  {originalAfter : SystemState name key value world error} ->
  applyAction @{nameEq} @{keyEq} action (MkSystemState ambient source) =
    Just (tag, originalAfter) ->
  LifecyclePlanActionCommute name key world error value nameEq keyEq action tag
    plan ambient originalAfter
lifecycleActionThroughInactivePlan nameEq keyEq action lifecycle tag commuteOne
  ambient source source NoInactiveLeafDeletion ActorOutsideDeletionEnd
  sourceWellFormed raw =
    MkLifecyclePlanActionCommute originalAfter raw
      (MkInactivePlanPreservingUpdateCommute
        (MkInactivePlanUpdateCommute (registry originalAfter)
          NoInactiveLeafDeletion Refl
          (\actor, ActorOutsideDeletionEnd => ActorOutsideDeletionEnd)) Refl)
      Refl
lifecycleActionThroughInactivePlan {name} {key} {world} {error} {value}
  nameEq keyEq action lifecycle tag commuteOne ambient source target
  oldPlan@(DeleteInactiveLeaf removed component parent retiredFlag table outcome
    removedFound removedNoChild rest)
  (ActorOutsideDeletionStep rest ownerDistinct outsideRest)
  sourceWellFormed raw =
    let deletedSource : Registry name key value world error
        deletedSource = deleteBinding @{nameEq} removed source
        0 deletedWellFormed : registryWellFormed @{nameEq} @{keyEq}
          (the (SystemState name key value world error)
            (MkSystemState ambient deletedSource)) = True
        deletedWellFormed = registryWellFormedInactiveDelete nameEq keyEq ambient
          removed component parent retiredFlag table outcome source removedFound
          removedNoChild sourceWellFormed
        0 headCommute : LifecycleDeleteRuntimeCommute name key world error
          value nameEq keyEq action tag removed originalAfter
          (MkSystemState ambient deletedSource)
        headCommute = commuteOne ambient source removed component parent
          retiredFlag table outcome removedFound removedNoChild ownerDistinct
          sourceWellFormed raw
        0 replayRaw : applyAction @{nameEq} @{keyEq} action
          (MkSystemState ambient deletedSource) =
          Just (tag, lifecycleDeleteReplayAfter headCommute)
        replayRaw = lifecycleDeleteReplayRaw headCommute
        0 recursive : LifecyclePlanActionCommute name key world error value
          nameEq keyEq action tag rest ambient
          (lifecycleDeleteReplayAfter headCommute)
        recursive = lifecycleActionThroughInactivePlan nameEq keyEq action
          lifecycle tag commuteOne ambient deletedSource target rest outsideRest
          deletedWellFormed replayRaw
        0 recursiveBase : InactivePlanUpdateCommute name key world error value
          nameEq rest (registry (lifecycleDeleteReplayAfter headCommute))
          (bindings (registry (lifecyclePlanReplayAfter recursive)))
        recursiveBase = preservingUpdateCommute
          (lifecycleAfterCommute recursive)
        canonicalAfterDelete : Registry name key value world error
        canonicalAfterDelete = deleteBinding @{nameEq} removed
          (registry originalAfter)
        0 recursiveSourceBindings :
          bindings (registry (lifecycleDeleteReplayAfter headCommute)) =
          bindings canonicalAfterDelete
        recursiveSourceBindings = sym (lifecycleDeleteBindings headCommute)
        0 transported : InactivePlanBindingsTransport name key world error
          value nameEq (commutedInactivePlan recursiveBase)
          canonicalAfterDelete
        transported = transportInactivePlanAcrossBindings nameEq
          (registry (lifecycleDeleteReplayAfter headCommute))
          (commutedPlanTarget recursiveBase) canonicalAfterDelete
          (commutedInactivePlan recursiveBase) recursiveSourceBindings
        0 survived : InactiveLeafSurvivesLifecycle name key world error value
          nameEq removed component parent retiredFlag table outcome originalAfter
        survived = inactiveLeafSurvivesLifecycle nameEq keyEq action lifecycle
          (MkSystemState ambient source) originalAfter tag raw removed ownerDistinct
          component parent retiredFlag table outcome removedFound removedNoChild
        nextPlan : InactiveLeafDeletionPlan {name = name} {key = key}
          {value = value} {world = world} {error = error} nameEq
          (registry originalAfter) (transportedPlanTarget transported)
        nextPlan = DeleteInactiveLeaf removed component parent retiredFlag table
          outcome (survivingInactiveFound survived)
          (survivingInactiveChildless survived)
          (transportedInactivePlan transported)
        0 targetBindings : bindings (transportedPlanTarget transported) =
          bindings (registry (lifecyclePlanReplayAfter recursive))
        targetBindings = trans (sym (transportedPlanBindings transported))
          (commutedTargetBindings recursiveBase)
        0 actorsSame : inactivePlanActors nextPlan = inactivePlanActors oldPlan
        actorsSame = cong (removed ::)
          (trans (transportedPlanActors transported)
            (preservedPlanActors (lifecycleAfterCommute recursive)))
        0 outsideMap : (actor : name) ->
          ActorOutsideDeletionPlan actor oldPlan ->
          ActorOutsideDeletionPlan actor nextPlan
        outsideMap actor outside = actorOutsideFromNotElem actor nextPlan
          (\present => actorOutsideNotElem outside
            (replace {p = Elem actor} actorsSame present))
        0 commuted : InactivePlanPreservingUpdateCommute name key world error
          value nameEq oldPlan (registry originalAfter)
          (bindings (registry (lifecyclePlanReplayAfter recursive)))
        commuted = MkInactivePlanPreservingUpdateCommute
          (MkInactivePlanUpdateCommute (transportedPlanTarget transported)
            nextPlan targetBindings outsideMap) actorsSame
    in MkLifecyclePlanActionCommute
      (lifecyclePlanReplayAfter recursive)
      (lifecyclePlanReplayRaw recursive) commuted
      (trans (lifecycleDeleteWorld headCommute)
        (lifecyclePlanWorld recursive))
