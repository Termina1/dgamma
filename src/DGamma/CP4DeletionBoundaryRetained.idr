module DGamma.CP4DeletionBoundaryRetained

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionChildlessInvariant
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlBegin
import DGamma.CP4DeletionControlOrchestration
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanCommute
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanSuccess
import DGamma.CP4DeletionRetainedAction
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Decidable.Equality

%default total

0 nothingNotJustRetained : Nothing = Just item -> Void
nothingNotJustRetained Refl impossible

0 lookupOutsideInactivePlan :
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  ActorOutsideDeletionPlan actor plan ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor target =
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source
lookupOutsideInactivePlan nameEq actor source source NoInactiveLeafDeletion
  ActorOutsideDeletionEnd = Refl
lookupOutsideInactivePlan nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest distinct outsideRest) =
    trans (lookupOutsideInactivePlan nameEq actor
      (deleteBinding @{nameEq} removed source) target rest outsideRest)
      (lookupDeleteOther actor removed distinct source)

0 orchestrationOwnerOutside :
  {action : Action name key value world error} ->
  {source, target : Registry name key value world error} ->
  {nameEq : DecEq name} ->
  {plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target} ->
  OrchestrationOutsideDeletionPlan action plan ->
  ActorOutsideDeletionPlan (actionOwner action) plan
orchestrationOwnerOutside OrchestrationOutsideDeletionEnd =
  ActorOutsideDeletionEnd
orchestrationOwnerOutside
  (OrchestrationOutsideDeletionStep rest ownerOutside parentOutside outsideRest) =
    ActorOutsideDeletionStep rest ownerOutside
      (orchestrationOwnerOutside outsideRest)

public export
record BoundaryActionTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (planBefore, planAfter, survivorBefore :
    SystemState name key value world error)
  (tag : RuleTag) where
  constructor MkBoundaryActionTransport
  boundaryTransportAfter : SystemState name key value world error
  0 boundaryTransportRaw : applyAction @{nameEq} @{keyEq} action survivorBefore =
    Just (tag, boundaryTransportAfter)
  0 boundaryTransportSnapshot : runtimeSnapshot planAfter =
    runtimeSnapshot boundaryTransportAfter
  0 boundaryTransportWellFormed : registryWellFormed @{nameEq} @{keyEq}
    boundaryTransportAfter = True
  boundaryTransportNamed : NamedTransition name key world error value action
    survivorBefore
  0 boundaryTransportNamedAfter : namedAfter boundaryTransportNamed =
    boundaryTransportAfter
  0 boundaryTransportFires : fireNamed nameEq keyEq action survivorBefore =
    Just boundaryTransportNamed

0 transportPlanActionToBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (planBefore, planAfter, survivorBefore :
    SystemState name key value world error) ->
  runtimeSnapshot planBefore = runtimeSnapshot survivorBefore ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action planBefore = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} survivorBefore = True ->
  BoundaryActionTransport name key world error value nameEq keyEq action
    planBefore planAfter survivorBefore tag
transportPlanActionToBoundary nameEq keyEq action planBefore planAfter
  survivorBefore snapshotsSame tag planRaw survivorWellFormed =
    case transportApplyActionAcrossRuntimeSnapshot nameEq keyEq action planBefore
      survivorBefore snapshotsSame tag planAfter planRaw of
      MkActionRuntimeTransport survivorAfter survivorRaw afterSnapshots =>
        let 0 survivorAfterWellFormed = preservationTheoremProof nameEq keyEq
              action survivorBefore survivorAfter tag survivorWellFormed
              survivorRaw
            survivorChecked : (checkedApplyAction @{nameEq} @{keyEq} action
              survivorBefore = Just (tag, survivorAfter))
            survivorChecked = rewrite survivorRaw in
              rewrite survivorAfterWellFormed in Refl
            survivorTransition : Transition survivorBefore survivorAfter
            survivorTransition = Fired nameEq keyEq action tag survivorChecked
            named : NamedTransition name key world error value action
              survivorBefore
            named = MkNamedTransition survivorAfter tag survivorTransition Refl
            0 fired : fireNamed nameEq keyEq action survivorBefore = Just named
            fired = rewrite survivorChecked in Refl
        in MkBoundaryActionTransport survivorAfter survivorRaw afterSnapshots
          survivorAfterWellFormed named Refl fired

0 boundaryTransportWorldFromPlan :
  (transport : BoundaryActionTransport name key world error value nameEq keyEq
    action planBefore (MkSystemState ambient afterRegistry) survivorBefore tag) ->
  worldState (boundaryTransportAfter transport) = ambient
boundaryTransportWorldFromPlan transport =
  sym (cong snapshotWorld (boundaryTransportSnapshot transport))

0 boundaryTransportBindingsFromPlan :
  (transport : BoundaryActionTransport name key world error value nameEq keyEq
    action planBefore (MkSystemState ambient afterRegistry) survivorBefore tag) ->
  bindings (registry (boundaryTransportAfter transport)) =
    bindings afterRegistry
boundaryTransportBindingsFromPlan transport =
  sym (cong snapshotBindings (boundaryTransportSnapshot transport))

public export
record RetainedNoEpisodeBoundaryStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (registered : List (RegistrationGeneration name))
  (nextLive : GenerationEnvironment name)
  (action : Action name key value world error)
  (originalAfter, survivorBefore : SystemState name key value world error) where
  constructor MkRetainedNoEpisodeBoundaryStep
  retainedBoundaryNamed : NamedTransition name key world error value action
    survivorBefore
  0 retainedBoundaryFires : fireNamed nameEq keyEq action survivorBefore =
    Just retainedBoundaryNamed
  0 retainedNextBoundary : NoEpisodeReplayBoundary name key world error value
    nameEq keyEq registered nextLive originalAfter
    (namedAfter retainedBoundaryNamed)

public export
data InsertSuccessView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkInsertSuccessView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} -> {parent : Parent name} ->
    {component : Component key value world error} -> {ambient : world} ->
    {source : Registry name key value world error} ->
    (absent : lookupFiber @{nameEq} actor source = Nothing) ->
    InsertSuccessView name key world error value nameEq actor parent component
      ambient source OInsertTag
      (MkSystemState ambient
        (insertBinding @{nameEq} actor (freshFiber component parent) source
          absent))

0 insertSuccessView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (OInsert actor parent component))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  InsertSuccessView name key world error value nameEq actor parent component
    ambient source tag afterState
insertSuccessView nameEq keyEq actor parent component ambient source tag afterState
  raw with (parentPresent @{nameEq} parent source &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers source)) proof guards
  insertSuccessView nameEq keyEq actor parent component ambient source tag
    afterState raw | False = void (nothingNotJustRetained raw)
  insertSuccessView nameEq keyEq actor parent component ambient source tag
    afterState raw | True
    with (setFresh @{nameEq} actor (freshFiber component parent) source)
      proof inserted
    insertSuccessView nameEq keyEq actor parent component ambient source tag
      afterState raw | True | Nothing = void (nothingNotJustRetained raw)
    insertSuccessView nameEq keyEq actor parent component ambient source tag
      afterState raw | True | Just applied = case justInjective raw of
        Refl => rewrite setFreshAfter nameEq actor (freshFiber component parent)
          source applied inserted in
          MkInsertSuccessView
            (setFreshAbsent nameEq actor (freshFiber component parent) source
              applied inserted)

0 snapshotWorldEquality :
  runtimeSnapshot left = runtimeSnapshot right ->
  worldState left = worldState right
snapshotWorldEquality same = cong snapshotWorld same

0 snapshotBindingsEquality :
  runtimeSnapshot left = runtimeSnapshot right ->
  bindings (registry left) = bindings (registry right)
snapshotBindingsEquality same = cong snapshotBindings same

data KnownRetireSuccess :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (oldFiber : Fiber name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkKnownRetireSuccess :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} -> {ambient : world} ->
    {source : Registry name key value world error} ->
    {oldFiber : Fiber name key value world error} ->
    KnownRetireSuccess name key world error value nameEq actor ambient source
      oldFiber ORetireTag
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor (retireFiber oldFiber) source))

0 retireSuccessAtKnownFiber :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (oldFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor source = Just oldFiber ->
  (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORetire actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  KnownRetireSuccess name key world error value nameEq actor ambient source
    oldFiber tag afterState
retireSuccessAtKnownFiber nameEq keyEq actor ambient source oldFiber known tag
  afterState raw =
    let 0 reduced : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (ORetire actor))
          (MkSystemState ambient source) =
          Just (ORetireTag, MkSystemState ambient
            (replaceBinding @{nameEq} actor (retireFiber oldFiber) source)))
        reduced = rewrite known in Refl
        0 samePair :
          (ORetireTag, MkSystemState ambient
            (replaceBinding @{nameEq} actor (retireFiber oldFiber) source)) =
          (tag, afterState)
        samePair = justInjective (trans (sym reduced) raw)
    in case samePair of Refl => MkKnownRetireSuccess

||| Retained O-Retire preserves the complete replay boundary and produces the
||| exact checked survivor head.
public export
0 retainedRetirePreservesNoEpisodeBoundary :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORetire actor)) original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq (ORetire actor) original rest ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORetire actor))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live (ORetire actor) originalAfter survivor
retainedRetirePreservesNoEpisodeBoundary {name} {key} {world} {error} {value}
  protocol nameEq keyEq registered ordinal live actor original survivor
  (MkNoEpisodeReplayBoundary ambient source originalShape
    (MkCompleteCurrentRegisteredPlanResult
      oldPlan@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
      oldComplete)
    survivorAmbient survivorBindings unique sourceWellFormed survivorWellFormed)
  tag checked rest discipline retained = case originalShape of
    Refl =>
      let 0 originalRaw = checkedActionProjects nameEq keyEq (ORetire actor)
            (MkSystemState ambient source) originalAfter tag checked
          0 outside = retainedOrchestrationOutsidePlan protocol nameEq keyEq
            registered ordinal live unique (ORetire actor) Refl
            (MkSystemState ambient source) originalAfter tag originalRaw rest
            discipline retained
              (MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
          0 ownerOutside = orchestrationOwnerOutside outside
          0 planRawResult = orchestrationRawAfterInactivePlan nameEq keyEq
            (ORetire actor) Refl ambient source oldTarget oldInactive outside
            originalRaw
      in case retireSuccessView nameEq keyEq actor ambient source tag
        originalAfter originalRaw of
        MkRetireSuccessView oldFiber oldFound =>
          let 0 planOldFound : (lookupFiber @{nameEq} {name = name}
                {key = key} {value = value} {world = world} {error = error}
                actor oldTarget = Just oldFiber)
              planOldFound = trans
                (lookupOutsideInactivePlan nameEq actor source oldTarget
                  oldInactive ownerOutside) oldFound
              0 canonicalPlanRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (ORetire actor))
                (MkSystemState ambient oldTarget) =
                Just (ORetireTag, MkSystemState ambient
                  (replaceBinding @{nameEq} actor (retireFiber oldFiber)
                    oldTarget)))
              canonicalPlanRaw = rewrite planOldFound in Refl
          in case replaceOutsideThroughInactivePlan nameEq actor oldFiber
                        (retireFiber oldFiber) source oldTarget oldInactive
                        ownerOutside oldFound (fiberParentRetireHint oldFiber) of
                        preserving@(MkInactivePlanPreservingUpdateCommute
                          base@(MkInactivePlanUpdateCommute nextTarget nextInactive
                            nextTargetBindings nextOutside) actorsSame) =>
                            let nextPlan : CurrentRegisteredPlanResult name key
                                  world error value nameEq registered live
                                  (replaceBinding @{nameEq} actor
                                    (retireFiber oldFiber) source)
                                nextPlan = MkCurrentRegisteredPlanResult nextTarget
                                  nextInactive
                                  (\observed, outsideCurrent =>
                                    nextOutside observed
                                      (oldOutside observed outsideCurrent))
                                0 nextComplete : CurrentRegisteredPlanComplete name
                                  key world error value nameEq registered live
                                  nextPlan
                                nextComplete selected generation present member =
                                  replace {p = Elem selected} (sym actorsSame)
                                    (oldComplete selected generation present member)
                            in case transportPlanActionToBoundary nameEq keyEq
                              (ORetire actor) (MkSystemState ambient oldTarget)
                              (MkSystemState ambient
                                (replaceBinding @{nameEq} actor
                                  (retireFiber oldFiber) oldTarget)) survivor
                              (boundaryPlanSnapshotMatchesSurvivor
                                (MkNoEpisodeReplayBoundary ambient source Refl
                                  (MkCompleteCurrentRegisteredPlanResult
                                    (MkCurrentRegisteredPlanResult oldTarget
                                      oldInactive oldOutside) oldComplete)
                                  survivorAmbient survivorBindings unique
                                  sourceWellFormed survivorWellFormed))
                              ORetireTag canonicalPlanRaw survivorWellFormed of
                              MkBoundaryActionTransport survivorAfter survivorRaw
                                afterSnapshots survivorAfterWellFormed named
                                namedAfterProof fired =>
                                let 0 survivorAmbientNext :
                                      (worldState survivorAfter = ambient)
                                    survivorAmbientNext =
                                      sym (cong snapshotWorld afterSnapshots)
                                    0 survivorBindingsNext :
                                       (bindings (registry survivorAfter) =
                                       bindings nextTarget)
                                    survivorBindingsNext = trans
                                       (sym (cong snapshotBindings afterSnapshots))
                                       (trans
                                         (replaceBindingRuntimeBindings nameEq
                                           actor (retireFiber oldFiber) oldTarget)
                                         (sym nextTargetBindings))
                                    0 originalAfterWellFormed :
                                       (registryWellFormed @{nameEq} @{keyEq}
                                         (the (SystemState name key value world
                                           error) (MkSystemState ambient
                                           (replaceBinding @{nameEq} actor
                                             (retireFiber oldFiber) source))) =
                                         True)
                                    originalAfterWellFormed =
                                       preservationTheoremProof nameEq keyEq
                                         (ORetire actor)
                                         (MkSystemState ambient source)
                                         (MkSystemState ambient
                                           (replaceBinding @{nameEq} actor
                                             (retireFiber oldFiber) source))
                                         ORetireTag sourceWellFormed originalRaw
                                    0 nextBoundary : NoEpisodeReplayBoundary name
                                       key world error value nameEq keyEq registered
                                       live
                                       (MkSystemState ambient
                                         (replaceBinding @{nameEq} actor
                                           (retireFiber oldFiber) source))
                                       survivorAfter
                                    nextBoundary = MkNoEpisodeReplayBoundary ambient
                                       (replaceBinding @{nameEq} actor
                                         (retireFiber oldFiber) source) Refl
                                       (MkCompleteCurrentRegisteredPlanResult
                                         nextPlan nextComplete)
                                       survivorAmbientNext survivorBindingsNext
                                       unique originalAfterWellFormed
                                       survivorAfterWellFormed
                                    0 namedBoundary : NoEpisodeReplayBoundary name
                                       key world error value nameEq keyEq registered
                                       live
                                       (MkSystemState ambient
                                         (replaceBinding @{nameEq} actor
                                           (retireFiber oldFiber) source))
                                       (namedAfter named)
                                    namedBoundary = replace {p = \candidate =>
                                       NoEpisodeReplayBoundary name key world error
                                         value nameEq keyEq registered live
                                         (MkSystemState ambient
                                           (replaceBinding @{nameEq} actor
                                             (retireFiber oldFiber) source))
                                         candidate}
                                       (sym namedAfterProof)
                                       nextBoundary
                               in MkRetainedNoEpisodeBoundaryStep named fired
                                 namedBoundary

0 hasChildFalseAfterInactivePlan :
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor target = False
hasChildFalseAfterInactivePlan nameEq actor source source
  NoInactiveLeafDeletion noChild = noChild
hasChildFalseAfterInactivePlan nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    removedNoChild rest) noChild =
      hasChildFalseAfterInactivePlan nameEq actor
        (deleteBinding @{nameEq} removed source) target rest
        (hasChildDeleteFalse nameEq actor removed source noChild)

||| Retained O-Remove closes a non-R generation in both the original and
||| survivor traces.  The outside deletion commutes through the complete R plan,
||| and the generation environment is reindexed without dropping any R leaf.
public export
0 retainedRemovePreservesNoEpisodeBoundary :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORemove actor)) original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq (ORemove actor) original rest ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORemove actor))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered (deleteCurrentGeneration @{nameEq} actor live)
    (ORemove actor) originalAfter survivor
retainedRemovePreservesNoEpisodeBoundary {name} {key} {world} {error} {value}
  protocol nameEq keyEq registered ordinal live actor original survivor
  (MkNoEpisodeReplayBoundary ambient source originalShape
    (MkCompleteCurrentRegisteredPlanResult
      oldPlan@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
      oldComplete)
    survivorAmbient survivorBindings unique sourceWellFormed survivorWellFormed)
  tag checked rest discipline retained = case originalShape of
    Refl =>
      let 0 originalRaw = checkedActionProjects nameEq keyEq (ORemove actor)
            (MkSystemState ambient source) originalAfter tag checked
          0 outside = retainedOrchestrationOutsidePlan protocol nameEq keyEq
            registered ordinal live unique (ORemove actor) Refl
            (MkSystemState ambient source) originalAfter tag originalRaw rest
            discipline retained
              (MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
          0 ownerOutside = orchestrationOwnerOutside outside
      in case removeSuccessView nameEq keyEq actor ambient source tag
        originalAfter originalRaw of
        MkRemoveSuccessView oldFiber oldFound originalGuard originalNoChild =>
          let 0 planOldFound : (lookupFiber @{nameEq} {name = name}
                {key = key} {value = value} {world = world} {error = error}
                actor oldTarget = Just oldFiber)
              planOldFound = trans
                (lookupOutsideInactivePlan nameEq actor source oldTarget
                  oldInactive ownerOutside) oldFound
              0 planNoChild : hasChild @{nameEq} {name = name} {key = key}
                {value = value} {world = world} {error = error} actor oldTarget =
                False
              planNoChild = hasChildFalseAfterInactivePlan nameEq actor source
                oldTarget oldInactive originalNoChild
              0 normalizedGuard : (retired oldFiber &&
                isInactive (fiberLifecycle oldFiber) && True = True)
              normalizedGuard = replace {p = \children =>
                retired oldFiber && isInactive (fiberLifecycle oldFiber) &&
                  not children = True} originalNoChild originalGuard
              0 planGuard : (retired oldFiber &&
                isInactive (fiberLifecycle oldFiber) &&
                not (hasChild @{nameEq} {name = name} {key = key}
                  {value = value} {world = world} {error = error} actor
                  oldTarget) = True)
              planGuard = rewrite planNoChild in normalizedGuard
              0 canonicalPlanRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (ORemove actor))
                (MkSystemState ambient oldTarget) =
                Just (ORemoveTag, MkSystemState ambient
                  (deleteBinding @{nameEq} actor oldTarget)))
              canonicalPlanRaw = rewrite planOldFound in rewrite planGuard in Refl
              0 removedOutsideCurrent : ActorOutsideCurrentRegistered actor
                registered live
              removedOutsideCurrent = actorOutsideCurrentFromCompletePlan
                (MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
                oldComplete actor ownerOutside
          in case deleteOutsideThroughInactivePlan nameEq actor source oldTarget
            oldInactive ownerOutside of
            MkInactivePlanPreservingUpdateCommute
              (MkInactivePlanUpdateCommute nextTarget nextInactive
                nextTargetBindings nextOutside) actorsSame =>
              let
                  0 outsideBack : (observed : name) ->
                    ActorOutsideCurrentRegistered observed registered (deleteCurrentGeneration @{nameEq} actor live) ->
                    ActorOutsideCurrentRegistered observed registered live
                  outsideBack observed outsideCurrent selected generation present
                    member = outsideCurrent selected generation
                      (deletePreservesOtherEntry nameEq actor selected
                        (removedOutsideCurrent selected generation present member)
                        generation live present) member
                  0 outsideNew : (observed : name) ->
                    ActorOutsideCurrentRegistered observed registered (deleteCurrentGeneration @{nameEq} actor live) ->
                    ActorOutsideDeletionPlan observed nextInactive
                  outsideNew observed outsideCurrent = nextOutside observed
                    (oldOutside observed (outsideBack observed outsideCurrent))
                  nextPlan : CurrentRegisteredPlanResult name key world error
                    value nameEq registered (deleteCurrentGeneration @{nameEq} actor live)
                    (deleteBinding @{nameEq} actor source)
                  nextPlan = MkCurrentRegisteredPlanResult nextTarget nextInactive
                    outsideNew
                  0 nextComplete : CurrentRegisteredPlanComplete name key world
                    error value nameEq registered (deleteCurrentGeneration @{nameEq} actor live) nextPlan
                  nextComplete selected generation present member =
                    replace {p = Elem selected} (sym actorsSame)
                      (oldComplete selected generation
                        (entryAfterDeleteComesFromOld nameEq actor live selected
                          generation present) member)
              in case transportPlanActionToBoundary nameEq keyEq (ORemove actor)
                (MkSystemState ambient oldTarget)
                (MkSystemState ambient (deleteBinding @{nameEq} actor oldTarget))
                survivor
                (boundaryPlanSnapshotMatchesSurvivor
                  (MkNoEpisodeReplayBoundary ambient source Refl
                    (MkCompleteCurrentRegisteredPlanResult
                      (MkCurrentRegisteredPlanResult oldTarget oldInactive
                        oldOutside) oldComplete)
                    survivorAmbient survivorBindings unique sourceWellFormed
                    survivorWellFormed))
                ORemoveTag canonicalPlanRaw survivorWellFormed of
                MkBoundaryActionTransport survivorAfter survivorRaw
                  afterSnapshots survivorAfterWellFormed named namedAfterProof
                  fired =>
                  let 0 survivorAmbientNext :
                        (worldState survivorAfter = ambient)
                      survivorAmbientNext =
                        sym (cong snapshotWorld afterSnapshots)
                      0 survivorBindingsNext :
                        (bindings (registry survivorAfter) = bindings nextTarget)
                      survivorBindingsNext = trans
                        (sym (cong snapshotBindings afterSnapshots))
                        (trans (deleteBindingRuntimeBindings nameEq actor oldTarget)
                          (sym nextTargetBindings))
                      0 originalAfterWellFormed :
                        (registryWellFormed @{nameEq} @{keyEq}
                          (the (SystemState name key value world error)
                            (MkSystemState ambient
                              (deleteBinding @{nameEq} actor source))) = True)
                      originalAfterWellFormed = preservationTheoremProof nameEq
                        keyEq (ORemove actor) (MkSystemState ambient source)
                        (MkSystemState ambient
                          (deleteBinding @{nameEq} actor source)) ORemoveTag
                        sourceWellFormed originalRaw
                      0 nextUnique : GenerationEnvironmentNamesUnique (deleteCurrentGeneration @{nameEq} actor live)
                      nextUnique = advanceGenerationEnvironmentPreservesUnique
                        nameEq ordinal
                        (the (Action name key value world error) (ORemove actor))
                        live unique
                      0 nextBoundary : NoEpisodeReplayBoundary name key world
                        error value nameEq keyEq registered (deleteCurrentGeneration @{nameEq} actor live)
                        (MkSystemState ambient
                          (deleteBinding @{nameEq} actor source)) survivorAfter
                      nextBoundary = MkNoEpisodeReplayBoundary ambient
                        (deleteBinding @{nameEq} actor source) Refl
                        (MkCompleteCurrentRegisteredPlanResult nextPlan
                          nextComplete)
                        survivorAmbientNext survivorBindingsNext nextUnique
                        originalAfterWellFormed survivorAfterWellFormed
                      0 namedBoundary : NoEpisodeReplayBoundary name key world
                        error value nameEq keyEq registered (deleteCurrentGeneration @{nameEq} actor live)
                        (MkSystemState ambient
                          (deleteBinding @{nameEq} actor source))
                        (namedAfter named)
                      namedBoundary = replace {p = \candidate =>
                        NoEpisodeReplayBoundary name key world error value nameEq
                          keyEq registered (deleteCurrentGeneration @{nameEq} actor live)
                          (MkSystemState ambient
                            (deleteBinding @{nameEq} actor source)) candidate}
                        (sym namedAfterProof) nextBoundary
                  in MkRetainedNoEpisodeBoundaryStep named fired namedBoundary
