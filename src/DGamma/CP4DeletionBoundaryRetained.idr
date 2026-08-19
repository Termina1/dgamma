module DGamma.CP4DeletionBoundaryRetained

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionBoundaryLifecycleBegin
import DGamma.CP4DeletionBoundaryLifecycleAdvance
import DGamma.CP4DeletionBoundaryLifecycleDivert
import DGamma.CP4DeletionBoundaryLifecycleLeave
import DGamma.CP4DeletionBoundaryLifecycleUnload
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

0 systemStateRuntimeEta :
  (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
systemStateRuntimeEta (MkSystemState ambient source) = Refl

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

||| Shared boundary assembly for all five retained lifecycle heads.  The
||| rule-specific callback proves one-leaf evaluator commutation; the core fold
||| transports it through the complete current-R plan, after which runtime
||| snapshot transport reconstructs the exact checked survivor head.
public export
0 retainedLifecyclePreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (nonInsert : NonInsertAction action) ->
  (tag : RuleTag) ->
  (commuteOne : LifecycleOneDeleteCommuter name key world error value nameEq
    keyEq action tag) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live action originalAfter survivor
retainedLifecyclePreservesNoEpisodeBoundary {name} {key} {world} {error} {value}
  nameEq keyEq registered ordinal live action lifecycle nonInsert tag commuteOne
  original survivor
  (MkNoEpisodeReplayBoundary ambient source originalShape
    oldComplete@(MkCompleteCurrentRegisteredPlanResult
      oldPlan@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
      oldCompleteProof)
    survivorAmbient survivorBindings unique sourceWellFormed survivorWellFormed)
  checked retained = case originalShape of
    Refl =>
      let 0 originalRaw = checkedActionProjects nameEq keyEq action
            (MkSystemState ambient source) originalAfter tag checked
          0 outsideCurrent = retainedNonInsertOutsideCurrentRegistered nameEq
            registered ordinal live unique action nonInsert retained
          0 outsidePlan = oldOutside (actionOwner action) outsideCurrent
          0 planCommute : LifecyclePlanActionCommute name key world error value
            nameEq keyEq action tag oldInactive ambient originalAfter
          planCommute = lifecycleActionThroughInactivePlan nameEq keyEq action
            lifecycle tag commuteOne ambient source oldTarget oldInactive
            outsidePlan sourceWellFormed originalRaw
          0 preserving : InactivePlanPreservingUpdateCommute name key world
            error value nameEq oldInactive (registry originalAfter)
            (bindings (registry (lifecyclePlanReplayAfter planCommute)))
          preserving = lifecycleAfterCommute planCommute
          0 commuteBase : InactivePlanUpdateCommute name key world error value
            nameEq oldInactive (registry originalAfter)
            (bindings (registry (lifecyclePlanReplayAfter planCommute)))
          commuteBase = preservingUpdateCommute preserving
          0 outsideNext : (observed : name) ->
            ActorOutsideCurrentRegistered observed registered live ->
            ActorOutsideDeletionPlan observed
              (commutedInactivePlan commuteBase)
          outsideNext observed outsideCurrent = commutedActorOutside commuteBase
            observed (oldOutside observed outsideCurrent)
          nextPlan : CurrentRegisteredPlanResult name key world error value
            nameEq registered live (registry originalAfter)
          nextPlan = MkCurrentRegisteredPlanResult
            (commutedPlanTarget commuteBase) (commutedInactivePlan commuteBase)
            outsideNext
          0 nextCompleteProof : CurrentRegisteredPlanComplete name key world
            error value nameEq registered live nextPlan
          nextCompleteProof selected generation present member =
            replace {p = Elem selected} (sym (preservedPlanActors preserving))
              (oldCompleteProof selected generation present member)
          completeNext : CompleteCurrentRegisteredPlanResult name key world
            error value nameEq registered live (registry originalAfter)
          completeNext = MkCompleteCurrentRegisteredPlanResult nextPlan
            nextCompleteProof
      in case transportPlanActionToBoundary nameEq keyEq action
              (MkSystemState ambient oldTarget)
              (lifecyclePlanReplayAfter planCommute) survivor
              (boundaryPlanSnapshotMatchesSurvivor
                (MkNoEpisodeReplayBoundary ambient source Refl
                  (MkCompleteCurrentRegisteredPlanResult
                    (MkCurrentRegisteredPlanResult oldTarget oldInactive
                      oldOutside) oldCompleteProof)
                  survivorAmbient survivorBindings unique sourceWellFormed
                  survivorWellFormed))
          tag (lifecyclePlanReplayRaw planCommute) survivorWellFormed of
          MkBoundaryActionTransport survivorAfter survivorRaw
            afterSnapshots survivorAfterWellFormed named namedAfterProof
            fired =>
                  let 0 survivorAmbientNext : (worldState survivorAfter =
                        worldState originalAfter)
                      survivorAmbientNext = trans
                        (sym (cong snapshotWorld afterSnapshots))
                        (sym (lifecyclePlanWorld planCommute))
                      0 survivorBindingsNext :
                        (bindings (registry survivorAfter) =
                        bindings (planTarget nextPlan))
                      survivorBindingsNext = trans
                        (sym (cong snapshotBindings afterSnapshots))
                        (sym (commutedTargetBindings commuteBase))
                      0 originalAfterWellFormed :
                        (registryWellFormed @{nameEq} @{keyEq} originalAfter =
                          True)
                      originalAfterWellFormed = preservationTheoremProof
                        nameEq keyEq action (MkSystemState ambient source)
                        originalAfter tag sourceWellFormed originalRaw
                      0 nextBoundary : NoEpisodeReplayBoundary name key world
                        error value nameEq keyEq registered live originalAfter
                        survivorAfter
                      nextBoundary = MkNoEpisodeReplayBoundary
                        (worldState originalAfter) (registry originalAfter)
                        (sym (systemStateRuntimeEta originalAfter)) completeNext
                        survivorAmbientNext survivorBindingsNext unique
                        originalAfterWellFormed survivorAfterWellFormed
                      0 namedBoundary : NoEpisodeReplayBoundary name key world
                        error value nameEq keyEq registered live originalAfter
                        (namedAfter named)
                      namedBoundary = replace {p = \candidate =>
                        NoEpisodeReplayBoundary name key world error value
                          nameEq keyEq registered live originalAfter candidate}
                        (sym namedAfterProof) nextBoundary
                  in MkRetainedNoEpisodeBoundaryStep named fired namedBoundary

||| Retained non-R L-Begin preserves exact result/control after deleting all
||| current R leaves.
public export
0 retainedBeginPreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LBegin actor)) original =
    Just (tag, originalAfter)) ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (LBegin actor))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live (LBegin actor) originalAfter survivor
retainedBeginPreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
  actor original survivor boundary tag checked retained =
    retainedLifecyclePreservesNoEpisodeBoundary nameEq keyEq registered ordinal
      live (LBegin actor) Refl NonInsertBegin tag
      (beginOneDeleteRuntimeCommute nameEq keyEq actor) original survivor boundary
      checked retained

||| Retained non-R L-Advance preserves exact world, ordered tables, and all
||| iterator lifecycle outcomes across the complete current-R plan.
public export
0 retainedAdvancePreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LAdvance actor)) original =
    Just (tag, originalAfter)) ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (LAdvance actor))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live (LAdvance actor) originalAfter survivor
retainedAdvancePreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
  actor original survivor boundary tag checked retained =
    retainedLifecyclePreservesNoEpisodeBoundary nameEq keyEq registered ordinal
      live (LAdvance actor) Refl NonInsertAdvance tag
      (advanceOneDeleteRuntimeCommute nameEq keyEq actor) original survivor
      boundary checked retained

||| Retained non-R L-Divert preserves the exact stale-target control transition
||| across the complete current-R plan.
public export
0 retainedDivertPreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LDivert actor)) original =
    Just (tag, originalAfter)) ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (LDivert actor))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live (LDivert actor) originalAfter survivor
retainedDivertPreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
  actor original survivor boundary tag checked retained =
    retainedLifecyclePreservesNoEpisodeBoundary nameEq keyEq registered ordinal
      live (LDivert actor) Refl NonInsertDivert tag
      (divertOneDeleteRuntimeCommute nameEq keyEq actor) original survivor boundary
      checked retained

||| Retained non-R L-Leave preserves the exact stale-target control transition
||| across the complete current-R plan.
public export
0 retainedLeavePreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LLeave actor)) original =
    Just (tag, originalAfter)) ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (LLeave actor))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live (LLeave actor) originalAfter survivor
retainedLeavePreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
  actor original survivor boundary tag checked retained =
    retainedLifecyclePreservesNoEpisodeBoundary nameEq keyEq registered ordinal
      live (LLeave actor) Refl NonInsertLeave tag
      (leaveOneDeleteRuntimeCommute nameEq keyEq actor) original survivor boundary
      checked retained

||| Retained non-R L-Unload applies the same normalized accumulator to both
||| states and preserves its exact recovered world/table and Inactive control.
public export
0 retainedUnloadPreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LUnload actor)) original =
    Just (tag, originalAfter)) ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (LUnload actor))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live (LUnload actor) originalAfter survivor
retainedUnloadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
  actor original survivor boundary tag checked retained =
    retainedLifecyclePreservesNoEpisodeBoundary nameEq keyEq registered ordinal
      live (LUnload actor) Refl NonInsertUnload tag
      (unloadOneDeleteRuntimeCommute nameEq keyEq actor) original survivor boundary
      checked retained

||| Exhaustive dispatcher for the five retained lifecycle forms.
public export
0 retainedLifecycleHeadPreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
    action originalAfter survivor
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (OInsert actor parent component) Refl original survivor boundary tag
  checked retained impossible
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (ORetire actor) Refl original survivor boundary tag checked retained
  impossible
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (ORemove actor) Refl original survivor boundary tag checked retained
  impossible
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (LBegin actor) lifecycle original survivor boundary tag checked retained =
    retainedBeginPreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
      actor original survivor boundary tag checked retained
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (LAdvance actor) lifecycle original survivor boundary tag checked retained =
    retainedAdvancePreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
      actor original survivor boundary tag checked retained
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (LDivert actor) lifecycle original survivor boundary tag checked retained =
    retainedDivertPreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
      actor original survivor boundary tag checked retained
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (LLeave actor) lifecycle original survivor boundary tag checked retained =
    retainedLeavePreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
      actor original survivor boundary tag checked retained
retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal
  live (LUnload actor) lifecycle original survivor boundary tag checked retained =
    retainedUnloadPreservesNoEpisodeBoundary nameEq keyEq registered ordinal live
      actor original survivor boundary tag checked retained

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

public export
record InsertRuntimeObservation
  (name, key, world, error : Type) (value : key -> Type)
  (actor : name) (component : Component key value world error)
  (parent : Parent name) (ambient : world)
  (source : Registry name key value world error)
  (tag : RuleTag) (afterState : SystemState name key value world error) where
  constructor MkInsertRuntimeObservation
  0 insertObservedWorld : worldState afterState = ambient
  0 insertObservedBindings : bindings (registry afterState) =
    Bind actor (freshFiber component parent) :: bindings source

public export
0 insertRuntimeObservation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (OInsert actor parent component))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  InsertRuntimeObservation name key world error value actor component parent
    ambient source tag afterState
insertRuntimeObservation nameEq keyEq actor parent component ambient source tag
  afterState raw = case insertSuccessView nameEq keyEq actor parent component
    ambient source tag afterState raw of
    MkInsertSuccessView absent => MkInsertRuntimeObservation Refl
      (insertBindingRuntimeBindings nameEq actor (freshFiber component parent)
        source absent)

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

||| Retained O-Insert creates a fresh non-R generation in both traces.  Owner
||| and parent exclusion commute the insertion through every current R leaf;
||| the new generation environment is proved complete using the strict retained
||| witness for the fresh birth stamp.
public export
0 retainedInsertPreservesNoEpisodeBoundary :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error)
      (OInsert inserted parent component)) original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq
    (OInsert inserted parent component) original rest ->
  Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error)
      (OInsert inserted parent component))) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered
    (putCurrentGeneration @{nameEq} inserted
      (MkRegistrationGeneration inserted ordinal) live)
    (OInsert inserted parent component) originalAfter survivor
retainedInsertPreservesNoEpisodeBoundary {name} {key} {world} {error} {value}
  protocol nameEq keyEq registered ordinal live inserted parent component
  original survivor
  (MkNoEpisodeReplayBoundary ambient source originalShape
    (MkCompleteCurrentRegisteredPlanResult
      oldPlan@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
      oldComplete)
    survivorAmbient survivorBindings unique sourceWellFormed survivorWellFormed)
  tag checked rest discipline retained = case originalShape of
    Refl =>
      let 0 originalRaw = checkedActionProjects nameEq keyEq
            (OInsert inserted parent component) (MkSystemState ambient source)
            originalAfter tag checked
          0 outside = retainedOrchestrationOutsidePlan protocol nameEq keyEq
            registered ordinal live unique (OInsert inserted parent component)
            Refl (MkSystemState ambient source) originalAfter tag originalRaw
            rest discipline retained
            (MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
          0 ownerOutside = orchestrationOwnerOutside outside
          0 planRawResult = orchestrationRawAfterInactivePlan nameEq keyEq
            (OInsert inserted parent component) Refl ambient source oldTarget
            oldInactive outside originalRaw
      in case insertSuccessView nameEq keyEq inserted parent component ambient
        source tag originalAfter originalRaw of
        MkInsertSuccessView originalAbsent => case planRawResult of
          MkRawActionResult planTag planAfter planRaw =>
            case insertRuntimeObservation nameEq keyEq inserted parent component
              ambient oldTarget planTag planAfter planRaw of
              MkInsertRuntimeObservation planWorld planBindings =>
                case insertFreshThroughInactivePlan nameEq inserted parent
                  component source oldTarget oldInactive outside originalAbsent of
                  MkInactivePlanPreservingUpdateCommute
                    (MkInactivePlanUpdateCommute nextTarget nextInactive
                      nextTargetBindings nextOutside) actorsSame =>
                    let 0 freshOutside : Not
                          (Elem (MkRegistrationGeneration inserted ordinal)
                            registered)
                        freshOutside member = retained ((MkRegistrationGeneration inserted ordinal) ** (Refl, member))
                        0 insertedOutsideCurrent :
                          ActorOutsideCurrentRegistered inserted registered live
                        insertedOutsideCurrent =
                          actorOutsideCurrentFromCompletePlan
                            (MkCurrentRegisteredPlanResult oldTarget oldInactive
                              oldOutside) oldComplete inserted ownerOutside
                        0 outsideBack : (observed : name) ->
                          ActorOutsideCurrentRegistered observed registered
                            (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live) ->
                          ActorOutsideCurrentRegistered observed registered live
                        outsideBack observed outsideCurrent selected generation
                          present member = outsideCurrent selected generation
                            (putPreservesOtherEntry nameEq inserted selected
                              (insertedOutsideCurrent selected generation present
                                member) (MkRegistrationGeneration inserted ordinal) generation live present) member
                        0 outsideNew : (observed : name) ->
                          ActorOutsideCurrentRegistered observed registered
                            (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live) ->
                          ActorOutsideDeletionPlan observed nextInactive
                        outsideNew observed outsideCurrent = nextOutside observed
                          (oldOutside observed
                            (outsideBack observed outsideCurrent))
                        nextPlan : CurrentRegisteredPlanResult name key world error
                          value nameEq registered (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live)
                          (insertBinding @{nameEq} inserted
                            (freshFiber component parent) source originalAbsent)
                        nextPlan = MkCurrentRegisteredPlanResult nextTarget
                          nextInactive outsideNew
                        0 nextComplete : CurrentRegisteredPlanComplete name key
                          world error value nameEq registered (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live) nextPlan
                        nextComplete selected generation present member =
                          replace {p = Elem selected} (sym actorsSame)
                            (oldComplete selected generation
                              (registeredEntryAfterPutComesFromOld nameEq inserted
                                (MkRegistrationGeneration inserted ordinal) registered freshOutside live selected
                                generation present member) member)
                    in case transportPlanActionToBoundary nameEq keyEq
                      (OInsert inserted parent component)
                      (MkSystemState ambient oldTarget) planAfter survivor
                      (boundaryPlanSnapshotMatchesSurvivor
                        (MkNoEpisodeReplayBoundary ambient source Refl
                          (MkCompleteCurrentRegisteredPlanResult
                            (MkCurrentRegisteredPlanResult oldTarget oldInactive
                              oldOutside) oldComplete)
                          survivorAmbient survivorBindings unique sourceWellFormed
                          survivorWellFormed))
                      planTag planRaw survivorWellFormed of
                      MkBoundaryActionTransport survivorAfter survivorRaw
                        afterSnapshots survivorAfterWellFormed named
                        namedAfterProof fired =>
                        let 0 survivorAmbientNext :
                              (worldState survivorAfter = ambient)
                            survivorAmbientNext = trans
                              (sym (cong snapshotWorld afterSnapshots)) planWorld
                            0 survivorBindingsNext :
                              (bindings (registry survivorAfter) =
                              bindings nextTarget)
                            survivorBindingsNext = trans
                              (sym (cong snapshotBindings afterSnapshots))
                              (trans planBindings (sym nextTargetBindings))
                            0 originalAfterWellFormed :
                              (registryWellFormed @{nameEq} @{keyEq}
                                (the (SystemState name key value world error)
                                  (MkSystemState ambient
                                    (insertBinding @{nameEq} inserted
                                      (freshFiber component parent) source
                                      originalAbsent))) = True)
                            originalAfterWellFormed = preservationTheoremProof
                              nameEq keyEq (OInsert inserted parent component)
                              (MkSystemState ambient source)
                              (MkSystemState ambient
                                (insertBinding @{nameEq} inserted
                                  (freshFiber component parent) source
                                  originalAbsent)) OInsertTag sourceWellFormed
                              originalRaw
                            0 nextUnique : GenerationEnvironmentNamesUnique
                              (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live)
                            nextUnique = advanceGenerationEnvironmentPreservesUnique
                              nameEq ordinal
                              (the (Action name key value world error)
                                (OInsert inserted parent component)) live unique
                            0 nextBoundary : NoEpisodeReplayBoundary name key
                              world error value nameEq keyEq registered (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live)
                              (MkSystemState ambient
                                (insertBinding @{nameEq} inserted
                                  (freshFiber component parent) source
                                  originalAbsent)) survivorAfter
                            nextBoundary = MkNoEpisodeReplayBoundary ambient
                              (insertBinding @{nameEq} inserted
                                (freshFiber component parent) source
                                originalAbsent) Refl
                              (MkCompleteCurrentRegisteredPlanResult nextPlan
                                nextComplete)
                              survivorAmbientNext survivorBindingsNext nextUnique
                              originalAfterWellFormed survivorAfterWellFormed
                            0 namedBoundary : NoEpisodeReplayBoundary name key
                              world error value nameEq keyEq registered (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live)
                              (MkSystemState ambient
                                (insertBinding @{nameEq} inserted
                                  (freshFiber component parent) source
                                  originalAbsent)) (namedAfter named)
                            namedBoundary = replace {p = \candidate =>
                              NoEpisodeReplayBoundary name key world error value
                                nameEq keyEq registered (putCurrentGeneration @{nameEq} inserted (MkRegistrationGeneration inserted ordinal) live)
                                (MkSystemState ambient
                                  (insertBinding @{nameEq} inserted
                                    (freshFiber component parent) source
                                    originalAbsent)) candidate}
                              (sym namedAfterProof) nextBoundary
                        in MkRetainedNoEpisodeBoundaryStep named fired
                          namedBoundary

||| Exhaustive retained orchestration boundary step.  Lifecycle actions are
||| intentionally left to the selected effect/control commutation layer.
public export
0 retainedOrchestrationPreservesNoEpisodeBoundary :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq action original rest ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
    action originalAfter survivor
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (OInsert inserted parent component) orchestration original survivor
  boundary tag checked rest discipline retained =
    retainedInsertPreservesNoEpisodeBoundary protocol nameEq keyEq registered
      ordinal live inserted parent component original survivor boundary tag
      checked rest discipline retained
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (ORetire actor) orchestration original survivor boundary tag
  checked rest discipline retained =
    retainedRetirePreservesNoEpisodeBoundary protocol nameEq keyEq registered
      ordinal live actor original survivor boundary tag checked rest discipline
      retained
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (ORemove actor) orchestration original survivor boundary tag
  checked rest discipline retained =
    retainedRemovePreservesNoEpisodeBoundary protocol nameEq keyEq registered
      ordinal live actor original survivor boundary tag checked rest discipline
      retained
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (LBegin actor) Refl original survivor boundary tag checked rest
  discipline retained impossible
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (LAdvance actor) Refl original survivor boundary tag checked rest
  discipline retained impossible
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (LDivert actor) Refl original survivor boundary tag checked rest
  discipline retained impossible
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (LLeave actor) Refl original survivor boundary tag checked rest
  discipline retained impossible
retainedOrchestrationPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live (LUnload actor) Refl original survivor boundary tag checked rest
  discipline retained impossible

||| Exhaustive retained-head boundary preservation used by the structural
||| no-selected-episode suffix induction.
public export
0 retainedSuffixHeadPreservesNoEpisodeBoundary :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq action original rest ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
    action originalAfter survivor
retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq keyEq registered
  ordinal live action original survivor boundary tag checked rest discipline
  retained with (isLifecycleAction action) proof kind
  retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq keyEq registered
    ordinal live action original survivor boundary tag checked rest discipline
    retained | True = retainedLifecycleHeadPreservesNoEpisodeBoundary nameEq
      keyEq registered ordinal live action kind original survivor boundary tag
      checked retained
  retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq keyEq registered
    ordinal live action original survivor boundary tag checked rest discipline
    retained | False = retainedOrchestrationPreservesNoEpisodeBoundary protocol
      nameEq keyEq registered ordinal live action kind original survivor boundary
      tag checked rest discipline retained
