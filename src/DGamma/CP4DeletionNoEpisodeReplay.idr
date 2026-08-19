module DGamma.CP4DeletionNoEpisodeReplay

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControl
import DGamma.CP4DeletionControlBegin
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionControlOrchestration
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionReadiness
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionRetainedAction
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total

||| Iterated Inactive-leaf deletion preserves Definition-58 validity at the
||| exact plan target.  This is the source certificate needed to turn a raw
||| commuting frame back into a checked retained transition.
public export
0 inactivePlanPreservesWellFormed :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (the (SystemState name key value world error)
      (MkSystemState ambient source)) = True ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (the (SystemState name key value world error)
      (MkSystemState ambient target)) = True
inactivePlanPreservesWellFormed nameEq keyEq ambient source source
  NoInactiveLeafDeletion sourceWellFormed = sourceWellFormed
inactivePlanPreservesWellFormed nameEq keyEq ambient source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) sourceWellFormed =
      inactivePlanPreservesWellFormed nameEq keyEq ambient
        (deleteBinding @{nameEq} removed source) target rest
        (registryWellFormedInactiveDelete nameEq keyEq ambient removed component
          parent retiredFlag table outcome source found noChild sourceWellFormed)

||| Raw, action-indexed counterpart of the older `TransitionResult` plan fold.
||| Retaining the action index is what allows `fireNamed` readiness to consume
||| the result without an extra proof-irrelevance assumption.
public export
0 lifecycleRawAfterInactivePlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  ActorOutsideDeletionPlan (actionOwner action) plan ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (the (SystemState name key value world error)
      (MkSystemState ambient source)) = True ->
  {originalAfter : SystemState name key value world error} ->
  {originalTag : RuleTag} ->
  applyAction @{nameEq} @{keyEq} action (MkSystemState ambient source) =
    Just (originalTag, originalAfter) ->
  RawActionResult name key world error value nameEq keyEq action
    (MkSystemState ambient target)
lifecycleRawAfterInactivePlan nameEq keyEq action lifecycle ambient source source
  NoInactiveLeafDeletion ActorOutsideDeletionEnd sourceWellFormed raw =
    MkRawActionResult _ _ raw
lifecycleRawAfterInactivePlan nameEq keyEq action lifecycle ambient source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (ActorOutsideDeletionStep rest distinct outsideRest) sourceWellFormed raw =
    let replay = lifecycleApplicableAfterInactiveDelete nameEq keyEq action
          lifecycle removed distinct ambient source component parent retiredFlag
          table outcome found sourceWellFormed raw
        nextWellFormed = registryWellFormedInactiveDelete nameEq keyEq ambient
          removed component parent retiredFlag table outcome source found noChild
          sourceWellFormed
    in case replay of
      MkRawActionResult replayTag replayAfter replayRaw =>
        lifecycleRawAfterInactivePlan nameEq keyEq action lifecycle ambient
          (deleteBinding @{nameEq} removed source) target rest outsideRest
          nextWellFormed replayRaw

public export
0 orchestrationRawAfterInactivePlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (ambient : world) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  OrchestrationOutsideDeletionPlan action plan ->
  {originalAfter : SystemState name key value world error} ->
  {originalTag : RuleTag} ->
  applyAction @{nameEq} @{keyEq} action (MkSystemState ambient source) =
    Just (originalTag, originalAfter) ->
  RawActionResult name key world error value nameEq keyEq action
    (MkSystemState ambient target)
orchestrationRawAfterInactivePlan nameEq keyEq action orchestration ambient source
  source NoInactiveLeafDeletion OrchestrationOutsideDeletionEnd raw =
    MkRawActionResult _ _ raw
orchestrationRawAfterInactivePlan nameEq keyEq action orchestration ambient source
  target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest)
  (OrchestrationOutsideDeletionStep rest ownerOutside parentOutside outsideRest)
  raw =
    case orchestrationApplicableAfterInactiveDelete nameEq keyEq action
      orchestration removed ownerOutside parentOutside ambient source raw of
      MkRawActionResult replayTag replayAfter replayRaw =>
        orchestrationRawAfterInactivePlan nameEq keyEq action orchestration
          ambient (deleteBinding @{nameEq} removed source) target rest outsideRest
          replayRaw

0 rawResultGivesRetainedReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalMiddle, originalFinal :
    SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (source : SystemState name key value world error) ->
  registryWellFormed @{nameEq} @{keyEq} source = True ->
  (originalTransition : Transition originalFirst originalMiddle) ->
  (originalRest : Transitions originalMiddle originalFinal) ->
  transitionAction originalTransition = action ->
  RawActionResult name key world error value nameEq keyEq action source ->
  RetainedGenerationReplayStep name key world error value nameEq keyEq
    {survivingFirst = source} originalTransition originalRest
rawResultGivesRetainedReplay {name} {key} {world} {error} {value}
  nameEq keyEq action source sourceWellFormed originalTransition originalRest
  sameAction rawResult =
    let transported : RawActionResult name key world error value nameEq keyEq
          (transitionAction originalTransition) source
        transported = replace
          {p = \observed => RawActionResult name key world error value nameEq
            keyEq observed source}
          (sym sameAction) rawResult
    in case transported of
      MkRawActionResult tag afterState raw =>
        let 0 targetWellFormed = preservationTheoremProof nameEq keyEq
              (transitionAction originalTransition) source afterState tag
              sourceWellFormed raw
            0 checked : (checkedApplyAction @{nameEq} @{keyEq}
              (transitionAction originalTransition) source =
              Just (tag, afterState))
            checked = rewrite raw in rewrite targetWellFormed in Refl
            transition : Transition source afterState
            transition = Fired nameEq keyEq
              (transitionAction originalTransition) tag checked
            named : NamedTransition name key world error value
              (transitionAction originalTransition) source
            named = MkNamedTransition afterState tag transition Refl
            0 fired : fireNamed nameEq keyEq
              (transitionAction originalTransition) source = Just named
            fired = rewrite checked in Refl
        in MkRetainedGenerationReplayStep named fired

0 lifecycleActionNonInsert :
  (action : Action name key value world error) ->
  isLifecycleAction action = True -> NonInsertAction action
lifecycleActionNonInsert (OInsert inserted parent component) lifecycle impossible
lifecycleActionNonInsert (ORetire actor) lifecycle impossible
lifecycleActionNonInsert (ORemove actor) lifecycle impossible
lifecycleActionNonInsert (LBegin actor) lifecycle = NonInsertBegin
lifecycleActionNonInsert (LAdvance actor) lifecycle = NonInsertAdvance
lifecycleActionNonInsert (LDivert actor) lifecycle = NonInsertDivert
lifecycleActionNonInsert (LLeave actor) lifecycle = NonInsertLeave
lifecycleActionNonInsert (LUnload actor) lifecycle = NonInsertUnload

||| Complete retained-head frame for a segment with no selected-episode
||| quotient: the survivor source is exactly the current-R plan target.  It
||| covers all lifecycle and orchestration actions and consumes the precise
||| complement of generation deletion required by the suffix readiness
||| induction.
public export
0 retainedSuffixHeadAfterCurrentPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (action : Action name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (planResult : CurrentRegisteredPlanResult name key world error value nameEq
    registered live source) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (originalTag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action
    (MkSystemState ambient source) = Just (originalTag, originalAfter)) ->
  (originalRest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq action
    (MkSystemState ambient source) originalRest ->
  Not (GenerationOwnedActor nameEq registered ordinal live action) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (the (SystemState name key value world error)
      (MkSystemState ambient source)) = True ->
  RetainedGenerationReplayStep name key world error value nameEq keyEq
    {originalFirst = MkSystemState ambient source}
    {originalMiddle = originalAfter} {originalFinal = originalFinal}
    {survivingFirst = MkSystemState ambient (planTarget planResult)}
    (Fired nameEq keyEq action originalTag checked) originalRest
retainedSuffixHeadAfterCurrentPlan protocol nameEq keyEq registered ordinal live
  unique action ambient source planResult originalTag checked originalRest
  discipline retained sourceWellFormed with (isLifecycleAction action) proof kind
  retainedSuffixHeadAfterCurrentPlan protocol nameEq keyEq registered ordinal live
    unique action ambient source planResult originalTag checked originalRest
    discipline retained sourceWellFormed | True =
      let nonInsert = lifecycleActionNonInsert action kind
          strongOutside = retainedNonInsertOutsideCurrentRegistered nameEq
            registered ordinal live unique action nonInsert retained
          outside = actorOutsidePlan planResult (actionOwner action) strongOutside
          raw = checkedActionProjects nameEq keyEq action
            (MkSystemState ambient source) originalAfter originalTag checked
          replayRaw = lifecycleRawAfterInactivePlan nameEq keyEq action kind
            ambient source (planTarget planResult) (inactiveLeafPlan planResult)
            outside sourceWellFormed raw
          targetWellFormed = inactivePlanPreservesWellFormed nameEq keyEq ambient
            source (planTarget planResult) (inactiveLeafPlan planResult)
            sourceWellFormed
      in rawResultGivesRetainedReplay nameEq keyEq action
        (MkSystemState ambient (planTarget planResult)) targetWellFormed
        (Fired nameEq keyEq action originalTag checked) originalRest Refl replayRaw
  retainedSuffixHeadAfterCurrentPlan protocol nameEq keyEq registered ordinal live
    unique action ambient source planResult originalTag checked originalRest
    discipline retained sourceWellFormed | False =
      let outside = retainedOrchestrationOutsidePlan protocol nameEq keyEq
            registered ordinal live unique action kind
            (MkSystemState ambient source) originalAfter originalTag
            (checkedActionProjects nameEq keyEq action
              (MkSystemState ambient source) originalAfter originalTag checked)
            originalRest discipline retained planResult
          replayRaw = orchestrationRawAfterInactivePlan nameEq keyEq action kind
            ambient source (planTarget planResult) (inactiveLeafPlan planResult)
            outside (checkedActionProjects nameEq keyEq action
              (MkSystemState ambient source) originalAfter originalTag checked)
          targetWellFormed = inactivePlanPreservesWellFormed nameEq keyEq ambient
            source (planTarget planResult) (inactiveLeafPlan planResult)
            sourceWellFormed
      in rawResultGivesRetainedReplay nameEq keyEq action
        (MkSystemState ambient (planTarget planResult)) targetWellFormed
        (Fired nameEq keyEq action originalTag checked) originalRest Refl replayRaw

||| Exact no-selected-episode boundary relation at the host-observable runtime
||| representation.  The survivor has the plan target's ambient state and exact
||| ordered binding list.  It does not demand equality of the erased
||| `UniqueKeys` witness, which would amount to an unavailable proof-irrelevance
||| axiom.  Both source validity facts are carried explicitly for checked replay.
public export
record NoEpisodeReplayBoundary
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (registered : List (RegistrationGeneration name))
  (live : GenerationEnvironment name)
  (original, survivor : SystemState name key value world error) where
  constructor MkNoEpisodeReplayBoundary
  boundaryAmbient : world
  boundaryRegistry : Registry name key value world error
  0 originalBoundaryShape : original =
    MkSystemState boundaryAmbient boundaryRegistry
  boundaryCompletePlan : CompleteCurrentRegisteredPlanResult name key world error
    value nameEq registered live boundaryRegistry
  0 survivorBoundaryAmbient : worldState survivor = boundaryAmbient
  0 survivorBoundaryBindings : bindings (registry survivor) =
    bindings (planTarget (completePlanResult boundaryCompletePlan))
  0 boundaryGenerationsUnique : GenerationEnvironmentNamesUnique live
  0 originalBoundaryWellFormed : registryWellFormed @{nameEq} @{keyEq}
    original = True
  0 survivorBoundaryWellFormed : registryWellFormed @{nameEq} @{keyEq}
    survivor = True

||| Existing consumers use the ordinary plan projection; completeness remains
||| attached to the coherent boundary scaffold rather than threaded separately.
public export
boundaryPlan :
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  CurrentRegisteredPlanResult name key world error value nameEq registered live
    (boundaryRegistry boundary)
boundaryPlan boundary = completePlanResult (boundaryCompletePlan boundary)

public export
0 boundaryPlanComplete :
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  CurrentRegisteredPlanComplete name key world error value nameEq registered live
    (boundaryPlan boundary)
boundaryPlanComplete boundary = currentPlanComplete (boundaryCompletePlan boundary)

0 runtimeSnapshotPartsEqual :
  (leftWorld, rightWorld : world) ->
  (leftBindings, rightBindings :
    List (Binding name (FiberAt name key value world error))) ->
  leftWorld = rightWorld -> leftBindings = rightBindings ->
  the (RuntimeSnapshot name key world error value)
    (MkRuntimeSnapshot leftWorld leftBindings) =
  the (RuntimeSnapshot name key world error value)
    (MkRuntimeSnapshot rightWorld rightBindings)
runtimeSnapshotPartsEqual leftWorld leftWorld leftBindings leftBindings Refl
  Refl = Refl

public export
0 boundaryPlanSnapshotMatchesSurvivor :
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  runtimeSnapshot
    (MkSystemState (boundaryAmbient boundary)
      (planTarget (boundaryPlan boundary))) =
  runtimeSnapshot survivor
boundaryPlanSnapshotMatchesSurvivor {survivor}
  (MkNoEpisodeReplayBoundary ambient source originalShape completePlan
    survivorAmbient survivorBindings unique originalWellFormed
    survivorWellFormed) =
      runtimeSnapshotPartsEqual ambient (worldState survivor)
        (bindings (planTarget (completePlanResult completePlan)))
        (bindings (registry survivor)) (sym survivorAmbient)
        (sym survivorBindings)

public export
0 namedFireProjectsRaw :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (source : SystemState name key value world error) ->
  (named : NamedTransition name key world error value action source) ->
  fireNamed nameEq keyEq action source = Just named ->
  applyAction @{nameEq} @{keyEq} action source =
    Just (namedTag named, namedAfter named)
namedFireProjectsRaw nameEq keyEq action source named fired
  with (checkedApplyAction @{nameEq} @{keyEq} action source) proof checked
  namedFireProjectsRaw nameEq keyEq action source named fired | Nothing =
    void (nothingIsNotJust fired)
  namedFireProjectsRaw nameEq keyEq action source named fired |
    Just (tag, afterState) =
      case justInjective fired of
        Refl => checkedActionProjects nameEq keyEq action source afterState tag
          checked

||| Instantiate the suffix retained-head interface at one exact boundary.
||| Unlike `TransitionResult`, the result remains indexed by the original action
||| and therefore feeds `GenerationReplayReady` directly.
public export
0 retainedSuffixHeadAtBoundary :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  (action : Action name key value world error) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq action original rest ->
  (retained : Not
    (GenerationOwnedActor nameEq registered ordinal live action)) ->
  RetainedGenerationReplayStep name key world error value nameEq keyEq
    {originalFirst = original} {originalMiddle = originalAfter}
    {originalFinal = originalFinal} {survivingFirst = survivor}
    (Fired nameEq keyEq action tag checked) rest
retainedSuffixHeadAtBoundary {name} {key} {world} {error} {value}
  protocol nameEq keyEq registered ordinal live original survivor
  boundary@(MkNoEpisodeReplayBoundary ambient source originalShape
    completePlan@(MkCompleteCurrentRegisteredPlanResult plan planComplete)
    survivorAmbient survivorBindings unique sourceWellFormed survivorWellFormed)
  action tag checked rest discipline retained =
    case originalShape of
      Refl =>
        case retainedSuffixHeadAfterCurrentPlan protocol nameEq keyEq registered
          ordinal live unique action ambient source plan tag checked rest
          discipline retained sourceWellFormed of
          MkRetainedGenerationReplayStep planNamed planFired =>
            let planSource : SystemState name key value world error
                planSource = MkSystemState ambient (planTarget plan)
                planRaw : applyAction @{nameEq} @{keyEq} action planSource =
                  Just (namedTag planNamed, namedAfter planNamed)
                planRaw = namedFireProjectsRaw nameEq keyEq action planSource
                  planNamed planFired
                0 planSurvivorSame : runtimeSnapshot planSource =
                  runtimeSnapshot survivor
                planSurvivorSame = boundaryPlanSnapshotMatchesSurvivor
                  (MkNoEpisodeReplayBoundary ambient source Refl
                    (MkCompleteCurrentRegisteredPlanResult plan planComplete)
                    survivorAmbient survivorBindings unique sourceWellFormed
                    survivorWellFormed)
                0 transported : ActionRuntimeTransport name key world error
                  value nameEq keyEq action survivor (namedTag planNamed)
                  (namedAfter planNamed)
                transported =
                  transportApplyActionAcrossRuntimeSnapshot nameEq keyEq action
                    planSource survivor planSurvivorSame
                    (namedTag planNamed) (namedAfter planNamed) planRaw
            in case transported of
              MkActionRuntimeTransport replayAfter replayRaw replaySnapshot =>
                let 0 replayWellFormed = preservationTheoremProof nameEq keyEq
                      action survivor replayAfter (namedTag planNamed)
                      survivorWellFormed replayRaw
                    0 replayChecked : (checkedApplyAction @{nameEq} @{keyEq}
                      action survivor = Just (namedTag planNamed, replayAfter))
                    replayChecked = rewrite replayRaw in
                      rewrite replayWellFormed in Refl
                    replayTransition : Transition survivor replayAfter
                    replayTransition = Fired nameEq keyEq action
                      (namedTag planNamed) replayChecked
                    replayNamed : NamedTransition name key world error value
                      action survivor
                    replayNamed = MkNamedTransition replayAfter
                      (namedTag planNamed) replayTransition Refl
                    0 replayFired : fireNamed nameEq keyEq action survivor =
                      Just replayNamed
                    replayFired = rewrite replayChecked in Refl
                in MkRetainedGenerationReplayStep replayNamed replayFired
