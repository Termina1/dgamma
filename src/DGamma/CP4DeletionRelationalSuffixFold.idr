module DGamma.CP4DeletionRelationalSuffixFold

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSuffixFold
import Data.Nat
import Decidable.Equality

%default total

||| Ordered Equation-53 controls compose pointwise while retaining the exact
||| registry domain and provider-scan order.
public export
0 orderedControlsTransitive :
  OrderedRegistryControlsRelated name key world error value left middle ->
  OrderedRegistryControlsRelated name key world error value middle right ->
  OrderedRegistryControlsRelated name key world error value left right
orderedControlsTransitive OrderedControlsNil OrderedControlsNil =
  OrderedControlsNil
orderedControlsTransitive
  (OrderedControlsCons actor first firstRest)
  (OrderedControlsCons actor second secondRest) =
    OrderedControlsCons actor (fiberControlTransitive first second)
      (orderedControlsTransitive firstRest secondRest)

0 effectRelationsTransitive :
  EffectStateRelated keyEq first middle ->
  EffectStateRelated keyEq middle finalState ->
  EffectStateRelated keyEq first finalState
effectRelationsTransitive
  (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

||| A complete relational boundary still determines the former exact scaffold
||| between the original state and its own plan target.  This is the bridge that
||| lets the already-proved exact plan/head commutations be reused without
||| identifying the actual survivor with that target.
public export
0 relationalBoundaryGivesPlanExactBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (boundary : RelationalNoEpisodeReplayBoundary name key world error value
    nameEq keyEq registered live original survivor) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered live
    original
    (plannedSystemState original
      (completePlanResult (relationalCompletePlan boundary)))
relationalBoundaryGivesPlanExactBoundary nameEq keyEq unique
  (MkRelationalNoEpisodeReplayBoundary
    completePlan effects controls originalWellFormed survivorWellFormed) =
      let 0 plannedWellFormed = inactivePlanPreservesWellFormed nameEq keyEq
            (worldState original) (registry original)
            (planTarget (completePlanResult completePlan))
            (inactiveLeafPlan (completePlanResult completePlan))
            originalWellFormed
      in case original of
        MkSystemState ambient source =>
          MkNoEpisodeReplayBoundary ambient source Refl completePlan Refl Refl
            unique originalWellFormed plannedWellFormed

||| One action replayed from the plan-side source to an already-related
||| survivor.  This is the local operational-congruence result consumed by the
||| structural suffix fold.  Its eventual constructor is supplied by the
||| Definition-60 per-head effect/outcome frames; the fold itself does not hide
||| that remaining proof behind an escape hatch.
public export
record RelatedNamedActionReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (leftBefore, rightBefore : SystemState name key value world error)
  (leftNamed : NamedTransition name key world error value action leftBefore) where
  constructor MkRelatedNamedActionReplay
  relatedReplayNamed : NamedTransition name key world error value action
    rightBefore
  0 relatedReplayFires : fireNamed nameEq keyEq action rightBefore =
    Just relatedReplayNamed
  0 relatedReplayEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} (namedAfter leftNamed))
    (projectEffectState @{nameEq} (namedAfter relatedReplayNamed))
  0 relatedReplayControls : OrderedRegistryControlsRelated name key world error
    value (bindings (registry (namedAfter leftNamed)))
    (bindings (registry (namedAfter relatedReplayNamed)))
  0 relatedReplayWellFormed : registryWellFormed @{nameEq} @{keyEq}
    (namedAfter relatedReplayNamed) = True

||| Saturated local interface for the relational suffix.  It states precisely
||| the one still-independent obligation: an actual checked plan-side head can
||| be replayed from a state with equal observable effects and ordered related
||| controls.  All generation scanning, deletion-plan commutation, and boundary
||| threading are proved below.
public export
RelationalActionReplayer :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> Type
RelationalActionReplayer name key world error value nameEq keyEq =
  (action : Action name key value world error) ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value action leftBefore) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} leftBefore)
    (projectEffectState @{nameEq} rightBefore) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry leftBefore)) (bindings (registry rightBefore)) ->
  registryWellFormed @{nameEq} @{keyEq} rightBefore = True ->
  RelatedNamedActionReplay name key world error value nameEq keyEq action
    leftBefore rightBefore leftNamed

||| Deleted R heads need no relational action replay: the exact commutation
||| updates the original/plan side while keeping the old plan target fixed, and
||| transitivity then reconnects that target to the actual survivor.
public export
0 deletedSuffixHeadPreservesRelationalBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  RegisteredGenerationsBornBefore registered ordinal ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : RelationalNoEpisodeReplayBoundary name key world error value
    nameEq keyEq registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (deleted : GenerationOwnedActor nameEq registered ordinal live action) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  RelationalNoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
    originalAfter survivor
deletedSuffixHeadPreservesRelationalBoundary nameEq keyEq registered ordinal live
  bornBefore unique action original survivor boundary tag checked deleted noBegin =
    let exactBefore = relationalBoundaryGivesPlanExactBoundary nameEq keyEq unique
          boundary
        exactAfter = deletedSuffixHeadPreservesNoEpisodeBoundary nameEq keyEq
          registered ordinal live bornBefore action original
          (plannedSystemState original
            (completePlanResult (relationalCompletePlan boundary)))
          exactBefore tag checked deleted noBegin
        bridge = exactBoundaryGivesRelational exactAfter
        0 nextEffects : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (plannedSystemState originalAfter
              (completePlanResult (relationalCompletePlan bridge))))
          (projectEffectState @{nameEq} survivor)
        nextEffects = effectRelationsTransitive
          (relationalEffects bridge) (relationalEffects boundary)
        0 nextControls : OrderedRegistryControlsRelated name key world error
          value
          (bindings (registry
            (plannedSystemState originalAfter
              (completePlanResult (relationalCompletePlan bridge)))))
          (bindings (registry survivor))
        nextControls = orderedControlsTransitive
          (relationalOrderedControls bridge)
          (relationalOrderedControls boundary)
    in MkRelationalNoEpisodeReplayBoundary
      (relationalCompletePlan bridge) nextEffects nextControls
      (relationalOriginalWellFormed bridge)
      (relationalSurvivorWellFormed boundary)

||| One retained suffix head and its next relational boundary.  This parallels
||| `RetainedNoEpisodeBoundaryStep` but deliberately keeps the survivor relation
||| rather than collapsing it to a runtime snapshot.
public export
record RelationalRetainedNoEpisodeBoundaryStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (registered : List (RegistrationGeneration name))
  (nextLive : GenerationEnvironment name)
  (action : Action name key value world error)
  (originalAfter, survivorBefore : SystemState name key value world error) where
  constructor MkRelationalRetainedNoEpisodeBoundaryStep
  relationalRetainedNamed : NamedTransition name key world error value action
    survivorBefore
  0 relationalRetainedFires : fireNamed nameEq keyEq action survivorBefore =
    Just relationalRetainedNamed
  0 relationalRetainedNextBoundary : RelationalNoEpisodeReplayBoundary name key
    world error value nameEq keyEq registered nextLive originalAfter
    (namedAfter relationalRetainedNamed)

||| Retained heads reuse the exact current-R plan commutation to obtain the
||| checked plan-side head, then invoke only the local relational action replay
||| interface.  The resulting relation is composed with the exact next-plan
||| bridge; no registry equality or proof irrelevance is requested.
public export
0 retainedSuffixHeadPreservesRelationalBoundary :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (replayAction : RelationalActionReplayer name key world error value nameEq
    keyEq) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : RelationalNoEpisodeReplayBoundary name key world error value
    nameEq keyEq registered live original survivor) ->
  {originalAfter, originalFinal : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq action original rest ->
  (retained : Not
    (GenerationOwnedActor nameEq registered ordinal live action)) ->
  RelationalRetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
    action originalAfter survivor
retainedSuffixHeadPreservesRelationalBoundary protocol nameEq keyEq replayAction
  registered ordinal live unique action original survivor boundary tag checked
  rest discipline retained =
    let exactBefore = relationalBoundaryGivesPlanExactBoundary nameEq keyEq unique
          boundary
        exactStep = retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq
          keyEq registered ordinal live action original
          (plannedSystemState original
            (completePlanResult (relationalCompletePlan boundary)))
          exactBefore tag checked rest discipline retained
    in case replayAction action
      (plannedSystemState original
        (completePlanResult (relationalCompletePlan boundary)))
      survivor (retainedBoundaryNamed exactStep)
      (relationalEffects boundary) (relationalOrderedControls boundary)
      (relationalSurvivorWellFormed boundary) of
      replay@(MkRelatedNamedActionReplay survivorNamed survivorFires
        replayEffects replayControls survivorAfterWellFormed) =>
          let bridge = exactBoundaryGivesRelational
                (retainedNextBoundary exactStep)
              0 nextEffects : EffectStateRelated keyEq
                (projectEffectState @{nameEq}
                  (plannedSystemState originalAfter
                    (completePlanResult (relationalCompletePlan bridge))))
                (projectEffectState @{nameEq} (namedAfter survivorNamed))
              nextEffects = effectRelationsTransitive
                (relationalEffects bridge) replayEffects
              0 nextControls : OrderedRegistryControlsRelated name key world
                error value
                (bindings (registry
                  (plannedSystemState originalAfter
                    (completePlanResult (relationalCompletePlan bridge)))))
                (bindings (registry (namedAfter survivorNamed)))
              nextControls = orderedControlsTransitive
                (relationalOrderedControls bridge) replayControls
              0 nextBoundary : RelationalNoEpisodeReplayBoundary name key world
                error value nameEq keyEq registered
                (advanceGenerationEnvironment @{nameEq} ordinal action live)
                originalAfter (namedAfter survivorNamed)
              nextBoundary = MkRelationalNoEpisodeReplayBoundary
                (relationalCompletePlan bridge) nextEffects nextControls
                (relationalOriginalWellFormed bridge) survivorAfterWellFormed
          in MkRelationalRetainedNoEpisodeBoundaryStep survivorNamed
            survivorFires nextBoundary

||| Relational counterpart of `NoEpisodeSuffixReplayFold`.  Besides the same
||| dependent generation scan and executable replay readiness, it returns the
||| final ordered effect/control boundary and the final live-name uniqueness
||| certificate needed by subsequent endpoint assembly.
public export
record RelationalNoEpisodeSuffixReplayFold
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {originalFirst, originalFinal : SystemState name key value world error}
  (original : Transitions originalFirst originalFinal)
  (survivingFirst : SystemState name key value world error) where
  constructor MkRelationalNoEpisodeSuffixReplayFold
  relationalSuffixFinalOrdinal : Nat
  relationalSuffixFinalLive : GenerationEnvironment name
  relationalSuffixFinalSurvivor : SystemState name key value world error
  0 relationalSuffixGenerationScan : GenerationTraceScan nameEq ordinal live
    original relationalSuffixFinalOrdinal relationalSuffixFinalLive
  0 relationalSuffixReplayReady : GenerationReplayReady nameEq keyEq
    (GenerationOwnedActor nameEq registered) ordinal live original survivingFirst
  0 relationalSuffixFinalUnique : GenerationEnvironmentNamesUnique
    relationalSuffixFinalLive
  0 relationalSuffixFinalBoundary : RelationalNoEpisodeReplayBoundary name key
    world error value nameEq keyEq registered relationalSuffixFinalLive
    originalFinal relationalSuffixFinalSurvivor

||| Structural relational whole-suffix fold.  Deleted exact-R heads are handled
||| constructively above; retained heads use the saturated per-action relational
||| replay interface and then recurse from its concrete checked survivor.
public export
0 relationalNoEpisodeSuffixReplayFold :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (replayAction : RelationalActionReplayer name key world error value nameEq
    keyEq) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  RegisteredGenerationsBornBefore registered ordinal ->
  GenerationEnvironmentNamesUnique live ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  RelationalNoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live originalFirst survivingFirst ->
  RegistrationDiscipline protocol nameEq original ->
  AlignedTransitions name key world error value nameEq keyEq original ->
  NoRegisteredEpisode nameEq registered ordinal live original ->
  RelationalNoEpisodeSuffixReplayFold name key world error value nameEq keyEq
    registered ordinal live original survivingFirst
relationalNoEpisodeSuffixReplayFold protocol nameEq keyEq replayAction registered
  ordinal live bornBefore unique NoTransitions survivingFirst boundary
  RegistrationDisciplineEnd AlignedEnd NoRegisteredEpisodeEnd =
    MkRelationalNoEpisodeSuffixReplayFold ordinal live survivingFirst
      GenerationTraceScanEnd ReplayReadyEnd unique boundary
relationalNoEpisodeSuffixReplayFold protocol nameEq keyEq replayAction registered
  ordinal live bornBefore unique
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  survivingFirst boundary
  (RegistrationDisciplineStep
    (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
  (AlignedStep action tag checked rest alignedRest)
  (NoRegisteredEpisodeStep
    (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest)
  with (decGenerationOwnedActor nameEq registered ordinal live action)
  relationalNoEpisodeSuffixReplayFold protocol nameEq keyEq replayAction
    registered ordinal live bornBefore unique
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
    survivingFirst boundary
    (RegistrationDisciplineStep
      (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
    (AlignedStep action tag checked rest alignedRest)
    (NoRegisteredEpisodeStep
      (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest) |
    Yes deleted =
      let 0 nextBoundary = deletedSuffixHeadPreservesRelationalBoundary nameEq
            keyEq registered ordinal live bornBefore unique action _
            survivingFirst boundary tag checked deleted noBegin
          0 folded = relationalNoEpisodeSuffixReplayFold protocol nameEq keyEq
            replayAction registered (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (registeredGenerationsBornBeforeNext bornBefore)
            (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action
              live unique)
            rest survivingFirst nextBoundary restDiscipline alignedRest
            noRegisteredRest
      in MkRelationalNoEpisodeSuffixReplayFold
        (relationalSuffixFinalOrdinal folded)
        (relationalSuffixFinalLive folded)
        (relationalSuffixFinalSurvivor folded)
        (GenerationTraceScanStep
          (Fired nameEq keyEq action tag checked) rest
          (relationalSuffixGenerationScan folded))
        (ReplayReadyDelete deleted (relationalSuffixReplayReady folded))
        (relationalSuffixFinalUnique folded)
        (relationalSuffixFinalBoundary folded)
  relationalNoEpisodeSuffixReplayFold protocol nameEq keyEq replayAction
    registered ordinal live bornBefore unique
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
    survivingFirst boundary
    (RegistrationDisciplineStep
      (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
    (AlignedStep action tag checked rest alignedRest)
    (NoRegisteredEpisodeStep
      (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest) |
    No retained =
      case retainedSuffixHeadPreservesRelationalBoundary protocol nameEq keyEq
        replayAction registered ordinal live unique action _ survivingFirst
        boundary tag checked rest stepDiscipline retained of
        MkRelationalRetainedNoEpisodeBoundaryStep
          named@(MkNamedTransition survivingAfter survivingTag
            survivingTransition sameAction) fired nextBoundary =>
              let 0 folded = relationalNoEpisodeSuffixReplayFold protocol nameEq
                    keyEq replayAction registered (S ordinal)
                    (advanceGenerationEnvironment @{nameEq} ordinal action live)
                    (registeredGenerationsBornBeforeNext bornBefore)
                    (advanceGenerationEnvironmentPreservesUnique nameEq ordinal
                      action live unique)
                    rest survivingAfter nextBoundary restDiscipline alignedRest
                    noRegisteredRest
              in MkRelationalNoEpisodeSuffixReplayFold
                (relationalSuffixFinalOrdinal folded)
                (relationalSuffixFinalLive folded)
                (relationalSuffixFinalSurvivor folded)
                (GenerationTraceScanStep
                  (Fired nameEq keyEq action tag checked) rest
                  (relationalSuffixGenerationScan folded))
                (ReplayReadyKeep retained survivingAfter survivingTag
                  survivingTransition sameAction fired
                  (relationalSuffixReplayReady folded))
                (relationalSuffixFinalUnique folded)
                (relationalSuffixFinalBoundary folded)
