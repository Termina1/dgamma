module DGamma.CP4DeletionPostCloseFold

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPostCloseDeleted
import DGamma.CP4DeletionPostCloseFinal
import DGamma.CP4DeletionPostCloseLifecycle
import DGamma.CP4DeletionPostCloseOrchestration
import DGamma.CP4DeletionPostCloseRemove
import DGamma.CP4DeletionPostCloseSelectedRetire
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionRelationalActionReplay
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSuffixFold
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 nothingNotJustPostFold : Nothing = Just item -> Void
nothingNotJustPostFold Refl impossible

0 insertPresentPostFold :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before -> Void
insertPresentPostFold nameEq keyEq selected parent component
  before@(MkSystemState ambient fibers) afterState tag raw
  (MkInactiveFiberAt oldComponent oldParent oldRetired oldTable oldOutcome found) =
    case foreignInsertPlanView nameEq keyEq selected parent component ambient
      fibers tag afterState raw of
      MkForeignInsertPlanView absent guards =>
        void (nothingNotJustPostFold (trans (sym absent) found))

0 beginFiberTagPostFold :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  (state, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  beginFiberAction @{nameEq} @{keyEq} selected fiber state =
    Just (tag, afterState) -> tag = LBeginTag
beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation
  with (fiberLifecycle fiber)
  beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation |
    Inactive Nothing with (targetFiber fiber (registry state))
    beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation |
      Inactive Nothing | Nothing = void (nothingNotJustPostFold equation)
    beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation |
      Inactive Nothing | Just view = case justInjective equation of Refl => Refl
  beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation |
    Inactive (Just failure) = void (nothingNotJustPostFold equation)
  beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation |
    Reloading remaining accumulator view = void (nothingNotJustPostFold equation)
  beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation |
    Active accumulator view = void (nothingNotJustPostFold equation)
  beginFiberTagPostFold nameEq keyEq selected fiber state afterState tag equation |
    Unloading accumulator view outcome = void (nothingNotJustPostFold equation)

0 beginSuccessTagPostFold :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (tag, afterState) -> tag = LBeginTag
beginSuccessTagPostFold nameEq keyEq selected
  (MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers)
  beginSuccessTagPostFold nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag equation | Nothing =
      void (nothingNotJustPostFold equation)
  beginSuccessTagPostFold nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag equation | Just fiber =
      beginFiberTagPostFold nameEq keyEq selected fiber
        (MkSystemState ambient fibers) afterState tag equation

0 prependPostCloseKept :
  {original, originalAfter, originalFinal,
    survivor : SystemState name key value world error} ->
  {rest : Transitions originalAfter originalFinal} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (transition : Transition original originalAfter) ->
  (retained : Not (GenerationOwnedActor nameEq registered ordinal live
    (transitionAction transition))) ->
  (named : NamedTransition name key world error value
    (transitionAction transition) survivor) ->
  fireNamed nameEq keyEq (transitionAction transition) survivor = Just named ->
  (folded : RelationalNoEpisodeSuffixReplayFold name key world error value nameEq
    keyEq registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal
      (transitionAction transition) live)
    rest (namedAfter named)) ->
  RelationalNoEpisodeSuffixReplayFold name key world error value nameEq keyEq
    registered ordinal live (MoreTransitions transition rest) survivor
prependPostCloseKept nameEq keyEq registered ordinal live transition retained
  named@(MkNamedTransition after namedTag namedTransition namedAction) fires
  folded =
    MkRelationalNoEpisodeSuffixReplayFold
      (relationalSuffixFinalOrdinal folded)
      (relationalSuffixFinalLive folded)
      (relationalSuffixFinalSurvivor folded)
      (GenerationTraceScanStep transition rest
        (relationalSuffixGenerationScan folded))
      (ReplayReadyKeep retained after namedTag namedTransition namedAction fires
        (relationalSuffixReplayReady folded))
      (ReplayEndsKeep retained namedTag namedTransition namedAction fires
        (relationalSuffixReplayReady folded) (relationalSuffixReadyEnds folded))
      (relationalSuffixFinalUnique folded)
      (relationalSuffixFinalBoundary folded)

0 prependPostCloseDeleted :
  {original, originalAfter, originalFinal :
    SystemState name key value world error} ->
  {rest : Transitions originalAfter originalFinal} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (transition : Transition original originalAfter) ->
  GenerationOwnedActor nameEq registered ordinal live
    (transitionAction transition) ->
  (survivor : SystemState name key value world error) ->
  (folded : RelationalNoEpisodeSuffixReplayFold name key world error value nameEq
    keyEq registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal
      (transitionAction transition) live) rest survivor) ->
  RelationalNoEpisodeSuffixReplayFold name key world error value nameEq keyEq
    registered ordinal live (MoreTransitions transition rest) survivor
prependPostCloseDeleted nameEq keyEq registered ordinal live transition
  deleted survivor folded =
    MkRelationalNoEpisodeSuffixReplayFold
      (relationalSuffixFinalOrdinal folded)
      (relationalSuffixFinalLive folded)
      (relationalSuffixFinalSurvivor folded)
      (GenerationTraceScanStep transition rest
        (relationalSuffixGenerationScan folded))
      (ReplayReadyDelete deleted (relationalSuffixReplayReady folded))
      (ReplayEndsDelete deleted (relationalSuffixReplayReady folded)
        (relationalSuffixReadyEnds folded))
      (relationalSuffixFinalUnique folded)
      (relationalSuffixFinalBoundary folded)

||| Structural suffix fold retaining the selected-static quotient exactly until
||| selected removal or a checked selected L-Begin discharges it. If neither
||| occurs, final no-failure discharges the clean endpoint.
public export
0 postCloseSuffixFold :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {globalFirst, globalLast : SystemState name key value world error} ->
  {original, finalState : SystemState name key value world error} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (global : Transitions globalFirst globalLast) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  RegisteredGenerationsBornBefore registered ordinal ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  (trace : Transitions original finalState) ->
  (survivor : SystemState name key value world error) ->
  PostCloseSelectedBoundary name key world error value nameEq keyEq selected
    registered ordinal live original survivor ->
  RegistrationDiscipline protocol nameEq trace ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq registered ordinal live trace ->
  noFailedFibers finalState = True ->
  RelationalNoEpisodeSuffixReplayFold name key world error value nameEq keyEq
    registered ordinal live trace survivor
postCloseSuffixFold protocol nameEq keyEq selected registered selectedOutside
  global noDependent ordinal live bornBefore unique stamped NoTransitions survivor
  boundary RegistrationDisciplineEnd AlignedEnd NoRegisteredEpisodeEnd noFailed =
    MkRelationalNoEpisodeSuffixReplayFold ordinal live survivor
      GenerationTraceScanEnd ReplayReadyEnd (ReplayEndsEnd Refl) unique
      (finalPostCloseGivesRelational nameEq keyEq selected registered live unique
        stamped selectedOutside _ survivor noFailed boundary)
postCloseSuffixFold {original} {finalState} protocol nameEq keyEq selected
  registered selectedOutside global noDependent ordinal live bornBefore unique
  stamped
  (MoreTransitions (Fired {afterState = afterState}
      nameEq keyEq action tag checked) rest)
  survivor boundary
  (RegistrationDisciplineStep _ _ stepDiscipline restDiscipline)
  (AlignedStep action tag checked rest alignedRest)
  (NoRegisteredEpisodeStep _ _ noBegin noRegisteredRest) noFailed
  with (decGenerationOwnedActor nameEq registered ordinal live action)
  postCloseSuffixFold protocol nameEq keyEq selected registered selectedOutside
    global noDependent ordinal live bornBefore unique stamped
    (MoreTransitions (Fired {afterState = afterState}
      nameEq keyEq action tag checked) rest) survivor boundary
    (RegistrationDisciplineStep _ _ stepDiscipline restDiscipline)
    (AlignedStep action tag checked rest alignedRest)
    (NoRegisteredEpisodeStep _ _ noBegin noRegisteredRest) noFailed |
    Yes deleted =
      let nextBoundary = deletedPostCloseStep nameEq keyEq selected registered
            ordinal live bornBefore unique action _ survivor boundary tag checked
            deleted noBegin
          nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
            action live unique
          nextStamped = advanceGenerationEnvironmentPreservesStamped nameEq
            ordinal action live stamped
          0 folded = postCloseSuffixFold protocol nameEq keyEq selected registered
            selectedOutside global noDependent (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (registeredGenerationsBornBeforeNext bornBefore) nextUnique
            nextStamped rest survivor nextBoundary restDiscipline alignedRest
            noRegisteredRest noFailed
      in prependPostCloseDeleted nameEq keyEq registered ordinal live
        (Fired nameEq keyEq action tag checked) deleted survivor folded
  postCloseSuffixFold protocol nameEq keyEq selected registered selectedOutside
    global noDependent ordinal live bornBefore unique stamped
    (MoreTransitions (Fired {afterState = afterState}
      nameEq keyEq action tag checked) rest) survivor boundary
    (RegistrationDisciplineStep _ _ stepDiscipline restDiscipline)
    (AlignedStep action tag checked rest alignedRest)
    (NoRegisteredEpisodeStep _ _ noBegin noRegisteredRest) noFailed |
    No retained with (decEq @{nameEq} (actionOwner action) selected)
    postCloseSuffixFold protocol nameEq keyEq selected registered selectedOutside
      global noDependent ordinal live bornBefore unique stamped
      (MoreTransitions (Fired {afterState = afterState}
      nameEq keyEq action tag checked) rest) survivor boundary
      (RegistrationDisciplineStep _ _ stepDiscipline restDiscipline)
      (AlignedStep action tag checked rest alignedRest)
      (NoRegisteredEpisodeStep _ _ noBegin noRegisteredRest) noFailed |
      No retained | No actorDistinct =
        let nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq
              ordinal action live unique
            nextStamped = advanceGenerationEnvironmentPreservesStamped nameEq
              ordinal action live stamped
            0 step : PostCloseOrchestrationStep name key world error value
              nameEq keyEq selected registered (S ordinal)
              (advanceGenerationEnvironment @{nameEq} ordinal action live)
              action afterState survivor
            step = case action of
              OInsert actor parent component =>
                retainedForeignPostCloseOrchestration protocol nameEq keyEq
                  selected registered ordinal live unique action Refl actorDistinct
                  _ _ _ survivor tag checked rest stepDiscipline retained noBegin
                  boundary
              ORetire actor => retainedForeignPostCloseOrchestration protocol
                nameEq keyEq selected registered ordinal live unique action Refl
                actorDistinct _ _ _ survivor tag checked rest stepDiscipline
                retained noBegin boundary
              ORemove actor => retainedForeignPostCloseOrchestration protocol
                nameEq keyEq selected registered ordinal live unique action Refl
                actorDistinct _ _ _ survivor tag checked rest stepDiscipline
                retained noBegin boundary
              LBegin actor => retainedForeignPostCloseLifecycle protocol nameEq
                keyEq selected registered ordinal live unique action Refl
                actorDistinct global noDependent _ _ _ survivor tag checked rest
                stepDiscipline retained noBegin boundary
              LAdvance actor => retainedForeignPostCloseLifecycle protocol nameEq
                keyEq selected registered ordinal live unique action Refl
                actorDistinct global noDependent _ _ _ survivor tag checked rest
                stepDiscipline retained noBegin boundary
              LDivert actor => retainedForeignPostCloseLifecycle protocol nameEq
                keyEq selected registered ordinal live unique action Refl
                actorDistinct global noDependent _ _ _ survivor tag checked rest
                stepDiscipline retained noBegin boundary
              LLeave actor => retainedForeignPostCloseLifecycle protocol nameEq
                keyEq selected registered ordinal live unique action Refl
                actorDistinct global noDependent _ _ _ survivor tag checked rest
                stepDiscipline retained noBegin boundary
              LUnload actor => retainedForeignPostCloseLifecycle protocol nameEq
                keyEq selected registered ordinal live unique action Refl
                actorDistinct global noDependent _ _ _ survivor tag checked rest
                stepDiscipline retained noBegin boundary
        in case step of
          MkPostCloseOrchestrationStep named fires nextBoundary =>
            let folded = postCloseSuffixFold protocol nameEq keyEq selected
                  registered selectedOutside global noDependent (S ordinal)
                  (advanceGenerationEnvironment @{nameEq} ordinal action live)
                  (registeredGenerationsBornBeforeNext bornBefore) nextUnique
                  nextStamped rest (namedAfter named) nextBoundary restDiscipline
                  alignedRest noRegisteredRest noFailed
            in prependPostCloseKept nameEq keyEq registered ordinal live
              (Fired nameEq keyEq action tag checked) retained named fires folded
    postCloseSuffixFold protocol nameEq keyEq selected registered selectedOutside
      global noDependent ordinal live bornBefore unique stamped
      (MoreTransitions (Fired {afterState = afterState}
      nameEq keyEq action tag checked) rest) survivor boundary
      (RegistrationDisciplineStep _ _ stepDiscipline restDiscipline)
      (AlignedStep action tag checked rest alignedRest)
      (NoRegisteredEpisodeStep _ _ noBegin noRegisteredRest) noFailed |
      No retained | Yes ownerSelected = case action of
        OInsert actor parent component => case ownerSelected of
          Refl => void (insertPresentPostFold nameEq keyEq selected parent component
            _ _ tag (checkedActionProjects nameEq keyEq
              (OInsert selected parent component) _ _ tag checked)
            (postCloseOriginalSelectedInactive nameEq selected registered live
              unique stamped selectedOutside _ survivor boundary))
        ORetire actor => case ownerSelected of
          Refl =>
            let raw = checkedActionProjects nameEq keyEq (ORetire selected)
                  original afterState tag checked
                tagIsRetire = retireSuccessTag nameEq keyEq selected original
                  afterState tag raw
            in case tagIsRetire of
              Refl => case retainedSelectedPostCloseRetire protocol nameEq keyEq
                selected registered ordinal live unique original afterState
                finalState survivor checked rest stepDiscipline retained noBegin
                boundary of
                MkPostCloseOrchestrationStep named fires nextBoundary =>
                  let retireAction : Action name key value world error
                      retireAction = ORetire selected
                      0 nextUnique : GenerationEnvironmentNamesUnique live
                      nextUnique = advanceGenerationEnvironmentPreservesUnique
                        nameEq ordinal retireAction live unique
                      0 nextStamped : GenerationEnvironmentStamped live
                      nextStamped = advanceGenerationEnvironmentPreservesStamped
                        nameEq ordinal retireAction live stamped
                      0 folded : RelationalNoEpisodeSuffixReplayFold name key
                        world error value nameEq keyEq registered (S ordinal)
                        live rest (namedAfter named)
                      folded = postCloseSuffixFold protocol nameEq keyEq selected
                        registered selectedOutside global noDependent (S ordinal)
                        live (registeredGenerationsBornBeforeNext bornBefore)
                        nextUnique nextStamped rest (namedAfter named) nextBoundary
                        restDiscipline alignedRest noRegisteredRest noFailed
                  in prependPostCloseKept nameEq keyEq registered ordinal live
                    (Fired nameEq keyEq (ORetire selected) ORetireTag checked)
                    retained named fires folded
        ORemove actor => case ownerSelected of
          Refl => case retainedSelectedPostCloseRemove protocol nameEq keyEq
            selected registered ordinal live unique _ _ _ survivor tag checked
            rest stepDiscipline retained boundary of
            MkRelationalRetainedNoEpisodeBoundaryStep named fires nextBoundary =>
              let 0 nextUnique : GenerationEnvironmentNamesUnique
                    (advanceGenerationEnvironment @{nameEq} ordinal
                      (the (Action name key value world error)
                        (ORemove selected)) live)
                  nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq
                    ordinal (the (Action name key value world error)
                        (ORemove selected)) live unique
                  0 folded : RelationalNoEpisodeSuffixReplayFold name key world
                    error value nameEq keyEq registered (S ordinal)
                    (advanceGenerationEnvironment @{nameEq} ordinal
                      (the (Action name key value world error)
                        (ORemove selected)) live) rest (namedAfter named)
                  folded = relationalNoEpisodeSuffixReplayFold protocol nameEq
                    keyEq (replayRelatedAction nameEq keyEq) registered (S ordinal)
                    (advanceGenerationEnvironment @{nameEq} ordinal
                      (the (Action name key value world error)
                        (ORemove selected)) live)
                    (registeredGenerationsBornBeforeNext bornBefore) nextUnique
                    rest (namedAfter named) nextBoundary restDiscipline alignedRest
                    noRegisteredRest
              in prependPostCloseKept nameEq keyEq registered ordinal live
                (Fired nameEq keyEq (ORemove selected) tag checked) retained named fires folded
        LBegin actor => case ownerSelected of
          Refl =>
            let raw = checkedActionProjects nameEq keyEq (LBegin selected)
                  original afterState tag checked
                tagIsBegin = beginSuccessTagPostFold nameEq keyEq selected
                  original afterState tag raw
            in case tagIsBegin of
              Refl =>
                let clean = selectedCleanInactiveBeforeBegin nameEq keyEq
                      selected original afterState checked
                    relational = cleanOriginalPostCloseGivesRelational nameEq
                      selected registered live unique stamped selectedOutside
                      original survivor boundary clean
                in relationalNoEpisodeSuffixReplayFold protocol nameEq keyEq
                  (replayRelatedAction nameEq keyEq) registered ordinal live
                  bornBefore unique
                  (MoreTransitions (Fired nameEq keyEq (LBegin selected)
                    LBeginTag checked) rest) survivor relational
                  (RegistrationDisciplineStep
                    (Fired nameEq keyEq (LBegin selected) LBeginTag checked) rest
                    stepDiscipline restDiscipline)
                  (AlignedStep (LBegin selected) LBeginTag checked rest
                    alignedRest)
                  (NoRegisteredEpisodeStep
                    (Fired nameEq keyEq (LBegin selected) LBeginTag checked) rest
                    noBegin noRegisteredRest)
        LAdvance actor => case ownerSelected of
          Refl => void (inactiveCannotAdvance nameEq keyEq selected _ _ tag
            (checkedActionProjects nameEq keyEq (LAdvance selected) _ _ tag
              checked)
            (postCloseOriginalSelectedInactive nameEq selected registered live
              unique stamped selectedOutside _ survivor boundary))
        LDivert actor => case ownerSelected of
          Refl => void (inactiveCannotDivert nameEq keyEq selected _ _ tag
            (checkedActionProjects nameEq keyEq (LDivert selected) _ _ tag
              checked)
            (postCloseOriginalSelectedInactive nameEq selected registered live
              unique stamped selectedOutside _ survivor boundary))
        LLeave actor => case ownerSelected of
          Refl => void (inactiveCannotLeave nameEq keyEq selected _ _ tag
            (checkedActionProjects nameEq keyEq (LLeave selected) _ _ tag checked)
            (postCloseOriginalSelectedInactive nameEq selected registered live
              unique stamped selectedOutside _ survivor boundary))
        LUnload actor => case ownerSelected of
          Refl => void (inactiveCannotUnload nameEq keyEq selected _ _ tag
            (checkedActionProjects nameEq keyEq (LUnload selected) _ _ tag checked)
            (postCloseOriginalSelectedInactive nameEq selected registered live
              unique stamped selectedOutside _ survivor boundary))
