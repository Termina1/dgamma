module DGamma.CP4DeletionTheorem

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Ordering
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionEndpoint
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPostCloseFold
import DGamma.CP4DeletionPremiseSplit
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedEpisodeFold
import DGamma.CP4DeletionSkeleton
import DGamma.CP4DeletionWithdrawalJoin
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 disciplineAppendRight :
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  RegistrationDiscipline protocol nameEq (appendTransitions left right) ->
  RegistrationDiscipline protocol nameEq right
disciplineAppendRight NoTransitions right discipline = discipline
disciplineAppendRight (MoreTransitions transition rest) right
  (RegistrationDisciplineStep _ _ step tail) =
    disciplineAppendRight rest right tail

0 generationScanEndpointsUnique :
  GenerationTraceScan nameEq ordinal live trace firstOrdinal firstLive ->
  GenerationTraceScan nameEq ordinal live trace secondOrdinal secondLive ->
  (firstOrdinal = secondOrdinal, firstLive = secondLive)
generationScanEndpointsUnique GenerationTraceScanEnd GenerationTraceScanEnd =
  (Refl, Refl)
generationScanEndpointsUnique
  (GenerationTraceScanStep transition rest firstTail)
  (GenerationTraceScanStep _ _ secondTail) =
    generationScanEndpointsUnique firstTail secondTail

0 transportPostCloseBoundary :
  firstOrdinal = secondOrdinal -> firstLive = secondLive ->
  PostCloseSelectedBoundary name key world error value nameEq keyEq selected
    registered firstOrdinal firstLive original survivor ->
  PostCloseSelectedBoundary name key world error value nameEq keyEq selected
    registered secondOrdinal secondLive original survivor
transportPostCloseBoundary Refl Refl boundary = boundary

0 transportGenerationFilterSource :
  first = second ->
  GenerationFilterResult name key world error value nameEq deletable ordinal live
    original first ->
  GenerationFilterResult name key world error value nameEq deletable ordinal live
    original second
transportGenerationFilterSource Refl result = result

0 transportGenerationFilterFinal :
  (same : first = second) ->
  (result : GenerationFilterResult name key world error value nameEq deletable
    ordinal live original first) ->
  GenerationFilterResult.survivingFinal
      (transportGenerationFilterSource same result) =
    GenerationFilterResult.survivingFinal result
transportGenerationFilterFinal Refl result = Refl

record ReadyGenerationResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type)
  (ordinal : Nat) (live : GenerationEnvironment name)
  {originalFirst, originalFinal : SystemState name key value world error}
  (original : Transitions originalFirst originalFinal)
  (survivingFirst, target : SystemState name key value world error) where
  constructor MkReadyGenerationResult
  readyGenerationResult : GenerationFilterResult name key world error value
    nameEq deletable ordinal live original survivingFirst
  0 readyGenerationFinal : GenerationFilterResult.survivingFinal
    readyGenerationResult = target

0 replayReadyResultAt :
  (nameEq : DecEq name) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  (ready : GenerationReplayReady nameEq keyEq deletable ordinal live original
    survivingFirst) ->
  (ends : ReplayReadyEndsAt ready target) ->
  ReadyGenerationResult name key world error value nameEq deletable ordinal live
    original survivingFirst target
replayReadyResultAt nameEq deletable ordinal live NoTransitions survivingFirst
  ReplayReadyEnd (ReplayEndsEnd same) =
    MkReadyGenerationResult
      (MkGenerationFilterResult survivingFirst NoTransitions
        GenerationActionSubsequenceEnd) (sym same)
replayReadyResultAt nameEq deletable ordinal live
  (MoreTransitions transition@(Fired stepNameEq stepKeyEq action tag checked)
    rest) survivingFirst (ReplayReadyDelete deleted tail)
  (ReplayEndsDelete _ _ tailEnds) =
    case replayReadyResultAt nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal action live) rest
      survivingFirst tail tailEnds of
      MkReadyGenerationResult
        (MkGenerationFilterResult finalState surviving witness) finalSame =>
          MkReadyGenerationResult
            (MkGenerationFilterResult finalState surviving
              (DeleteGenerationAction (Fired stepNameEq stepKeyEq action tag checked) rest deleted witness))
            finalSame
replayReadyResultAt nameEq deletable ordinal live
  (MoreTransitions transition@(Fired stepNameEq stepKeyEq action ruleTag checked)
    rest) survivingFirst
  (ReplayReadyKeep retained after tag survivingTransition sameAction fires tail)
  (ReplayEndsKeep _ _ _ _ _ _ tailEnds) =
    case replayReadyResultAt nameEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal action live) rest after
      tail tailEnds of
      MkReadyGenerationResult
        (MkGenerationFilterResult finalState surviving witness) finalSame =>
          MkReadyGenerationResult
            (MkGenerationFilterResult finalState
              (MoreTransitions survivingTransition surviving)
              (KeepGenerationAction (Fired stepNameEq stepKeyEq action ruleTag checked) rest survivingTransition
                surviving retained (sym sameAction) witness))
            finalSame

||| Checked inhabitant of the public Lemma-72 type. The proof uses the selected
||| center fold, the post-close structural fold, the retirement/scanner join,
||| and the generic endpoint assembler; no semantic premise is added.
public export
0 deletionTheoremProof : deletionTheorem name key value world error
deletionTheoremProof nameEq keyEq protocol initial finalState global aligned
  discipline initialWF initialEmpty finalQuiet finalNoFailed componentsTotal
  independent selected episode registered selectedOutside episodeStartOrdinal
  episodeStartLive beforeScan registeredDuring noDependent noRegistered =
    let segments = splitLocatedNoRegisteredSegments nameEq keyEq global selected
          episode registered episodeStartOrdinal episodeStartLive beforeScan
          noRegistered
        0 selectedFold = selectedClosedEpisodeFoldFromPremises protocol nameEq
          keyEq initial finalState global aligned discipline initialWF initialEmpty
          independent selected episode registered selectedOutside
          episodeStartOrdinal episodeStartLive beforeScan registeredDuring
          noDependent noRegistered
        0 centerEndpointSame = generationScanEndpointsUnique
          (selectedFoldScan selectedFold) (episodeScan segments)
        0 centerOrdinalSame = fst centerEndpointSame
        0 centerLiveSame = snd centerEndpointSame
        0 postBoundary : PostCloseSelectedBoundary name key world error value
          nameEq keyEq selected registered (episodeEndOrdinal segments)
          (episodeEndLive segments) (locatedAfter episode)
          (selectedFoldSurvivor selectedFold)
        postBoundary = transportPostCloseBoundary centerOrdinalSame centerLiveSame
          (selectedFoldPostClose selectedFold)
        0 decomposedDiscipline : RegistrationDiscipline protocol nameEq
          (appendTransitions (traceBeforeOpening episode)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode episode)))
              (appendTransitions
                (closedTransitions (locatedEpisode episode)) (traceAfterClosing episode))))
        decomposedDiscipline = replace
          {p = RegistrationDiscipline protocol nameEq}
          (sym (locatedDecomposition episode)) discipline
        0 centerSuffixDiscipline : RegistrationDiscipline protocol nameEq
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (appendTransitions (closedTransitions (locatedEpisode episode))
              (traceAfterClosing episode)))
        centerSuffixDiscipline = disciplineAppendRight
          (traceBeforeOpening episode)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (appendTransitions (closedTransitions (locatedEpisode episode))
              (traceAfterClosing episode))) decomposedDiscipline
        0 suffixDiscipline : RegistrationDiscipline protocol nameEq (traceAfterClosing episode)
        suffixDiscipline = disciplineAppendRight
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (traceAfterClosing episode) centerSuffixDiscipline
        0 suffixAligned : AlignedTransitions name key world error value nameEq
          keyEq (traceAfterClosing episode)
        suffixAligned = alignedLocatedAfter global aligned episode
        0 uniqueStart : GenerationEnvironmentNamesUnique episodeStartLive
        uniqueStart = generationTraceScanPreservesUnique nameEq beforeScan
          UniqueNil
        0 stampedStart : GenerationEnvironmentStamped episodeStartLive
        stampedStart = generationTraceScanPreservesStamped nameEq beforeScan
          emptyGenerationEnvironmentStamped
        0 uniqueCenter : GenerationEnvironmentNamesUnique
          (episodeEndLive segments)
        uniqueCenter = generationTraceScanPreservesUnique nameEq
          (episodeScan segments) uniqueStart
        0 stampedCenter : GenerationEnvironmentStamped
          (episodeEndLive segments)
        stampedCenter = generationTraceScanPreservesStamped nameEq
          (episodeScan segments) stampedStart
        0 bornBefore : RegisteredGenerationsBornBefore registered
          (episodeEndOrdinal segments)
        bornBefore = registeredBornBeforeCenterEnd nameEq selected
          episodeStartOrdinal registered
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (episodeEndOrdinal segments)
          (episodeEndLive segments) (episodeScan segments) registeredDuring
        0 suffixFold : RelationalNoEpisodeSuffixReplayFold name key world error
          value nameEq keyEq registered (episodeEndOrdinal segments)
          (episodeEndLive segments) (traceAfterClosing episode)
          (selectedFoldSurvivor selectedFold)
        suffixFold = postCloseSuffixFold protocol nameEq keyEq selected
          registered selectedOutside global noDependent
          (episodeEndOrdinal segments) (episodeEndLive segments) bornBefore
          uniqueCenter stampedCenter (traceAfterClosing episode)
          (selectedFoldSurvivor selectedFold)
          postBoundary suffixDiscipline suffixAligned
          (suffixNoRegistered segments) finalNoFailed
        0 finalOrdinal : Nat
        finalOrdinal = relationalSuffixFinalOrdinal suffixFold
        0 finalLive : GenerationEnvironment name
        finalLive = relationalSuffixFinalLive suffixFold
        0 finalSurvivor : SystemState name key value world error
        finalSurvivor = relationalSuffixFinalSurvivor suffixFold
        0 finalEndpointSame :
          (finalOrdinal = originalFinalOrdinal segments,
           finalLive = originalFinalLive segments)
        finalEndpointSame = generationScanEndpointsUnique
          (relationalSuffixGenerationScan suffixFold) (suffixScan segments)
        0 finalLiveSame : finalLive = originalFinalLive segments
        finalLiveSame = snd finalEndpointSame
        0 finalBoundary : RelationalNoEpisodeReplayBoundary name key world
          error value nameEq keyEq registered finalLive finalState finalSurvivor
        finalBoundary = relationalSuffixFinalBoundary suffixFold
        0 finalUnique : GenerationEnvironmentNamesUnique finalLive
        finalUnique = relationalSuffixFinalUnique suffixFold
        0 finalStamped : GenerationEnvironmentStamped finalLive
        finalStamped = generationTraceScanPreservesStamped nameEq
          (relationalSuffixGenerationScan suffixFold) stampedCenter
        0 finalInactive : CurrentRegisteredInactiveFibers name key world error
          value nameEq registered finalLive finalState
        finalInactive = currentRegisteredInactiveTrace nameEq keyEq registered
          (episodeEndOrdinal segments) (episodeEndLive segments) uniqueCenter
          (traceAfterClosing episode) finalOrdinal finalLive
          (relationalSuffixGenerationScan suffixFold) suffixAligned
          (suffixNoRegistered segments) (postCloseCurrentInactive postBoundary)
        0 finalEmpty : CurrentRegisteredEmptyTables name key world error value
          nameEq registered finalLive finalState
        finalEmpty = currentRegisteredEmptyTableTrace nameEq keyEq registered
          (episodeEndOrdinal segments) (episodeEndLive segments) uniqueCenter
          (traceAfterClosing episode) finalOrdinal finalLive
          (relationalSuffixGenerationScan suffixFold) suffixAligned
          (suffixNoRegistered segments) (postCloseCurrentInactive postBoundary)
          (postCloseCurrentEmpty postBoundary)
        0 finalPlanEmpty : EmptyTableInactivePlan name key world error value
          nameEq (inactiveLeafPlan (completePlanResult
            (relationalCompletePlan finalBoundary)))
        finalPlanEmpty = completeCurrentRegisteredPlanHasEmptyTables nameEq
          registered finalLive finalUnique (worldState finalState)
          (registry finalState) (relationalCompletePlan finalBoundary) finalEmpty
        0 withdrawable : CurrentRegisteredWithdrawable name key world error
          value nameEq registered finalLive finalState
        withdrawable = currentRegisteredWithdrawableFromTrace nameEq keyEq
          selected registered episodeStartOrdinal episodeStartLive (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          (episodeEndOrdinal segments) (episodeEndLive segments)
          (episodeScan segments) uniqueStart stampedStart
          (alignedLocatedCenter global aligned episode)
          (episodeNoRegistered segments) registeredDuring (traceAfterClosing episode) bornBefore
          uniqueCenter (relationalSuffixGenerationScan suffixFold) finalStamped
          suffixAligned (suffixNoRegistered segments)
          (postCloseCurrentInactive postBoundary)
          (postCloseCurrentEmpty postBoundary)
        0 endpoint :
          (EffectStateRelated keyEq (projectEffectState @{nameEq} finalState)
              (projectEffectState @{nameEq} finalSurvivor),
           ControlEquivalentOutsideGenerations nameEq registered finalLive
             finalState finalSurvivor,
           RegisteredNamesWithdrawn nameEq registered finalLive finalState
             finalSurvivor)
        endpoint = relationalBoundaryGivesEndpointEvidence nameEq keyEq
          registered finalLive finalUnique finalState finalSurvivor finalBoundary
          finalPlanEmpty withdrawable
        0 beforeDeletion : GenerationActionSubsequence nameEq
          (GenerationOwnedActor nameEq registered) 0 []
          (traceBeforeOpening episode) (traceBeforeOpening episode)
        beforeDeletion = deletionBeforeFromRegisteredDuring nameEq selected
          registered (traceBeforeOpening episode) (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode))) episodeStartOrdinal
          episodeStartLive beforeScan registeredDuring
    in case replayReadyResultAt nameEq
      (EpisodeGenerationDeletedActor nameEq selected registered)
      episodeStartOrdinal episodeStartLive
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))
      (locatedPreStart episode) (selectedFoldReady selectedFold)
      (selectedFoldReadyEnds selectedFold) of
      MkReadyGenerationResult episodeFiltered episodeFinalSame =>
        case replayReadyResultAt nameEq
          (GenerationOwnedActor nameEq registered)
          (episodeEndOrdinal segments) (episodeEndLive segments)
          (traceAfterClosing episode) (selectedFoldSurvivor selectedFold)
          (relationalSuffixReplayReady suffixFold)
          (relationalSuffixReadyEnds suffixFold) of
          MkReadyGenerationResult suffixFilteredRaw suffixFinalSame =>
            let 0 suffixFiltered : GenerationFilterResult name key world
                  error value nameEq (GenerationOwnedActor nameEq registered)
                  (episodeEndOrdinal segments) (episodeEndLive segments)
                  (traceAfterClosing episode)
                  (GenerationFilterResult.survivingFinal episodeFiltered)
                suffixFiltered = transportGenerationFilterSource (sym episodeFinalSame)
                  suffixFilteredRaw
                0 filteredFinalSame :
                  (GenerationFilterResult.survivingFinal suffixFiltered =
                    finalSurvivor)
                filteredFinalSame = trans
                  (transportGenerationFilterFinal (sym episodeFinalSame) suffixFilteredRaw)
                  suffixFinalSame
                0 skeleton : DeletionTraceSkeleton name key world error
                  value nameEq keyEq global selected episode registered
                  episodeStartOrdinal episodeStartLive
                skeleton = MkDeletionTraceSkeleton segments beforeScan
                  beforeDeletion episodeFiltered suffixFiltered
                0 effectsAtSkeleton : EffectStateRelated keyEq
                  (projectEffectState @{nameEq} finalState)
                  (projectEffectState @{nameEq}
                    (GenerationFilterResult.survivingFinal suffixFiltered))
                effectsAtSkeleton = replace
                  {p = \observed => EffectStateRelated keyEq
                    (projectEffectState @{nameEq} finalState)
                    (projectEffectState @{nameEq} observed)}
                  (sym filteredFinalSame) (fst endpoint)
                0 controlsAtFinalLive : ControlEquivalentOutsideGenerations
                  nameEq registered finalLive finalState
                  (GenerationFilterResult.survivingFinal suffixFiltered)
                controlsAtFinalLive = replace
                  {p = \observed => ControlEquivalentOutsideGenerations nameEq
                    registered finalLive finalState observed}
                  (sym filteredFinalSame) (fst (snd endpoint))
                0 controlsAtSkeleton : ControlEquivalentOutsideGenerations nameEq
                  registered (originalFinalLive segments) finalState
                  (GenerationFilterResult.survivingFinal suffixFiltered)
                controlsAtSkeleton = replace
                  {p = \observedLive => ControlEquivalentOutsideGenerations
                    nameEq registered observedLive finalState
                    (GenerationFilterResult.survivingFinal suffixFiltered)}
                  finalLiveSame controlsAtFinalLive
                0 withdrawnAtFinalLive : RegisteredNamesWithdrawn nameEq
                  registered finalLive finalState
                  (GenerationFilterResult.survivingFinal suffixFiltered)
                withdrawnAtFinalLive = replace
                  {p = \observed => RegisteredNamesWithdrawn nameEq registered
                    finalLive finalState observed}
                  (sym filteredFinalSame) (snd (snd endpoint))
                0 withdrawnAtSkeleton : RegisteredNamesWithdrawn nameEq registered
                  (originalFinalLive segments) finalState
                  (GenerationFilterResult.survivingFinal suffixFiltered)
                withdrawnAtSkeleton = replace
                  {p = \observedLive => RegisteredNamesWithdrawn nameEq registered
                    observedLive finalState
                    (GenerationFilterResult.survivingFinal suffixFiltered)}
                  finalLiveSame withdrawnAtFinalLive
                0 endpointEvidence : DeletionEndpointEvidence name key world
                  error value nameEq keyEq skeleton selectedOutside
                endpointEvidence = MkDeletionEndpointEvidence effectsAtSkeleton
                  controlsAtSkeleton withdrawnAtSkeleton
            in assembleDeletionResult skeleton selectedOutside endpointEvidence
