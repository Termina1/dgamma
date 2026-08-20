module DGamma.CP4DeletionSelectedEpisodeFold

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPremiseSplit
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedEpisodeFoldCore
import DGamma.CP4DeletionSelectedEpisodeReplay
import DGamma.CP4DeletionSelectedEpisodeAnchors
import DGamma.CP4DeletionSelectedStart
import DGamma.CP4RecoveryModelTrace
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 noRegisteredAppendLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  NoRegisteredEpisode nameEq registered ordinal live
    (appendTransitions left right) ->
  NoRegisteredEpisode nameEq registered ordinal live left
noRegisteredAppendLeft nameEq registered ordinal live NoTransitions right
  noRegistered = NoRegisteredEpisodeEnd
noRegisteredAppendLeft nameEq registered ordinal live
  (MoreTransitions transition@(Fired _ _ action tag checked) rest) right
  (NoRegisteredEpisodeStep
    (Fired _ _ action tag checked) (appendTransitions rest right)
    noBegin tail) =
      NoRegisteredEpisodeStep transition rest noBegin
        (noRegisteredAppendLeft nameEq registered (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          rest right tail)

0 appendLeftEmbedding :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  OccurrenceEmbedding left (appendTransitions left right)
appendLeftEmbedding NoTransitions right transition occurs impossible
appendLeftEmbedding (MoreTransitions transition rest) right transition OccursHere =
  OccursHere
appendLeftEmbedding (MoreTransitions head rest) right transition
  (OccursLater later) = OccursLater
    (appendLeftEmbedding rest right transition later)

0 appendRightEmbedding :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  OccurrenceEmbedding right (appendTransitions left right)
appendRightEmbedding NoTransitions right transition occurs = occurs
appendRightEmbedding (MoreTransitions head rest) right transition occurs =
  OccursLater (appendRightEmbedding rest right transition occurs)

0 transportEmbeddingTarget :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {segmentFirst, segmentLast, wholeFirst, wholeLast :
    SystemState name key value world error} ->
  {segment : Transitions segmentFirst segmentLast} ->
  {left, right : Transitions wholeFirst wholeLast} ->
  left = right -> OccurrenceEmbedding segment left -> OccurrenceEmbedding segment right
transportEmbeddingTarget Refl embedding = embedding

0 appendGenerationScan :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  GenerationTraceScan nameEq ordinal live left middleOrdinal middleLive ->
  GenerationTraceScan nameEq middleOrdinal middleLive right finalOrdinal finalLive ->
  GenerationTraceScan nameEq ordinal live (appendTransitions left right)
    finalOrdinal finalLive
appendGenerationScan NoTransitions right GenerationTraceScanEnd rightScan =
  rightScan
appendGenerationScan
  (MoreTransitions transition rest) right
  (GenerationTraceScanStep transition rest leftTail) rightScan =
    GenerationTraceScanStep transition (appendTransitions rest right)
      (appendGenerationScan rest right leftTail rightScan)

0 appendReady :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (scan : GenerationTraceScan nameEq ordinal live left endOrdinal endLive) ->
  GenerationReplayReady nameEq keyEq deletable ordinal live left survivor ->
  ((endSurvivor : SystemState name key value world error) ->
    GenerationReplayReady nameEq keyEq deletable endOrdinal endLive right
      endSurvivor) ->
  GenerationReplayReady nameEq keyEq deletable ordinal live
    (appendTransitions left right) survivor
appendReady nameEq keyEq deletable NoTransitions right GenerationTraceScanEnd
  ReplayReadyEnd rightReady = rightReady survivor
appendReady nameEq keyEq deletable
  (MoreTransitions transition@(Fired _ _ action tag checked) rest) right
  (GenerationTraceScanStep
    (Fired _ _ action tag checked) rest scanTail)
  (ReplayReadyDelete deleted readyTail) rightReady =
    ReplayReadyDelete deleted
      (appendReady nameEq keyEq deletable rest right scanTail readyTail rightReady)
appendReady nameEq keyEq deletable
  (MoreTransitions transition@(Fired _ _ action tag checked) rest) right
  (GenerationTraceScanStep
    (Fired _ _ action tag checked) rest scanTail)
  (ReplayReadyKeep retained next tagNext fired sameAction fires readyTail)
  rightReady =
    ReplayReadyKeep retained next tagNext fired sameAction fires
      (appendReady nameEq keyEq deletable rest right scanTail readyTail rightReady)

0 appendReadySelfEnds :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (scan : GenerationTraceScan nameEq ordinal live left middleOrdinal middleLive) ->
  (ready : GenerationReplayReady nameEq keyEq deletable ordinal live left
    survivorFirst) ->
  (rightReady : (current : SystemState name key value world error) ->
    GenerationReplayReady nameEq keyEq deletable middleOrdinal middleLive right
      current) ->
  ((current : SystemState name key value world error) ->
    ReplayReadyEndsAt (rightReady current) current) ->
  (leftEnds : ReplayReadyEndsAt ready target) ->
  ReplayReadyEndsAt
    (appendReady nameEq keyEq deletable left right scan ready rightReady) target
appendReadySelfEnds nameEq keyEq deletable NoTransitions right
  GenerationTraceScanEnd ReplayReadyEnd rightReady rightEnds
  (ReplayEndsEnd {endpoint = survivorFirst} same) =
    replace
      {p = \observed => ReplayReadyEndsAt (rightReady survivorFirst) observed}
      (sym same) (rightEnds survivorFirst)
appendReadySelfEnds nameEq keyEq deletable
  (MoreTransitions transition@(Fired _ _ action ruleTag checked) rest) right
  (GenerationTraceScanStep (Fired _ _ action ruleTag checked) rest tailScan)
  (ReplayReadyDelete deleted tailReady) rightReady rightEnds
  (ReplayEndsDelete _ _ tailEnds) =
    let 0 shape : (appendReady nameEq keyEq deletable
            (MoreTransitions transition rest) right
            (GenerationTraceScanStep transition rest tailScan)
            (ReplayReadyDelete deleted tailReady) rightReady =
          ReplayReadyDelete {originalTransition = transition}
            {originalRest = appendTransitions rest right} deleted
            (appendReady nameEq keyEq deletable rest right tailScan tailReady
            rightReady))
        shape = Refl
        0 built : ReplayReadyEndsAt
          (ReplayReadyDelete {originalTransition = transition}
            {originalRest = appendTransitions rest right} deleted
            (appendReady nameEq keyEq deletable rest
            right tailScan tailReady rightReady)) target
        built = ReplayEndsDelete deleted (appendReady nameEq keyEq deletable rest
            right tailScan tailReady rightReady)
          (appendReadySelfEnds nameEq keyEq deletable rest right tailScan
            tailReady rightReady rightEnds tailEnds)
    in replace {p = \ready => ReplayReadyEndsAt ready target} (sym shape) built
appendReadySelfEnds nameEq keyEq deletable
  (MoreTransitions transition@(Fired _ _ action ruleTag checked) rest) right
  (GenerationTraceScanStep (Fired _ _ action ruleTag checked) rest tailScan)
  (ReplayReadyKeep retained after tag survivingTransition sameAction fires
    tailReady) rightReady rightEnds
  (ReplayEndsKeep _ _ _ _ _ _ tailEnds) =
    let 0 shape : (appendReady nameEq keyEq deletable
            (MoreTransitions transition rest) right
            (GenerationTraceScanStep transition rest tailScan)
            (ReplayReadyKeep retained after tag survivingTransition sameAction
              fires tailReady) rightReady =
          ReplayReadyKeep {originalTransition = transition}
            {originalRest = appendTransitions rest right} retained after tag
            survivingTransition sameAction fires (appendReady nameEq keyEq deletable rest right tailScan tailReady
            rightReady))
        shape = Refl
        0 built : ReplayReadyEndsAt
          (ReplayReadyKeep {originalTransition = transition}
            {originalRest = appendTransitions rest right} retained after tag
            survivingTransition sameAction fires (appendReady nameEq keyEq deletable rest right tailScan
              tailReady rightReady)) target
        built = ReplayEndsKeep retained tag survivingTransition sameAction fires
          (appendReady nameEq keyEq deletable rest right tailScan tailReady
            rightReady)
          (appendReadySelfEnds nameEq keyEq deletable rest right tailScan
            tailReady rightReady rightEnds tailEnds)
    in replace {p = \ready => ReplayReadyEndsAt ready target} (sym shape) built

public export
record SelectedClosedEpisodeFold
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (episodeStartOrdinal : Nat)
  (episodeStartLive : GenerationEnvironment name)
  {preStart, afterClose, wholeLast : SystemState name key value world error}
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    preStart afterClose)
  (whole : Transitions (closedStartState episode) wholeLast) where
  constructor MkSelectedClosedEpisodeFold
  selectedFoldEndOrdinal : Nat
  selectedFoldEndLive : GenerationEnvironment name
  selectedFoldSurvivor : SystemState name key value world error
  0 selectedFoldScan : GenerationTraceScan nameEq episodeStartOrdinal
    episodeStartLive
    (MoreTransitions (beginTransition (closedOpening episode))
      (closedTransitions episode))
    selectedFoldEndOrdinal selectedFoldEndLive
  0 selectedFoldReady : GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    episodeStartOrdinal episodeStartLive
    (MoreTransitions (beginTransition (closedOpening episode))
      (closedTransitions episode)) preStart
  0 selectedFoldReadyEnds : ReplayReadyEndsAt selectedFoldReady
    selectedFoldSurvivor
  0 selectedFoldUnique : GenerationEnvironmentNamesUnique selectedFoldEndLive
  0 selectedFoldStamped : GenerationEnvironmentStamped selectedFoldEndLive
  0 selectedFoldPostClose : PostCloseSelectedBoundary name key world error value
    nameEq keyEq selected registered selectedFoldEndOrdinal selectedFoldEndLive
    afterClose selectedFoldSurvivor

0 initialCurrentInactive :
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE ordinal (generationBirthOrdinal generation)) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live state
initialCurrentInactive registered live bounded lower actor generation member
  current = void (noCurrentRegisteredAtEpisodeStart registered live bounded lower
    actor generation (currentGenerationEntryFromLookup nameEq actor generation
      live current) member)

0 initialCurrentEmpty :
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE ordinal (generationBirthOrdinal generation)) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    state
initialCurrentEmpty registered live bounded lower actor generation member current
  fiber found = void (noCurrentRegisteredAtEpisodeStart registered live bounded
    lower actor generation (currentGenerationEntryFromLookup nameEq actor
      generation live current) member)

||| Complete selected-episode fold.  Opening and closing lifecycle actions are
||| deleted, every installed interior head is dispatched by the concrete local
||| replay module, and the closing accumulator is packaged into the post-close
||| selected-static boundary.
public export
0 selectedClosedEpisodeFold :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  TraceIndependent name key world error value keyEq global ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (beforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening located) episodeStartOrdinal episodeStartLive) ->
  (registeredDuring : RegisteredGenerationsDuring selected episodeStartOrdinal
    registered
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  (noRegistered : NoRegisteredEpisode nameEq registered 0 [] global) ->
  SelectedEpisodeLifecycleAnchorProvider name key world error value nameEq keyEq
    selected registered global (locatedEpisode located) ->
  SelectedClosedEpisodeFold name key world error value nameEq keyEq selected
    registered episodeStartOrdinal episodeStartLive (locatedEpisode located)
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
selectedClosedEpisodeFold {name} {key} {world} {error} {value}
  protocol nameEq keyEq initial finalState global aligned discipline initialWF
  independent selected located registered selectedOutside episodeStartOrdinal
  episodeStartLive beforeScan registeredDuring noDependent noRegistered anchors =
    let 0 alignedDecomposed : AlignedTransitions name key world error value nameEq
          keyEq
          (appendTransitions (traceBeforeOpening located)
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode located)))
              (appendTransitions (closedTransitions (locatedEpisode located))
                (traceAfterClosing located))))
        alignedDecomposed = replace
          {p = \trace => AlignedTransitions name key world error value nameEq
            keyEq trace}
          (sym (locatedDecomposition located)) aligned
        0 alignedParts :
          (AlignedTransitions name key world error value nameEq keyEq
            (traceBeforeOpening located),
           AlignedTransitions name key world error value nameEq keyEq
            (MoreTransitions
              (beginTransition (closedOpening (locatedEpisode located)))
              (appendTransitions (closedTransitions (locatedEpisode located))
                (traceAfterClosing located))))
        alignedParts = alignedAppendSplit (traceBeforeOpening located)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            (appendTransitions (closedTransitions (locatedEpisode located))
              (traceAfterClosing located))) alignedDecomposed
        0 alignedAfterOpening : AlignedTransitions name key world error value
          nameEq keyEq
          (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
        alignedAfterOpening = case snd alignedParts of
          AlignedStep (LBegin selected) LBeginTag _ _ alignedWhole =>
            alignedWhole
        0 alignedAfterOpeningAssoc : AlignedTransitions name key world error
          value nameEq keyEq
          (appendTransitions (closedInside (locatedEpisode located))
            (MoreTransitions
              (unloadTransition (closing (locatedEpisode located)))
              (traceAfterClosing located)))
        alignedAfterOpeningAssoc = replace
          {p = \trace => AlignedTransitions name key world error value nameEq
            keyEq trace}
          (appendTransitionsAssociative
            (closedInside (locatedEpisode located))
            (MoreTransitions
              (unloadTransition (closing (locatedEpisode located))) NoTransitions)
            (traceAfterClosing located)) alignedAfterOpening
        0 alignedWholeParts :
          (AlignedTransitions name key world error value nameEq keyEq
            (closedInside (locatedEpisode located)),
           AlignedTransitions name key world error value nameEq keyEq
            (MoreTransitions (unloadTransition (closing (locatedEpisode located)))
              (traceAfterClosing located)))
        alignedWholeParts = alignedAppendSplit (closedInside (locatedEpisode located))
          (MoreTransitions (unloadTransition (closing (locatedEpisode located)))
            (traceAfterClosing located)) alignedAfterOpeningAssoc
        0 alignedInside : AlignedTransitions name key world error value nameEq
          keyEq (closedInside (locatedEpisode located))
        alignedInside = fst alignedWholeParts
        0 segments : LocatedNoRegisteredSegments name key world error value
          nameEq keyEq global selected located registered episodeStartOrdinal
          episodeStartLive
        segments = splitLocatedNoRegisteredSegments nameEq keyEq global selected
          located registered episodeStartOrdinal episodeStartLive beforeScan
          noRegistered
        0 centerNoRegistered : NoRegisteredEpisode nameEq registered
          episodeStartOrdinal episodeStartLive
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            (closedTransitions (locatedEpisode located)))
        centerNoRegistered = episodeNoRegistered segments
        0 afterOpeningNoRegistered : NoRegisteredEpisode nameEq registered
          (S episodeStartOrdinal) episodeStartLive
          (closedTransitions (locatedEpisode located))
        afterOpeningNoRegistered = case centerNoRegistered of
          NoRegisteredEpisodeStep _ _ _ tail => tail
        0 insideNoRegistered : NoRegisteredEpisode nameEq registered
          (S episodeStartOrdinal) episodeStartLive
          (closedInside (locatedEpisode located))
        insideNoRegistered = noRegisteredAppendLeft nameEq registered
          (S episodeStartOrdinal) episodeStartLive
          (closedInside (locatedEpisode located))
          (MoreTransitions
            (unloadTransition (closing (locatedEpisode located))) NoTransitions)
          afterOpeningNoRegistered
        0 bounded : GenerationEnvironmentBounded episodeStartOrdinal
          episodeStartLive
        bounded = generationScanPreservesBounded nameEq ()
          (traceBeforeOpening located) beforeScan
        0 lower : (generation : RegistrationGeneration name) ->
          Elem generation registered ->
          LTE episodeStartOrdinal (generationBirthOrdinal generation)
        lower = registeredDuringBirthLowerBound registeredDuring
        0 uniqueStart : GenerationEnvironmentNamesUnique episodeStartLive
        uniqueStart = generationTraceScanPreservesUnique nameEq beforeScan
          UniqueNil
        0 stampedStart : GenerationEnvironmentStamped episodeStartLive
        stampedStart = generationTraceScanPreservesStamped nameEq beforeScan
          emptyGenerationEnvironmentStamped
        0 preWF : registryWellFormed @{nameEq} @{keyEq}
          (locatedPreStart located) = True
        preWF = alignedTraceWellFormedEnd nameEq keyEq
          (traceBeforeOpening located) (fst alignedParts) initialWF
        0 initialBoundary : SelectedEpisodeReplayBoundary name key world error
          value nameEq keyEq selected registered (S episodeStartOrdinal)
          episodeStartLive
          (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
          (closedStartState (locatedEpisode located))
          (locatedPreStart located)
        initialBoundary = initialSelectedEpisodeBoundary nameEq keyEq selected
          registered episodeStartOrdinal episodeStartLive
          (traceBeforeOpening located) beforeScan
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            (closedTransitions (locatedEpisode located)))
          registeredDuring
          (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
          (closedOpening (locatedEpisode located)) preWF
        0 initialInactive : CurrentRegisteredInactiveFibers name key world error
          value nameEq registered episodeStartLive
          (closedStartState (locatedEpisode located))
        initialInactive = initialCurrentInactive registered episodeStartLive
          bounded lower
        0 initialEmpty : CurrentRegisteredEmptyTables name key world error value
          nameEq registered episodeStartLive
          (closedStartState (locatedEpisode located))
        initialEmpty = initialCurrentEmpty registered episodeStartLive bounded
          lower
        0 initialPlanEmpty : EmptyTableInactivePlan name key world error value
          nameEq (inactiveLeafPlan (completePlanResult
            (selectedBoundaryPlan initialBoundary)))
        initialPlanEmpty = completeCurrentRegisteredPlanHasEmptyTables nameEq
          registered episodeStartLive uniqueStart (worldState (closedStartState (locatedEpisode located)))
          (registry (closedStartState (locatedEpisode located)))
          (selectedBoundaryPlan initialBoundary) initialEmpty
        insideEmbedding : OccurrenceEmbedding (closedInside (locatedEpisode located)) (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
        insideEmbedding = transportEmbeddingTarget
          (sym (appendTransitionsAssociative
            (closedInside (locatedEpisode located))
            (MoreTransitions
              (unloadTransition (closing (locatedEpisode located))) NoTransitions)
            (traceAfterClosing located)))
          (appendLeftEmbedding (closedInside (locatedEpisode located))
            (MoreTransitions
              (unloadTransition (closing (locatedEpisode located)))
              (traceAfterClosing located)))
        wholeGlobalRaw : OccurrenceEmbedding (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
          (appendTransitions (traceBeforeOpening located)
            (MoreTransitions (beginTransition (closedOpening (locatedEpisode located))) (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))))
        wholeGlobalRaw transition occurrence = appendRightEmbedding
          (traceBeforeOpening located)
          (MoreTransitions (beginTransition (closedOpening (locatedEpisode located))) (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located)))
          transition (OccursLater occurrence)
        wholeGlobal : OccurrenceEmbedding (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located)) global
        wholeGlobal = transportEmbeddingTarget (locatedDecomposition located)
          wholeGlobalRaw
        0 local : SelectedEpisodeLocalReplayer name key world error value nameEq
          keyEq selected registered protocol
          (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
          (closedInside (locatedEpisode located))
        local = selectedEpisodeLocalReplayer protocol nameEq keyEq selected
          registered selectedOutside global aligned discipline noDependent independent (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
          (locatedEpisode located) wholeGlobal anchors
        0 interior : SelectedEpisodeInteriorFold name key world error value
          nameEq keyEq selected registered (S episodeStartOrdinal)
          episodeStartLive
          (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
          (closedInside (locatedEpisode located)) (locatedPreStart located)
        interior = selectedEpisodeInteriorFold protocol nameEq keyEq selected
          registered selectedOutside (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located)) (closedInside (locatedEpisode located))
          local (S episodeStartOrdinal)
          episodeStartLive uniqueStart stampedStart (closedInside (locatedEpisode located))
          alignedInside (closedInsideInstalled (locatedEpisode located))
          insideNoRegistered insideEmbedding NoTransitions Refl
          (locatedPreStart located)
          initialBoundary initialInactive initialEmpty initialPlanEmpty
        0 finalUnique : GenerationEnvironmentNamesUnique
          (interiorFinalLive interior)
        finalUnique = generationTraceScanPreservesUnique nameEq
          (interiorScan interior) uniqueStart
        0 finalStamped : GenerationEnvironmentStamped
          (interiorFinalLive interior)
        finalStamped = generationTraceScanPreservesStamped nameEq
          (interiorScan interior) stampedStart
        0 finalInactive : CurrentRegisteredInactiveFibers name key world error
          value nameEq registered (interiorFinalLive interior)
          (lastInstalledState (locatedEpisode located))
        finalInactive = currentRegisteredInactiveTrace nameEq keyEq registered
          (S episodeStartOrdinal) episodeStartLive uniqueStart
          (closedInside (locatedEpisode located)) (interiorFinalOrdinal interior)
          (interiorFinalLive interior) (interiorScan interior) alignedInside
          insideNoRegistered initialInactive
        0 finalEmpty : CurrentRegisteredEmptyTables name key world error value
          nameEq registered (interiorFinalLive interior)
          (lastInstalledState (locatedEpisode located))
        finalEmpty = currentRegisteredEmptyTableTrace nameEq keyEq registered
          (S episodeStartOrdinal) episodeStartLive uniqueStart
          (closedInside (locatedEpisode located)) (interiorFinalOrdinal interior)
          (interiorFinalLive interior) (interiorScan interior) alignedInside
          insideNoRegistered initialInactive initialEmpty
        0 finalPlanEmpty : EmptyTableInactivePlan name key world error value
          nameEq (inactiveLeafPlan (completePlanResult
            (selectedBoundaryPlan (interiorBoundary interior))))
        finalPlanEmpty = completeCurrentRegisteredPlanHasEmptyTables nameEq
          registered (interiorFinalLive interior) finalUnique
          (worldState (lastInstalledState (locatedEpisode located)))
          (registry (lastInstalledState (locatedEpisode located)))
          (selectedBoundaryPlan (interiorBoundary interior)) finalEmpty
        0 postClose : PostCloseSelectedBoundary name key world error value
          nameEq keyEq selected registered (S (interiorFinalOrdinal interior))
          (interiorFinalLive interior) (locatedAfter located)
          (interiorFinalSurvivor interior)
        postClose = selectedUnloadClosesPostBoundary nameEq keyEq selected
          registered (interiorFinalOrdinal interior) (interiorFinalLive interior)
          finalUnique finalStamped selectedOutside (appendTransitions (closedTransitions (locatedEpisode located))
            (traceAfterClosing located))
          (lastInstalledState (locatedEpisode located)) (locatedAfter located)
          (interiorFinalSurvivor interior) (closing (locatedEpisode located))
          (interiorBoundary interior) finalPlanEmpty finalInactive finalEmpty
        0 closeTransition : Transition
          (lastInstalledState (locatedEpisode located)) (locatedAfter located)
        closeTransition = unloadTransition (closing (locatedEpisode located))
        closeDeleted : EpisodeGenerationDeletedActor nameEq selected registered
          (interiorFinalOrdinal interior) (interiorFinalLive interior)
          (LUnload selected)
        closeDeleted = DeleteEpisodeGenerationLifecycle Refl Refl
        closeReady : (currentSurvivor : SystemState name key value world error) ->
          GenerationReplayReady nameEq keyEq
            (EpisodeGenerationDeletedActor nameEq selected registered)
            (interiorFinalOrdinal interior) (interiorFinalLive interior)
            (MoreTransitions closeTransition NoTransitions) currentSurvivor
        closeReady currentSurvivor = ReplayReadyDelete closeDeleted ReplayReadyEnd
        0 insideCloseReady : GenerationReplayReady nameEq keyEq
          (EpisodeGenerationDeletedActor nameEq selected registered)
          (S episodeStartOrdinal) episodeStartLive
          (closedTransitions (locatedEpisode located)) (locatedPreStart located)
        insideCloseReady = appendReady nameEq keyEq
          (EpisodeGenerationDeletedActor nameEq selected registered)
          (closedInside (locatedEpisode located)) (MoreTransitions closeTransition NoTransitions)
          (interiorScan interior) (interiorReady interior) closeReady
        openingDeleted : EpisodeGenerationDeletedActor nameEq selected registered
          episodeStartOrdinal episodeStartLive (LBegin selected)
        openingDeleted = DeleteEpisodeGenerationLifecycle Refl Refl
        0 fullReady : GenerationReplayReady nameEq keyEq
          (EpisodeGenerationDeletedActor nameEq selected registered)
          episodeStartOrdinal episodeStartLive
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            (closedTransitions (locatedEpisode located)))
          (locatedPreStart located)
        fullReady = ReplayReadyDelete openingDeleted insideCloseReady
        closeEnds : (currentSurvivor : SystemState name key value world error) ->
          ReplayReadyEndsAt (closeReady currentSurvivor) currentSurvivor
        closeEnds currentSurvivor = ReplayEndsDelete closeDeleted ReplayReadyEnd
          (ReplayEndsEnd Refl)
        0 insideCloseEnds : ReplayReadyEndsAt insideCloseReady
          (interiorFinalSurvivor interior)
        insideCloseEnds = appendReadySelfEnds nameEq keyEq
          (EpisodeGenerationDeletedActor nameEq selected registered)
          (closedInside (locatedEpisode located))
          (MoreTransitions closeTransition NoTransitions)
          (interiorScan interior) (interiorReady interior) closeReady closeEnds
          (interiorReadyEnds interior)
        0 fullReadyEnds : ReplayReadyEndsAt fullReady
          (interiorFinalSurvivor interior)
        fullReadyEnds = ReplayEndsDelete openingDeleted insideCloseReady
          insideCloseEnds
        appendScanWithClose : GenerationTraceScan nameEq (S episodeStartOrdinal)
          episodeStartLive (closedTransitions (locatedEpisode located))
          (S (interiorFinalOrdinal interior)) (interiorFinalLive interior)
        appendScanWithClose = appendGenerationScan (closedInside (locatedEpisode located))
          (MoreTransitions closeTransition NoTransitions) (interiorScan interior)
          (GenerationTraceScanStep closeTransition NoTransitions
            GenerationTraceScanEnd)
        0 fullScan : GenerationTraceScan nameEq episodeStartOrdinal
          episodeStartLive
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode located)))
            (closedTransitions (locatedEpisode located)))
          (S (interiorFinalOrdinal interior)) (interiorFinalLive interior)
        fullScan = GenerationTraceScanStep (beginTransition (closedOpening (locatedEpisode located)))
          (closedTransitions (locatedEpisode located))
          appendScanWithClose
    in MkSelectedClosedEpisodeFold (S (interiorFinalOrdinal interior))
      (interiorFinalLive interior) (interiorFinalSurvivor interior) fullScan
      fullReady fullReadyEnds finalUnique finalStamped postClose

||| Public-premise entry point: reconstruct the occurrence-local lifecycle
||| anchor provider internally, then run the complete selected structural fold.
public export
0 selectedClosedEpisodeFoldFromPremises :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  TraceIndependent name key world error value keyEq global ->
  (selected : name) ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq
    selected global) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (beforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening located) episodeStartOrdinal episodeStartLive) ->
  (registeredDuring : RegisteredGenerationsDuring selected episodeStartOrdinal
    registered
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode located)))
      (closedTransitions (locatedEpisode located)))) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  (noRegistered : NoRegisteredEpisode nameEq registered 0 [] global) ->
  SelectedClosedEpisodeFold name key world error value nameEq keyEq selected
    registered episodeStartOrdinal episodeStartLive (locatedEpisode located)
    (appendTransitions (closedTransitions (locatedEpisode located))
      (traceAfterClosing located))
selectedClosedEpisodeFoldFromPremises protocol nameEq keyEq initial finalState
  global aligned discipline initialWellFormed initialEmpty independent selected
  located registered selectedOutside episodeStartOrdinal episodeStartLive
  beforeScan registeredDuring noDependent noRegistered =
    selectedClosedEpisodeFold protocol nameEq keyEq initial finalState global
      aligned discipline initialWellFormed independent selected located registered
      selectedOutside episodeStartOrdinal episodeStartLive beforeScan
      registeredDuring noDependent noRegistered
      (selectedEpisodeLifecycleAnchorProvider nameEq keyEq initial finalState
        global aligned initialWellFormed initialEmpty selected located registered
        noDependent)
