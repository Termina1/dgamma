module DGamma.CP5O20DeletionDisappearanceSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5O20CanonicalMaybeControlSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Join scans of actual adjacent trace segments. Only the first scan is
||| eliminated; the actual ordinal/live indices are preserved at the cut.
export
0 o20AppendGenerationScans :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {ordinal, middleOrdinal, finalOrdinal : Nat} ->
  {live, middleLive, finalLive : GenerationEnvironment name} ->
  {earlier : Transitions first middle} -> {later : Transitions middle finalState} ->
  GenerationTraceScan nameEq ordinal live earlier middleOrdinal middleLive ->
  GenerationTraceScan nameEq middleOrdinal middleLive later finalOrdinal finalLive ->
  GenerationTraceScan nameEq ordinal live (appendTransitions earlier later) finalOrdinal finalLive
o20AppendGenerationScans GenerationTraceScanEnd right = right
o20AppendGenerationScans (GenerationTraceScanStep step rest left) right =
  GenerationTraceScanStep step _ (o20AppendGenerationScans left right)

||| The actual deletion construction owns a whole ORIGINAL generation scan
||| by joining its before/episode/after scans at this episode's decomposition.
export
0 o20DeletionOriginalScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {original : Transitions initial finalState} ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq original) ->
  (result : DeletionResult name key world error value nameEq keyEq original
    (selectedActor candidate) (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->
  GenerationTraceScan nameEq Z [] original (originalFinalOrdinal result) (originalFinalLive result)
o20DeletionOriginalScan {nameEq} candidate result =
  replace {p = \trace => GenerationTraceScan nameEq Z [] trace (originalFinalOrdinal result) (originalFinalLive result)}
    (locatedDecomposition (selectedEpisode candidate))
    (o20AppendGenerationScans (beforeGenerationScan result)
      (o20AppendGenerationScans (episodeGenerationScan result) (afterGenerationScan result)))

||| Standalone observed Begin projection; the frozen counterpart is private.
export
0 o20DeletionBeginLiveObserved :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (actor : name) -> (live : GenerationEnvironment name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) -> (deleted : List (RegistrationGeneration name)) ->
  (observed : Maybe (RegistrationGeneration name)) ->
  (lookupCurrentGeneration @{nameEq} actor live = observed) ->
  (indexedLiveGenerations (advanceRegistrationIndex @{nameEq} ordinal
    (the (Action name key value world error) (LBegin actor))
    (MkRegistrationIndexState live activations counts deleted)) = live)
o20DeletionBeginLiveObserved name key world error value nameEq ordinal actor live activations counts deleted Nothing exact =
  rewrite exact in Refl
o20DeletionBeginLiveObserved name key world error value nameEq ordinal actor live activations counts deleted (Just generation) exact =
  rewrite exact in Refl

||| Every native action projects its actual registration-index update.
export
0 o20DeletionIndexLiveAdvance :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (action : Action name key value world error) -> (index : RegistrationIndexState name) ->
  (indexedLiveGenerations (advanceRegistrationIndex @{nameEq} ordinal action index) =
    advanceGenerationEnvironment @{nameEq} ordinal action (indexedLiveGenerations index))
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (OInsert child Root component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (OInsert child (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (ORetire actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (ORemove actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (LBegin actor)
  (MkRegistrationIndexState live activations counts deleted) =
    o20DeletionBeginLiveObserved name key world error value nameEq ordinal actor live activations counts deleted
      (lookupCurrentGeneration @{nameEq} actor live) Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (LAdvance actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (LDivert actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (LLeave actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20DeletionIndexLiveAdvance name key world error value nameEq ordinal (LUnload actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl

||| Observed surviving-Insert activation retains the exact child stamp.
export
0 o20DeletionSurvivingLiveObserved :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (child, parent : name) -> (component : Component key value world error) ->
  (live : GenerationEnvironment name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) -> (deleted : List (RegistrationGeneration name)) ->
  (observed : Maybe (RegistrationActivation name)) ->
  (lookupParentActivation @{nameEq} parent activations = observed) ->
  (indexedLiveGenerations (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component
    (MkRegistrationIndexState live activations counts deleted)) =
    advanceGenerationEnvironment @{nameEq} ordinal (OInsert child (ChildOf parent) component) live)
o20DeletionSurvivingLiveObserved name key world error value nameEq ordinal child parent component live activations counts deleted Nothing exact =
  rewrite exact in Refl
o20DeletionSurvivingLiveObserved name key world error value nameEq ordinal child parent component live activations counts deleted (Just activation) exact =
  rewrite exact in Refl

||| Project the LEFT scan directly from the public bilateral correspondence.
||| The private side-scan type is intentionally not used. Right-only advances
||| recurse without changing the left trace, and both matching directions keep
||| the real asynchronous indices and pending words.
export
0 o20DeletionSideGenerationScan :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (mapping : RegistrationGenerationBijection name) ->
  (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
  (rightOrdinal : Nat) -> (rightIndex : RegistrationIndexState name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (leftFinalIndex, rightFinalIndex : RegistrationIndexState name) ->
  {pendingLeft, pendingRight : List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq mapping leftOrdinal leftIndex left leftFinalIndex
    rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight ->
  (finalOrdinal : Nat ** GenerationTraceScan nameEq leftOrdinal (indexedLiveGenerations leftIndex)
    left finalOrdinal (indexedLiveGenerations leftFinalIndex))
o20DeletionSideGenerationScan name key world error value nameEq mapping leftOrdinal
  (MkRegistrationIndexState live activations counts deleted) rightOrdinal rightIndex
  left right leftFinalIndex rightFinalIndex correspondence = case correspondence of
    RegistrationCorrespondenceEnd => (leftOrdinal ** GenerationTraceScanEnd)
    SkipLeftNonRegistration action step rest actionExact nonRegistration tail =>
      case o20DeletionSideGenerationScan name key world error value nameEq mapping (S leftOrdinal)
        (advanceRegistrationIndex @{nameEq} leftOrdinal action (MkRegistrationIndexState live activations counts deleted)) rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail of
        (finalOrdinal ** scan) => (finalOrdinal ** GenerationTraceScanStep step rest
          (replace {p = \observed => GenerationTraceScan nameEq (S leftOrdinal) observed rest finalOrdinal (indexedLiveGenerations leftFinalIndex)}
            (trans (o20DeletionIndexLiveAdvance name key world error value nameEq leftOrdinal action (MkRegistrationIndexState live activations counts deleted))
              (cong (\chosen => advanceGenerationEnvironment @{nameEq} leftOrdinal chosen live) (sym actionExact))) scan))
    DiscardLeftDeletedRegistration {child} {parent} {component} step rest actionExact discarded tail =>
      case o20DeletionSideGenerationScan name key world error value nameEq mapping (S leftOrdinal)
        (advanceDeletedRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts deleted)) rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail of
        (finalOrdinal ** scan) => (finalOrdinal ** GenerationTraceScanStep step rest
          (replace {p = \observed => GenerationTraceScan nameEq (S leftOrdinal) observed rest finalOrdinal (indexedLiveGenerations leftFinalIndex)}
            (trans (o20DeletionIndexLiveAdvance name key world error value nameEq leftOrdinal (OInsert child (ChildOf parent) component) (MkRegistrationIndexState live activations counts deleted))
              (cong (\chosen => advanceGenerationEnvironment @{nameEq} leftOrdinal chosen live) (sym actionExact))) scan))
    QueueLeftGeneratedRegistration {child} {parent} {component} step rest actionExact retained tail =>
      case o20DeletionSideGenerationScan name key world error value nameEq mapping (S leftOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts deleted)) rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail of
        (finalOrdinal ** scan) => (finalOrdinal ** GenerationTraceScanStep step rest
          (replace {p = \observed => GenerationTraceScan nameEq (S leftOrdinal) observed rest finalOrdinal (indexedLiveGenerations leftFinalIndex)}
            (trans (o20DeletionSurvivingLiveObserved name key world error value nameEq leftOrdinal child parent component live activations counts deleted (lookupParentActivation @{nameEq} parent activations) Refl)
              (cong (\chosen => advanceGenerationEnvironment @{nameEq} leftOrdinal chosen live) (sym actionExact))) scan))
    MatchLeftWithPendingRight {child} {parent} {component} step rest actionExact retained priorWords event laterWords matched tail =>
      case o20DeletionSideGenerationScan name key world error value nameEq mapping (S leftOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts deleted)) rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail of
        (finalOrdinal ** scan) => (finalOrdinal ** GenerationTraceScanStep step rest
          (replace {p = \observed => GenerationTraceScan nameEq (S leftOrdinal) observed rest finalOrdinal (indexedLiveGenerations leftFinalIndex)}
            (trans (o20DeletionSurvivingLiveObserved name key world error value nameEq leftOrdinal child parent component live activations counts deleted (lookupParentActivation @{nameEq} parent activations) Refl)
              (cong (\chosen => advanceGenerationEnvironment @{nameEq} leftOrdinal chosen live) (sym actionExact))) scan))
    SkipRightNonRegistration action step rest actionExact nonRegistration tail =>
      o20DeletionSideGenerationScan name key world error value nameEq mapping leftOrdinal (MkRegistrationIndexState live activations counts deleted)
        (S rightOrdinal) (advanceRegistrationIndex @{nameEq} rightOrdinal action rightIndex) left rest leftFinalIndex rightFinalIndex tail
    DiscardRightDeletedRegistration {child} {parent} {component} step rest actionExact discarded tail =>
      o20DeletionSideGenerationScan name key world error value nameEq mapping leftOrdinal (MkRegistrationIndexState live activations counts deleted)
        (S rightOrdinal) (advanceDeletedRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex) left rest leftFinalIndex rightFinalIndex tail
    QueueRightGeneratedRegistration {child} {parent} {component} step rest actionExact retained tail =>
      o20DeletionSideGenerationScan name key world error value nameEq mapping leftOrdinal (MkRegistrationIndexState live activations counts deleted)
        (S rightOrdinal) (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex) left rest leftFinalIndex rightFinalIndex tail
    MatchRightWithPendingLeft {child} {parent} {component} step rest actionExact retained priorWords event laterWords matched tail =>
      o20DeletionSideGenerationScan name key world error value nameEq mapping leftOrdinal (MkRegistrationIndexState live activations counts deleted)
        (S rightOrdinal) (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex) left rest leftFinalIndex rightFinalIndex tail

||| Accepted original current generations and the actual deletion's current
||| table are the same plain value: both are authenticated scans of THIS word.
||| No equality of independently reconstructed dependent records is needed.
export
0 o20DeletionAcceptedOriginalLive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq left) ->
  (result : DeletionResult name key world error value nameEq keyEq left
    (selectedActor candidate) (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->
  (leftFinalGenerations registrations = originalFinalLive result)
o20DeletionAcceptedOriginalLive {name} {key} {world} {error} {value}
  nameEq keyEq left right mapping registrations candidate result =
  case o20DeletionSideGenerationScan name key world error value nameEq mapping Z emptyRegistrationIndex Z emptyRegistrationIndex
    left right (leftFinalIndex registrations) (rightFinalIndex registrations) (generationTraceCorrespondence registrations) of
    (finalOrdinal ** scan) => trans (o20GenerationScanFinalLiveExact scan)
      (sym (o20GenerationScanFinalLiveExact (o20DeletionOriginalScan candidate result)))

||| A native withdrawal result at an actually current generation owns lookup
||| absence. Its historical branch is rejected by this exact current equation.
export
0 o20CurrentWithdrawalAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {live : GenerationEnvironment name} ->
  {generation : RegistrationGeneration name} ->
  {originalFinal, survivor : SystemState name key value world error} ->
  WithdrawnGenerationResult nameEq live generation originalFinal survivor ->
  (lookupCurrentGeneration @{nameEq} (generationName generation) live = Just generation) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (generationName generation) (registry survivor) = Nothing)
o20CurrentWithdrawalAbsent (CurrentGenerationWithdrawn fiber current found retiredFlag inactive empty absent) observed = absent
o20CurrentWithdrawalAbsent (HistoricalGenerationClosed closed) observed = void (closed observed)

||| Present vestigial disappearance at an actual deletion: the FULL original
||| packet uses BOTH environments of the same accepted surviving-tree scan.
||| Its generation must belong to this actual candidate's selected births;
||| this membership is NOT inferred merely from global discarded membership.
||| The result, current table reconciliation and actual absence are produced.
export
0 o20SelectedVestigialDisappears :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq left) ->
  (result : DeletionResult name key world error value nameEq keyEq left
    (selectedActor candidate) (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->
  (selected : name) ->
  (packet : VestigialEndpointGeneration name key world error value nameEq keyEq
    (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal) ->
  Elem (vestigialGeneration packet) (selectedRegistrations candidate) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (survivingFinal result)) = Nothing)
o20SelectedVestigialDisappears {name} {key} {value} {world} {error}
  nameEq keyEq left right mapping registrations candidate result selected packet member =
  replace {p = \actor => lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    actor (registry (survivingFinal result)) = Nothing}
    (cong generationName (currentBirthStampExact (acceptedLeftCurrentBirth name key world error value nameEq
      left right mapping registrations selected (vestigialGeneration packet) (vestigialGenerationCurrent packet))))
    (o20CurrentWithdrawalAbsent (registeredWithdrawn result (vestigialGeneration packet) member)
      (trans (cong (\actor => lookupCurrentGeneration @{nameEq} actor (originalFinalLive result))
        (cong generationName (currentBirthStampExact (acceptedLeftCurrentBirth name key world error value nameEq
          left right mapping registrations selected (vestigialGeneration packet) (vestigialGenerationCurrent packet)))))
        (trans (cong (\live => lookupCurrentGeneration @{nameEq} selected live)
          (sym (o20DeletionAcceptedOriginalLive nameEq keyEq left right mapping registrations candidate result)))
          (vestigialGenerationCurrent packet))))

||| Whole native deletion-chain induction: an actually absent original name
||| remains absent after every producer-owned deletion endpoint, without a
||| caller-provided endpoint relation for the chain's final state.
export
0 o20DeletionChainPreservesAbsence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  ClosingFreeDeletionDerivation name key world error value protocol nameEq keyEq source target ->
  (selected : name) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry sourceFinal) = Nothing) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry targetFinal) = Nothing)
o20DeletionChainPreservesAbsence nameEq keyEq (ClosingFreeDeletionDone trace) selected absent = absent
o20DeletionChainPreservesAbsence {sourceFinal} nameEq keyEq
  (ClosingFreeDeletionStep trace premises candidate step target rest) selected absent =
  o20DeletionChainPreservesAbsence nameEq keyEq rest selected
    (o20CanonicalEndpointPreservesAbsence nameEq keyEq sourceFinal (survivingFinal (deletionResult step))
      (deletionEndpoint step) selected absent)

||| Observe the selected birth list at the FIRST actual deletion node. This
||| is not the accepted global discarded list and no equality is postulated.
public export
0 o20DeletionHeadGenerations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  ClosingFreeDeletionDerivation name key world error value protocol nameEq keyEq source target ->
  List (RegistrationGeneration name)
o20DeletionHeadGenerations (ClosingFreeDeletionDone trace) = []
o20DeletionHeadGenerations (ClosingFreeDeletionStep trace premises candidate step target rest) = selectedRegistrations candidate

||| A FULL accepted present-vestigial generation selected at the actual head
||| disappears through the entire actual remaining deletion chain. No tail
||| disappearance, endpoint cut, or new withdrawal-result premise is supplied.
||| Global discarded-to-selected coverage is explicitly not proved here.
export
0 o20VestigialHeadDisappearsThroughChain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal, targetFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (target : Transitions leftFirst targetFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (derivation : ClosingFreeDeletionDerivation name key world error value protocol nameEq keyEq left target) ->
  (selected : name) ->
  (packet : VestigialEndpointGeneration name key world error value nameEq keyEq
    (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal) ->
  Elem (vestigialGeneration packet) (o20DeletionHeadGenerations derivation) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry targetFinal) = Nothing)
o20VestigialHeadDisappearsThroughChain nameEq keyEq _ right _ mapping registrations
  (ClosingFreeDeletionDone _) selected packet member = absurd member
o20VestigialHeadDisappearsThroughChain nameEq keyEq left right _ mapping registrations
  (ClosingFreeDeletionStep _ premises candidate step _ rest) selected packet member =
  o20DeletionChainPreservesAbsence nameEq keyEq rest selected
    (o20SelectedVestigialDisappears nameEq keyEq left right mapping registrations candidate
      (deletionResult step) selected packet member)

||| The SAME accepted construction's sorting endpoint preserves reduced
||| lookup absence. It is projected from capital, not taken as a new relation.
export
0 o20ReducedAbsenceSurvivesSorting :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (selected : name) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (reducedFinal (capitalReduction capital))) = Nothing) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (canonicalFinal (canonicalSchedule capital))) = Nothing)
o20ReducedAbsenceSurvivesSorting nameEq keyEq original
  (MkIndependentCanonicalSchedule premises reduction ordering sorted supportTransport accounting _ Refl classified)
  selected absent =
  o20CanonicalEndpointPreservesAbsence nameEq keyEq (reducedFinal reduction) (sortedFinal sorted)
    (sortedEndpoint sorted) selected absent
