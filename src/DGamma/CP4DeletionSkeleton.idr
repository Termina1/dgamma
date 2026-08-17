module DGamma.CP4DeletionSkeleton

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionPremiseSplit
import Data.List.Elem
import Decidable.Equality

%default total

||| The complete trace/subsequence portion of Lemma 72, separated from endpoint
||| effect/control/withdrawal facts. Construction may fail only where a kept
||| action is not yet known to replay in the smaller state.
public export
record DeletionTraceSkeleton
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (selected : name)
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original)
  (registered : List (RegistrationGeneration name))
  (episodeStartOrdinal : Nat)
  (episodeStartLive : GenerationEnvironment name) where
  constructor MkDeletionTraceSkeleton
  splitSegments : LocatedNoRegisteredSegments name key world error value nameEq
    keyEq original selected episode registered episodeStartOrdinal
    episodeStartLive
  0 skeletonBeforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening episode) episodeStartOrdinal episodeStartLive
  0 skeletonBeforeDeletion : GenerationActionSubsequence nameEq
    (GenerationOwnedActor nameEq registered) 0 []
    (traceBeforeOpening episode) (traceBeforeOpening episode)
  episodeSurvivor : GenerationFilterResult name key world error value nameEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    episodeStartOrdinal episodeStartLive
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    (locatedPreStart episode)
  suffixSurvivor : GenerationFilterResult name key world error value nameEq
    (GenerationOwnedActor nameEq registered)
    (episodeEndOrdinal splitSegments) (episodeEndLive splitSegments)
    (traceAfterClosing episode) (survivingFinal episodeSurvivor)

||| Assemble every trace-indexed field from the existing public premises and
||| the total generation filters. A `Nothing` is a concrete replay-applicability
||| obligation, not a missing proof hidden behind an escape hatch.
public export
0 buildDeletionTraceSkeleton :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (original : Transitions initial originalFinal) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] (traceBeforeOpening episode)
    episodeStartOrdinal episodeStartLive ->
  RegisteredGenerationsDuring selected episodeStartOrdinal registered
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode))) ->
  NoRegisteredEpisode nameEq registered 0 [] original ->
  Maybe (DeletionTraceSkeleton name key world error value nameEq keyEq original
    selected episode registered episodeStartOrdinal episodeStartLive)
buildDeletionTraceSkeleton nameEq keyEq original selected episode registered
  episodeStartOrdinal episodeStartLive beforeScan registeredDuring
  noRegistered =
    let 0 beforeDeletion = deletionBeforeFromRegisteredDuring nameEq selected
          registered (traceBeforeOpening episode)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          episodeStartOrdinal episodeStartLive beforeScan registeredDuring
        0 segments = splitLocatedNoRegisteredSegments nameEq keyEq original
          selected episode registered episodeStartOrdinal episodeStartLive
          beforeScan noRegistered
    in case filterSelectedEpisode nameEq keyEq selected registered
      episodeStartOrdinal episodeStartLive
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))
      (locatedPreStart episode) of
      Nothing => Nothing
      Just episodeFiltered =>
        case filterRegisteredGenerations nameEq keyEq registered
          (episodeEndOrdinal segments) (episodeEndLive segments)
          (traceAfterClosing episode) (survivingFinal episodeFiltered) of
          Nothing => Nothing
          Just suffixFiltered => Just
            (MkDeletionTraceSkeleton segments beforeScan beforeDeletion
              episodeFiltered suffixFiltered)

||| Endpoint facts still to be derived by selected-episode recovery plus the
||| Inactive-leaf suffix invariant. Keeping them in one erased record makes the
||| remaining gap exact and lets endpoint assembly itself typecheck now.
public export
record DeletionEndpointEvidence
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  {original : Transitions initial originalFinal}
  {selected : name}
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original}
  {registered : List (RegistrationGeneration name)}
  {episodeStartOrdinal : Nat}
  {episodeStartLive : GenerationEnvironment name}
  (skeleton : DeletionTraceSkeleton name key world error value nameEq keyEq
    original selected episode registered episodeStartOrdinal episodeStartLive)
  (selectedOutside : (generation : RegistrationGeneration name) ->
    Elem generation registered -> Not (generationName generation = selected)) where
  constructor MkDeletionEndpointEvidence
  0 skeletonEffectsPreserved : EffectStateRelated keyEq
    (projectEffectState @{nameEq} originalFinal)
    (projectEffectState @{nameEq}
      (survivingFinal (suffixSurvivor skeleton)))
  0 skeletonControlsPreserved : ControlEquivalentOutsideGenerations nameEq
    registered (originalFinalLive (splitSegments skeleton)) originalFinal
    (survivingFinal (suffixSurvivor skeleton))
  0 skeletonRegisteredWithdrawn : RegisteredNamesWithdrawn nameEq registered
    (originalFinalLive (splitSegments skeleton)) originalFinal
    (survivingFinal (suffixSurvivor skeleton))

||| Conditional final `DeletionResult` assembly. No theorem strength is lost:
||| the three endpoint fields are exactly the public result's remaining fields.
public export
0 assembleDeletionResult :
  (skeleton : DeletionTraceSkeleton name key world error value nameEq keyEq
    original selected episode registered episodeStartOrdinal episodeStartLive) ->
  (selectedOutside : (generation : RegistrationGeneration name) ->
    Elem generation registered -> Not (generationName generation = selected)) ->
  DeletionEndpointEvidence name key world error value nameEq keyEq skeleton
    selectedOutside ->
  DeletionResult name key world error value nameEq keyEq original selected
    episode registered episodeStartOrdinal episodeStartLive
assembleDeletionResult skeleton selectedOutside endpoint =
  MkDeletionResult selectedOutside
    (locatedPreStart episode)
    (survivingFinal (episodeSurvivor skeleton))
    (survivingFinal (suffixSurvivor skeleton))
    (traceBeforeOpening episode)
    (surviving (episodeSurvivor skeleton))
    (surviving (suffixSurvivor skeleton))
    (skeletonBeforeScan skeleton)
    (episodeEndOrdinal (splitSegments skeleton))
    (episodeEndLive (splitSegments skeleton))
    (episodeScan (splitSegments skeleton))
    (originalFinalOrdinal (splitSegments skeleton))
    (originalFinalLive (splitSegments skeleton))
    (suffixScan (splitSegments skeleton))
    (skeletonBeforeDeletion skeleton)
    (filteredSubsequence (episodeSurvivor skeleton))
    (filteredSubsequence (suffixSurvivor skeleton))
    (skeletonEffectsPreserved endpoint)
    (skeletonControlsPreserved endpoint)
    (skeletonRegisteredWithdrawn endpoint)
