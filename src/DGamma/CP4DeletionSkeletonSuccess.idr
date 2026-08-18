module DGamma.CP4DeletionSkeletonSuccess

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionPremiseSplit
import DGamma.CP4DeletionSkeleton
import Data.List.Elem
import Decidable.Equality

%default total

||| Proof-driven, non-`Maybe` counterpart of `buildDeletionTraceSkeleton`.
||| Its two readiness arguments are exactly the remaining cross-boundary
||| applicability invariant. Both executable filters are run by the proved
||| success specializations, so this does not hand-construct a parallel trace.
public export
0 deletionReplayReadyGivesTraceSkeleton :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (original : Transitions initial originalFinal) ->
  (selected : name) ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original) ->
  (registered : List (RegistrationGeneration name)) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  (beforeScan : GenerationTraceScan nameEq 0 [] (traceBeforeOpening episode)
    episodeStartOrdinal episodeStartLive) ->
  (registeredDuring : RegisteredGenerationsDuring selected episodeStartOrdinal
    registered
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))) ->
  (noRegistered : NoRegisteredEpisode nameEq registered 0 [] original) ->
  GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    episodeStartOrdinal episodeStartLive
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    (locatedPreStart episode) ->
  ((endOrdinal : Nat) -> (endLive : GenerationEnvironment name) ->
    GenerationTraceScan nameEq episodeStartOrdinal episodeStartLive
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode))) endOrdinal endLive ->
    (episodeFiltered : GenerationFilterResult name key world error value nameEq
      (EpisodeGenerationDeletedActor nameEq selected registered)
      episodeStartOrdinal episodeStartLive
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))
      (locatedPreStart episode)) ->
    GenerationReplayReady nameEq keyEq
      (GenerationOwnedActor nameEq registered) endOrdinal endLive
      (traceAfterClosing episode) (survivingFinal episodeFiltered)) ->
  DeletionTraceSkeleton name key world error value nameEq keyEq original selected
    episode registered episodeStartOrdinal episodeStartLive
deletionReplayReadyGivesTraceSkeleton nameEq keyEq original selected episode
  registered episodeStartOrdinal episodeStartLive beforeScan registeredDuring
  noRegistered episodeReady suffixReady =
    let 0 beforeDeletion = deletionBeforeFromRegisteredDuring nameEq selected
          registered (traceBeforeOpening episode)
          (MoreTransitions
            (beginTransition (closedOpening (locatedEpisode episode)))
            (closedTransitions (locatedEpisode episode)))
          episodeStartOrdinal episodeStartLive beforeScan registeredDuring
        0 segments = splitLocatedNoRegisteredSegments nameEq keyEq original selected
          episode registered episodeStartOrdinal episodeStartLive beforeScan
          noRegistered
    in case selectedEpisodeReplayReadyGivesFilterSuccess nameEq keyEq selected
      registered episodeStartOrdinal episodeStartLive
      (MoreTransitions
        (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))
      (locatedPreStart episode) episodeReady of
      MkGenerationFilterSucceeded episodeFiltered episodeEquation =>
        case registeredGenerationReplayReadyGivesFilterSuccess nameEq keyEq
          registered (episodeEndOrdinal segments) (episodeEndLive segments)
          (traceAfterClosing episode) (survivingFinal episodeFiltered)
          (suffixReady (episodeEndOrdinal segments) (episodeEndLive segments)
            (episodeScan segments) episodeFiltered) of
          MkGenerationFilterSucceeded suffixFiltered suffixEquation =>
            MkDeletionTraceSkeleton segments beforeScan beforeDeletion
              episodeFiltered suffixFiltered
