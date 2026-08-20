module DGamma.Ordering

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality

%default total

record ConsumerEpisodePreparation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (consumer : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) where
  constructor MkConsumerEpisodePreparation
  preparedStartWellFormed : registryWellFormed @{nameEq} @{keyEq}
    (closedStartState (locatedEpisode consumerEpisode)) = True
  preparedInsideAligned : AlignedTransitions name key world error value nameEq keyEq
    (closedInside (locatedEpisode consumerEpisode))

0 alignedLocatedBefore :
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  AlignedTransitions name key world error value nameEq keyEq
    (traceBeforeOpening episode)
alignedLocatedBefore global aligned episode =
  fst (alignedAppendSplit (traceBeforeOpening episode)
    (appendTransitions
      (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
        (closedTransitions (locatedEpisode episode)))
      (traceAfterClosing episode))
    (rewrite (locatedDecomposition episode) in aligned))

0 alignedLocatedCenter :
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
alignedLocatedCenter global aligned episode =
  fst (alignedAppendSplit
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    (traceAfterClosing episode)
    (snd (alignedAppendSplit (traceBeforeOpening episode)
      (appendTransitions
        (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
          (closedTransitions (locatedEpisode episode)))
        (traceAfterClosing episode))
      (rewrite (locatedDecomposition episode) in aligned))))

0 alignedLocatedInside :
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  AlignedTransitions name key world error value nameEq keyEq
    (closedInside (locatedEpisode episode))
alignedLocatedInside global aligned episode =
  fst (alignedAppendSplit (closedInside (locatedEpisode episode))
    (MoreTransitions (unloadTransition (closing (locatedEpisode episode)))
      NoTransitions)
    (alignedEpisodeInside (closedOpening (locatedEpisode episode))
      (closedTransitions (locatedEpisode episode))
      (alignedLocatedCenter global aligned episode)))

public export
0 episodeStartWellFormed :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (consumer : name) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  (episode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  registryWellFormed @{nameEq} @{keyEq}
    (closedStartState (locatedEpisode episode)) = True
episodeStartWellFormed nameEq keyEq consumer global aligned initialWellFormed episode =
  preservationTheoremProof nameEq keyEq (LBegin consumer)
    (locatedPreStart episode) (closedStartState (locatedEpisode episode)) LBeginTag
    (alignedTraceWellFormedEnd nameEq keyEq (traceBeforeOpening episode)
      (alignedLocatedBefore global aligned episode) initialWellFormed)
    (checkedActionProjects nameEq keyEq (LBegin consumer)
      (locatedPreStart episode) (closedStartState (locatedEpisode episode))
      LBeginTag (beginEquation (closedOpening (locatedEpisode episode))))

0 prepareConsumerEpisode :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (consumer : name) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  ConsumerEpisodePreparation name key world error value nameEq keyEq consumer
    global consumerEpisode
prepareConsumerEpisode nameEq keyEq consumer global aligned initialWellFormed episode =
  MkConsumerEpisodePreparation
    (episodeStartWellFormed nameEq keyEq consumer global aligned initialWellFormed
      episode)
    (alignedLocatedInside global aligned episode)

record OrderingCore
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (provider, consumer : name)
  (wanted : key) {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) where
  constructor MkOrderingCore
  coreProvided : value wanted
  coreConsumerResolution : ConsumerResolutionConstant name key world error value
    nameEq keyEq consumer wanted provider
    (closedInside (locatedEpisode consumerEpisode))
  coreProviderValues : ProviderValueConstant name key world error value nameEq keyEq
    provider wanted coreProvided (closedInside (locatedEpisode consumerEpisode))
  coreProviderBeforeInstalled : installedAt @{nameEq} provider
    (locatedPreStart consumerEpisode) = True
  coreProviderAfterInstalled : installedAt @{nameEq} provider
    (locatedAfter consumerEpisode) = True
  coreProviderCenterInstalled : InstalledTrace name key world error value nameEq keyEq
    provider
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode consumerEpisode)))
      (closedTransitions (locatedEpisode consumerEpisode)))

0 buildOrderingCore :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider, consumer : name) -> Not (consumer = provider) -> (wanted : key) ->
  (global : Transitions initial finalState) ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    consumer global) ->
  registryWellFormed @{nameEq} @{keyEq}
    (closedStartState (locatedEpisode consumerEpisode)) = True ->
  AlignedTransitions name key world error value nameEq keyEq
    (closedInside (locatedEpisode consumerEpisode)) ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer wanted provider
    (closedStartState (locatedEpisode consumerEpisode)) = True ->
  OrderingCore name key world error value nameEq keyEq provider consumer wanted
    global consumerEpisode
buildOrderingCore nameEq keyEq provider consumer distinct wanted global
  consumerEpisode startWellFormed insideAligned sourceResolution =
  let providerDistinctConsumer : Not (provider = consumer)
      providerDistinctConsumer = \same => distinct (sym same)
      0 openingRaw : applyAction @{nameEq} @{keyEq} (LBegin consumer)
        (locatedPreStart consumerEpisode) = Just (LBeginTag,
          closedStartState (locatedEpisode consumerEpisode))
      openingRaw = checkedActionProjects nameEq keyEq (LBegin consumer)
        (locatedPreStart consumerEpisode)
        (closedStartState (locatedEpisode consumerEpisode)) LBeginTag
        (beginEquation (closedOpening (locatedEpisode consumerEpisode)))
  in case resolvedProviderData nameEq keyEq consumer wanted provider
       (closedStartState (locatedEpisode consumerEpisode)) startWellFormed
       sourceResolution of
    MkResolvedProviderData providerFiber providerFound providerStable provided
      providerPresent providerStartInstalled =>
      let sourceProviderSnapshot = MkStableProviderValue providerFiber providerFound
            providerStable providerPresent
          providerPreInstalled = trans
            (foreignInstalledStable nameEq keyEq provider (LBegin consumer)
              providerDistinctConsumer (locatedPreStart consumerEpisode)
              (closedStartState (locatedEpisode consumerEpisode)) LBeginTag openingRaw)
            providerStartInstalled
      in case resolvedConsumerSnapshotData nameEq keyEq consumer wanted provider
           (closedStartState (locatedEpisode consumerEpisode)) sourceResolution of
        MkResolvedConsumerSnapshotData providers consumerSnapshot selectedLookup =>
          let consumerResolution = resolvedConstantInstalledTrace nameEq keyEq
                consumer wanted provider providers
                (closedInside (locatedEpisode consumerEpisode))
                (closedInsideInstalled (locatedEpisode consumerEpisode))
                consumerSnapshot selectedLookup
          in case providerValueConstantTrace nameEq keyEq consumer provider wanted
               provided (closedInside (locatedEpisode consumerEpisode)) insideAligned
               startWellFormed consumerResolution sourceProviderSnapshot of
            MkProviderValueTraceResult lastWellFormed lastSnapshot valuesStable
              providerInsideInstalled =>
              let providerLastInstalled = stableValueInstalled nameEq lastSnapshot
                  closingRaw = checkedActionProjects nameEq keyEq
                    (LUnload consumer)
                    (lastInstalledState (locatedEpisode consumerEpisode))
                    (locatedAfter consumerEpisode) LUnloadTag
                    (unloadEquation (closing (locatedEpisode consumerEpisode)))
                  providerAfterInstalled = trans
                    (sym (foreignInstalledStable nameEq keyEq provider
                      (LUnload consumer) providerDistinctConsumer
                      (lastInstalledState (locatedEpisode consumerEpisode))
                      (locatedAfter consumerEpisode) LUnloadTag closingRaw))
                    providerLastInstalled
                  providerClosingInstalled = InstalledStep
                    (LUnload consumer) LUnloadTag
                    (unloadEquation (closing (locatedEpisode consumerEpisode)))
                    NoTransitions providerLastInstalled
                    (InstalledEnd providerAfterInstalled)
                  providerClosedInstalled = appendInstalledTrace
                    (closedInside (locatedEpisode consumerEpisode))
                    (MoreTransitions
                      (unloadTransition (closing (locatedEpisode consumerEpisode)))
                      NoTransitions)
                    providerInsideInstalled providerClosingInstalled
                  providerCenterInstalled = InstalledStep
                    (LBegin consumer) LBeginTag
                    (beginEquation (closedOpening (locatedEpisode consumerEpisode)))
                    (closedTransitions (locatedEpisode consumerEpisode))
                    providerPreInstalled providerClosedInstalled
              in MkOrderingCore provided consumerResolution valuesStable
                providerPreInstalled providerAfterInstalled providerCenterInstalled

||| Proven inhabitant of paper Theorem 63. The proof selects the provider episode
||| by last-opening/first-closing boundary extraction, rather than accepting an
||| unrelated episode as an input.
public export
0 orderingTheoremProof : orderingTheorem name key value world error
orderingTheoremProof nameEq keyEq initial finalState global aligned initialWellFormed
  empty consumer provider distinct wanted providerFinalFalse consumerEpisode
  sourceResolution =
  let preparation = prepareConsumerEpisode nameEq keyEq consumer global aligned
        initialWellFormed consumerEpisode
      providerInitiallyFalse = emptyRegistryUninstalled nameEq provider initial empty
  in case buildOrderingCore nameEq keyEq provider consumer distinct wanted global
       consumerEpisode (preparedStartWellFormed preparation)
       (preparedInsideAligned preparation) sourceResolution of
    MkOrderingCore provided consumerResolution providerValues providerPreInstalled
      providerAfterInstalled providerCenterInstalled =>
      case extractContainingProviderEpisode nameEq keyEq provider consumer global
        aligned consumerEpisode distinct providerInitiallyFalse providerPreInstalled
        providerAfterInstalled providerFinalFalse providerCenterInstalled of
          (providerEpisode ** containment) =>
            let providerDistinctConsumer : Not (provider = consumer)
                providerDistinctConsumer = \same => distinct (sym same)
            in (providerEpisode ** MkOrderingResult providerDistinctConsumer
              containment consumerResolution provided providerValues)
