module DGamma.CP4DeletionSelectedForeignLifecycleCrossing

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Ordering
import DGamma.CP4DeletionCommittedProviderPersistence
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceCurrent
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceResolved
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSelected
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSnapshot
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import Data.List.Elem
import Decidable.Equality

%default total

0 installedTraceEndCrossing :
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq actor trace ->
  installedAt @{nameEq} actor finalState = True
installedTraceEndCrossing NoTransitions (InstalledEnd installed) = installed
installedTraceEndCrossing
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled) =
    installedTraceEndCrossing rest tailInstalled

0 installedFiberCrossing :
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{nameEq} actor state = True ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} actor (registry state) = Just fiber)
installedFiberCrossing nameEq actor state installed
  with (lookupFiber @{nameEq} actor (registry state)) proof found
  installedFiberCrossing nameEq actor state installed | Nothing =
    case installed of Refl impossible
  installedFiberCrossing nameEq actor state installed | Just fiber =
    (fiber ** Refl)

||| Crossing-activation provider exclusion.  If the foreign activation began
||| before the selected activation (or before a selected raw-name reissue), a
||| current selected candidate would have to be the provider already committed
||| by the foreign activation. `committedProviderProvisionPersists` transports
||| that name back to the foreign L-Begin boundary, where it yields exactly the
||| precedence edge forbidden by `NoDependentClosingEpisode`.
|||
||| Operationally this is the reusable form of “a later provisions-disjoint
||| insertion cannot introduce the selected fiber as a provider for a key
||| committed before its insertion”.  It reasons about the committed provider
||| observation rather than trying to distinguish insertion/reissue cases.
public export
0 crossingActivationExcludesSelectedProvider :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq
    keyEq actor global) ->
  (current : SystemState name key value world error) ->
  (activationToCurrent : Transitions
    (closedStartState (locatedEpisode consumerEpisode)) current) ->
  InstalledTrace name key world error value nameEq keyEq actor
    activationToCurrent ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry current) = Just currentSelected ->
  lookupFiber @{nameEq} actor (registry current) = Just currentOwner ->
  registryWellFormed @{nameEq} @{keyEq} current = True ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner))) ->
  providerCandidate @{keyEq} wanted currentSelected = False
crossingActivationExcludesSelectedProvider nameEq keyEq selected actor global
  aligned initialWellFormed noDependent consumerEpisode current
  activationToCurrent ownerInstalled currentSelected currentOwner selectedFound
  ownerFound currentWellFormed wanted ownerDeclares
  with (providerCandidate @{keyEq} wanted currentSelected) proof candidate
  crossingActivationExcludesSelectedProvider nameEq keyEq selected actor global
    aligned initialWellFormed noDependent consumerEpisode current
    activationToCurrent ownerInstalled currentSelected currentOwner selectedFound
    ownerFound currentWellFormed wanted ownerDeclares | False = Refl
  crossingActivationExcludesSelectedProvider nameEq keyEq selected actor global
    aligned initialWellFormed noDependent consumerEpisode current
    activationToCurrent ownerInstalled currentSelected currentOwner selectedFound
    ownerFound currentWellFormed wanted ownerDeclares | True =
      case installedFiberCrossing nameEq actor
        (closedStartState (locatedEpisode consumerEpisode))
        (installedTraceStart ownerInstalled) of
        (openingOwner ** openingFound) =>
          let openingInstalled = installedOwnerCommittedSnapshot nameEq actor
                (closedStartState (locatedEpisode consumerEpisode)) openingOwner
                openingFound (installedTraceStart ownerInstalled)
              currentInstalled = installedOwnerCommittedSnapshot nameEq actor
                current currentOwner ownerFound
                (installedTraceEndCrossing activationToCurrent ownerInstalled)
              currentCommitted = selectedCandidateGivesCommittedSnapshot nameEq
                keyEq selected actor wanted current currentSelected currentOwner
                selectedFound ownerFound currentWellFormed
                (installedTraceEndCrossing activationToCurrent ownerInstalled)
                ownerDeclares candidate
              0 openingSelects : (viewLookup @{keyEq} wanted
                (dependencies (componentDependencies
                  (fiberComponent (committedFiber
                    (installedOwnerSnapshot openingInstalled)))))
                (committedView (installedOwnerSnapshot openingInstalled)) =
                  Just selected)
              openingSelects = committedProviderProvisionPersists nameEq keyEq
                actor wanted selected
                (committedSnapshotProviders openingInstalled)
                (currentCommittedProviders currentCommitted)
                activationToCurrent ownerInstalled
                (installedOwnerSnapshot openingInstalled)
                (currentCommittedSnapshot currentCommitted)
                (currentSnapshotSelects currentCommitted)
              0 openingResolved : (resolvedProviderAt @{nameEq} @{keyEq}
                actor wanted selected
                (closedStartState (locatedEpisode consumerEpisode)) = True)
              openingResolved = snapshotResolvesRelianceAnchor nameEq keyEq
                actor wanted selected (installedOwnerSnapshot openingInstalled)
                openingSelects
              0 openingWellFormed : (registryWellFormed @{nameEq} @{keyEq}
                (closedStartState (locatedEpisode consumerEpisode)) = True)
              openingWellFormed = episodeStartWellFormed nameEq keyEq actor
                global aligned initialWellFormed consumerEpisode
              0 providerData : ResolvedProviderData name key world error value
                nameEq keyEq actor wanted selected
                (closedStartState (locatedEpisode consumerEpisode))
              providerData = resolvedProviderData nameEq keyEq actor wanted
                selected (closedStartState (locatedEpisode consumerEpisode))
                openingWellFormed openingResolved
              0 selectedDeclares : Elem wanted (dependencies
                (componentProvisions
                  (fiberComponent (resolvedProviderFiber providerData))))
              selectedDeclares = resolvedProviderDeclaresRelianceAnchor nameEq
                keyEq selected wanted
                (closedStartState (locatedEpisode consumerEpisode)) providerData
              0 ownerComponent : (fiberComponent currentOwner =
                fiberComponent openingOwner)
              ownerComponent = installedTracePreservesComponent nameEq keyEq
                actor activationToCurrent ownerInstalled openingOwner currentOwner
                openingFound ownerFound
              0 openingOwnerDeclares : Elem wanted (dependencies
                (componentDependencies (fiberComponent openingOwner)))
              openingOwnerDeclares = replace
                {p = \component => Elem wanted
                  (dependencies (componentDependencies component))}
                ownerComponent ownerDeclares
              0 edge : PrecedenceEdge nameEq selected actor
                (closedStartState (locatedEpisode consumerEpisode))
              edge = MkPrecedenceEdge wanted (resolvedProviderFiber providerData)
                openingOwner (resolvedProviderLookup providerData) openingFound
                selectedDeclares openingOwnerDeclares
          in void (noDependent actor consumerEpisode edge)
