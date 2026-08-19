module DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceCurrent

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSnapshot
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceResolved
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSelected
import Data.List.Elem
import Decidable.Equality

%default total

public export
record CurrentSelectedCommittedSnapshot
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (selected, actor : name) (wanted : key)
  (current : SystemState name key value world error)
  (currentOwner : Fiber name key value world error) where
  constructor MkCurrentSelectedCommittedSnapshot
  currentCommittedProviders : List name
  currentCommittedSnapshot : CommittedSnapshot name key world error value nameEq
    actor currentCommittedProviders current
  0 currentSnapshotOwner : committedFiber currentCommittedSnapshot = currentOwner
  0 currentSnapshotSelects : viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber currentCommittedSnapshot))))
    (committedView currentCommittedSnapshot) = Just selected

||| In a well-formed current registry, pairwise provision uniqueness identifies
||| an active selected provider with the intrinsically total provider stored in
||| the foreign owner's committed view.
public export
0 selectedCandidateGivesCommittedSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> (wanted : key) ->
  (current : SystemState name key value world error) ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry current) = Just currentSelected ->
  lookupFiber @{nameEq} actor (registry current) = Just currentOwner ->
  registryWellFormed @{nameEq} @{keyEq} current = True ->
  installedAt @{nameEq} actor current = True ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner))) ->
  providerCandidate @{keyEq} wanted currentSelected = True ->
  CurrentSelectedCommittedSnapshot name key world error value nameEq keyEq
    selected actor wanted current currentOwner
selectedCandidateGivesCommittedSnapshot nameEq keyEq selected actor wanted
  current currentSelected currentOwner selectedFound ownerFound currentWellFormed
  ownerInstalled ownerDeclares candidate =
    case installedOwnerCommittedSnapshot nameEq actor current currentOwner
      ownerFound ownerInstalled of
      installedSnapshot =>
        case viewLookupFromElemRelianceAnchor keyEq wanted
          (dependencies (componentDependencies (fiberComponent
            (committedFiber (installedOwnerSnapshot installedSnapshot)))))
          (committedView (installedOwnerSnapshot installedSnapshot))
          (replace
            {p = \component => Elem wanted (dependencies
              (componentDependencies component))}
            (sym (cong fiberComponent
              (installedSnapshotOwner installedSnapshot))) ownerDeclares) of
          (committedProvider ** committedLookup) =>
            let 0 sourceResolved : (resolvedProviderAt @{nameEq} @{keyEq}
                  {name = name} {key = key} {value = value} {world = world}
                  {error = error} actor wanted committedProvider current = True)
                sourceResolved = snapshotResolvesRelianceAnchor nameEq keyEq
                  actor wanted committedProvider
                  (installedOwnerSnapshot installedSnapshot) committedLookup
                0 providerData : ResolvedProviderData name key world error value
                  nameEq keyEq actor wanted committedProvider current
                providerData = resolvedProviderData nameEq keyEq actor wanted
                  committedProvider current currentWellFormed sourceResolved
                0 selectedDeclares : Elem wanted (dependencies
                  (componentProvisions (fiberComponent currentSelected)))
                selectedDeclares = selectedCandidateDeclaresRelianceAnchor
                  keyEq wanted currentSelected candidate
                0 providerDeclares : Elem wanted (dependencies
                  (componentProvisions (fiberComponent
                    (resolvedProviderFiber providerData))))
                providerDeclares = resolvedProviderDeclaresRelianceAnchor
                  nameEq keyEq committedProvider wanted current providerData
                0 pairwise : (pairwiseProvisionInvariant @{keyEq}
                  {name = name} {key = key} {value = value} {world = world}
                  {error = error}
                  (registryFibers {value = value} {world = world}
                    {error = error} (registry current)) = True)
                pairwise = registryWellFormedPairwiseOpenAnchor nameEq keyEq
                  current currentWellFormed
                0 selectedEntry : Elem (Bind selected currentSelected)
                  (registryFibers {value = value} {world = world}
                    {error = error} (registry current))
                selectedEntry = lookupEntryElemOpenAnchor nameEq selected
                  (registryFibers {value = value} {world = world}
                    {error = error} (registry current)) currentSelected
                  (lookupFiberEntries nameEq selected currentSelected
                    (registry current) selectedFound)
                0 providerEntry : Elem
                  (Bind committedProvider (resolvedProviderFiber providerData))
                  (registryFibers {value = value} {world = world}
                    {error = error} (registry current))
                providerEntry = lookupEntryElemOpenAnchor nameEq
                  committedProvider
                  (registryFibers {value = value} {world = world}
                    {error = error} (registry current))
                  (resolvedProviderFiber providerData)
                  (lookupFiberEntries nameEq committedProvider
                    (resolvedProviderFiber providerData) (registry current)
                    (resolvedProviderLookup providerData))
                0 selectedIsCommitted : selected = committedProvider
                selectedIsCommitted = pairwiseSharedProvisionSameName keyEq
                  (registryFibers {value = value} {world = world}
                    {error = error} (registry current)) pairwise selected
                  committedProvider currentSelected
                  (resolvedProviderFiber providerData) selectedEntry
                  providerEntry wanted selectedDeclares providerDeclares
                0 selectedLookup : viewLookup @{keyEq} wanted
                  (dependencies (componentDependencies
                    (fiberComponent (committedFiber
                      (installedOwnerSnapshot installedSnapshot)))))
                  (committedView (installedOwnerSnapshot installedSnapshot)) =
                    Just selected
                selectedLookup = replace
                  {p = \provider => viewLookup @{keyEq} wanted
                    (dependencies (componentDependencies
                      (fiberComponent (committedFiber
                        (installedOwnerSnapshot installedSnapshot)))))
                    (committedView (installedOwnerSnapshot installedSnapshot)) =
                      Just provider}
                  (sym selectedIsCommitted) committedLookup
            in MkCurrentSelectedCommittedSnapshot
              (committedSnapshotProviders installedSnapshot)
              (installedOwnerSnapshot installedSnapshot)
              (installedSnapshotOwner installedSnapshot) selectedLookup
