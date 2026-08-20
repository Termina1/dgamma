module DGamma.CP4DeletionCommittedProviderPersistence

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality

%default total

0 justInjectiveCommittedPersistence : Just left = Just right -> left = right
justInjectiveCommittedPersistence Refl = Refl

||| A provider selected by an installed consumer's committed view at a later
||| point was already selected by that same activation at every earlier point.
||| In particular, a provisions-disjoint insertion cannot manufacture a new
||| selected provider inside an activation: the checked-step preservation used
||| below keeps the committed provider list and component fixed, while O-Insert
||| can only extend the surrounding registry.
|||
||| This is stated backwards because the crossing-activation proof discovers
||| the candidate at the retained lifecycle occurrence and must transport that
||| observation to the consumer's L-Begin boundary.
public export
0 committedProviderProvisionPersists :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (consumer : name) -> (wanted : key) -> (provider : name) ->
  (providers : List name) ->
  (trace : Transitions first finalState) ->
  (installed : InstalledTrace name key world error value nameEq keyEq consumer
    trace) ->
  (firstSnapshot : CommittedSnapshot name key world error value nameEq consumer
    providers first) ->
  (finalSnapshot : CommittedSnapshot name key world error value nameEq consumer
    providers finalState) ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber finalSnapshot))))
    (committedView finalSnapshot) = Just provider ->
  viewLookup @{keyEq} wanted
    (dependencies (componentDependencies
      (fiberComponent (committedFiber firstSnapshot))))
    (committedView firstSnapshot) = Just provider
committedProviderProvisionPersists nameEq keyEq consumer wanted provider
  providers NoTransitions (InstalledEnd installed) firstSnapshot finalSnapshot
  finalResolved =
    let 0 sameFiber : (committedFiber finalSnapshot = committedFiber firstSnapshot)
        sameFiber = justInjectiveCommittedPersistence
          (trans (sym (committedLookup finalSnapshot))
            (committedLookup firstSnapshot))
        0 componentSame : (fiberComponent (committedFiber firstSnapshot) =
          fiberComponent (committedFiber finalSnapshot))
        componentSame = cong fiberComponent (sym sameFiber)
    in snapshotResolvedLookupStable wanted provider finalSnapshot firstSnapshot
      componentSame finalResolved
committedProviderProvisionPersists nameEq keyEq consumer wanted provider
  providers
  (MoreTransitions transition@(Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled)
  firstSnapshot finalSnapshot finalResolved =
    let 0 raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        0 targetInstalled = installedTraceStart tailInstalled
        0 afterCommitted = case decEq @{nameEq} consumer (actionOwner action) of
          No distinct => committedProvidersForeignAction nameEq keyEq consumer
            providers action _ _ tag distinct
            (committedSnapshotEquation firstSnapshot) raw
          Yes same => committedProvidersSelectedAction nameEq keyEq consumer
            providers action _ _ tag (sym same) firstSnapshot targetInstalled raw
        middleSnapshot = committedSnapshotFrom nameEq consumer providers _
          afterCommitted
        0 middleResolved = committedProviderProvisionPersists nameEq keyEq
          consumer wanted provider providers rest tailInstalled middleSnapshot
          finalSnapshot finalResolved
        0 replacement = installedCheckedStepStaticReplacement nameEq keyEq
          consumer action tag _ _ checked sourceInstalled targetInstalled
        0 componentStable = snapshotComponentStable firstSnapshot middleSnapshot
          replacement
    in snapshotResolvedLookupStable wanted provider middleSnapshot firstSnapshot
      (sym componentStable) middleResolved
