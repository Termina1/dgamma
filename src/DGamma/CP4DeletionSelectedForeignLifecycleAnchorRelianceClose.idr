module DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceClose

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSnapshot
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceObservation
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceCurrent
import Decidable.Equality

%default total

0 falseNotTrueRelianceClose : False = True -> Void
falseNotTrueRelianceClose Refl impossible

0 installedTraceEndRelianceClose :
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq actor trace ->
  installedAt @{nameEq} actor finalState = True
installedTraceEndRelianceClose NoTransitions (InstalledEnd installed) = installed
installedTraceEndRelianceClose
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled) =
    installedTraceEndRelianceClose rest tailInstalled

||| A committed reference to the selected name persists across the complete
||| installed segment and therefore contradicts the selected L-Unload head
||| observation stored by `SelectedUnloadRelianceAnchor`.
public export
0 committedSelectedContradictsUnload :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) -> (wanted : key) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    selectedPre selectedAfter) ->
  (current : SystemState name key value world error) ->
  (toSelectedClose : Transitions current (lastInstalledState episode)) ->
  InstalledTrace name key world error value nameEq keyEq actor toSelectedClose ->
  (currentOwner : Fiber name key value world error) ->
  (committed : CurrentSelectedCommittedSnapshot name key world error value
    nameEq keyEq selected actor wanted current currentOwner) ->
  SelectedUnloadRelianceAnchor name key world error value nameEq keyEq selected
    actor episode currentOwner ->
  Void
committedSelectedContradictsUnload nameEq keyEq selected actor actorDistinct
  wanted episode current toSelectedClose ownerInstalled currentOwner committed
  reliance =
    let 0 constant = resolvedConstantInstalledTrace nameEq keyEq actor wanted
          selected (currentCommittedProviders committed) toSelectedClose
          ownerInstalled (currentCommittedSnapshot committed)
          (currentSnapshotSelects committed)
        0 closingResolved : (resolvedProviderAt @{nameEq} @{keyEq}
          {name = name} {key = key} {value = value} {world = world}
          {error = error} actor wanted selected (lastInstalledState episode) =
            True)
        closingResolved = consumerResolutionEndRelianceAnchor toSelectedClose
          constant
        0 closingInstalled : InstalledCommittedSnapshot name key world error
          value nameEq actor (lastInstalledState episode)
          (selectedUnloadOwner reliance)
        closingInstalled = installedOwnerCommittedSnapshot nameEq actor
          (lastInstalledState episode) (selectedUnloadOwner reliance)
          (selectedUnloadOwnerFound reliance)
          (installedTraceEndRelianceClose toSelectedClose ownerInstalled)
    in let 0 closingLookup = snapshotLookupFromResolvedRelianceAnchor nameEq
             keyEq actor wanted selected
             (installedOwnerSnapshot closingInstalled) closingResolved
           0 closingContains = viewLookupImpliesContainsRelianceAnchor nameEq
             keyEq wanted
             (dependencies (componentDependencies
               (fiberComponent (committedFiber
                 (installedOwnerSnapshot closingInstalled)))))
             (committedView (installedOwnerSnapshot closingInstalled)) selected
             closingLookup
           0 closingHeadTrue = reliedHeadFromSnapshotRelianceAnchor nameEq
             selected actor actorDistinct
             (installedOwnerSnapshot closingInstalled) closingContains
           0 anchoredHeadTrue : (reliedHead @{nameEq} selected selected
             (Bind actor (selectedUnloadOwner reliance)) = True)
           anchoredHeadTrue = replace
             {p = \fiber => reliedHead @{nameEq} selected selected
               (Bind actor fiber) = True}
             (installedSnapshotOwner closingInstalled) closingHeadTrue
       in falseNotTrueRelianceClose
         (trans (sym (selectedUnloadOwnerDoesNotRely reliance))
           anchoredHeadTrue)
