module DGamma.CP4DeletionSelectedForeignLifecycleAnchorReliance

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceCurrent
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceClose
import Data.List.Elem
import Decidable.Equality

%default total

||| The reliance-side provider exclusion used when raw endpoint reuse prevents
||| the selected closing activation from being identified with the final cell.
||| A committed provider name is constant throughout an installed activation.
||| Pairwise provision uniqueness therefore turns any current selected table
||| overlap into a committed reference to `selected`, contradicting the exact
||| selected L-Unload reliance guard at the end of the segment.
public export
0 relianceAnchorProviderExcluded :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq selected
    selectedPre selectedAfter) ->
  (current : SystemState name key value world error) ->
  (toSelectedClose : Transitions current (lastInstalledState episode)) ->
  InstalledTrace name key world error value nameEq keyEq actor toSelectedClose ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry current) = Just currentSelected ->
  lookupFiber @{nameEq} actor (registry current) = Just currentOwner ->
  registryWellFormed @{nameEq} @{keyEq} current = True ->
  SelectedUnloadRelianceAnchor name key world error value nameEq keyEq selected
    actor episode currentOwner ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner))) ->
  providerCandidate @{keyEq} wanted currentSelected = False
relianceAnchorProviderExcluded nameEq keyEq selected actor actorDistinct episode
  current toSelectedClose ownerInstalled currentSelected currentOwner
  selectedFound ownerFound currentWellFormed reliance wanted ownerDeclares
  with (providerCandidate @{keyEq} wanted currentSelected) proof candidate
  relianceAnchorProviderExcluded nameEq keyEq selected actor actorDistinct episode
    current toSelectedClose ownerInstalled currentSelected currentOwner
    selectedFound ownerFound currentWellFormed reliance wanted ownerDeclares |
    False = Refl
  relianceAnchorProviderExcluded nameEq keyEq selected actor actorDistinct episode
    current toSelectedClose ownerInstalled currentSelected currentOwner
    selectedFound ownerFound currentWellFormed reliance wanted ownerDeclares |
    True =
      let 0 committed = selectedCandidateGivesCommittedSnapshot nameEq keyEq
            selected actor wanted current currentSelected currentOwner
            selectedFound ownerFound currentWellFormed
            (installedTraceStart ownerInstalled) ownerDeclares candidate
      in void (committedSelectedContradictsUnload nameEq keyEq selected actor
        actorDistinct wanted episode current toSelectedClose ownerInstalled
        currentOwner committed reliance)
