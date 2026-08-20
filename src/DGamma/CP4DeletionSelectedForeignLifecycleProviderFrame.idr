module DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorReliance
import DGamma.CP4DeletionSelectedForeignLifecycleFrame
import Data.List.Elem
import Decidable.Equality

%default total

||| The two constructive reasons a retained foreign lifecycle occurrence cannot
||| observe the selected activation as a provider. The precedence case includes
||| both a closing consumer and the Lemma-70 Active endpoint constructor. The
||| reliance case is anchored at the selected episode's own L-Unload source and
||| remains valid across later raw-name reuse.
public export
data ForeignLifecycleProviderFrameEvidence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (selected, actor : name) ->
  (current : SystemState name key value world error) ->
  (currentSelected, currentOwner : Fiber name key value world error) -> Type where
  PrecedenceProviderFrameEvidence :
    ForeignLifecyclePrecedenceAnchor name key world error value nameEq keyEq
      global selected actor currentSelected currentOwner ->
    ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
      global selected actor current currentSelected currentOwner
  RelianceProviderFrameEvidence :
    {selectedPre, selectedAfter : SystemState name key value world error} ->
    (episode : ClosedEpisode name key world error value nameEq keyEq selected
      selectedPre selectedAfter) ->
    (toSelectedClose : Transitions current (lastInstalledState episode)) ->
    InstalledTrace name key world error value nameEq keyEq actor
      toSelectedClose ->
    lookupFiber @{nameEq} selected (registry current) = Just currentSelected ->
    lookupFiber @{nameEq} actor (registry current) = Just currentOwner ->
    registryWellFormed @{nameEq} @{keyEq} current = True ->
    SelectedUnloadRelianceAnchor name key world error value nameEq keyEq
      selected actor episode currentOwner ->
    ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
      global selected actor current currentSelected currentOwner

||| Eliminate either provider-frame reason to the one Boolean observation used
||| by the ordered source relation.
public export
0 lifecycleProviderFrameExcludesSelected :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (global : Transitions initial finalState) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq}
    selected global ->
  (current : SystemState name key value world error) ->
  (currentSelected, currentOwner : Fiber name key value world error) ->
  ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
    global selected actor current currentSelected currentOwner ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent currentOwner))) ->
  providerCandidate @{keyEq} wanted currentSelected = False
lifecycleProviderFrameExcludesSelected nameEq keyEq selected actor actorDistinct
  global noDependent current currentSelected currentOwner
  (PrecedenceProviderFrameEvidence anchor) wanted ownerDeclares =
    selectedProviderExcludedByNoDependent nameEq keyEq selected actor global
      noDependent currentSelected currentOwner anchor wanted ownerDeclares
lifecycleProviderFrameExcludesSelected nameEq keyEq selected actor actorDistinct
  global noDependent current currentSelected currentOwner
  (RelianceProviderFrameEvidence episode toSelectedClose ownerInstalled
    selectedFound ownerFound currentWellFormed reliance)
  wanted ownerDeclares = relianceAnchorProviderExcluded nameEq keyEq selected
    actor actorDistinct episode current toSelectedClose ownerInstalled
    currentSelected currentOwner selectedFound ownerFound currentWellFormed
    reliance wanted ownerDeclares

||| Build the saturated ordered guard frame from an already proved selected
||| provider exclusion. This factorization lets both the Lemma-70/precedence and
||| L-Unload-reliance branches share exactly the same runtime/control assembly.
public export
0 foreignLifecycleGuardFrameFromProviderExclusion :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (leftOwner, rightOwner, leftSelected : Fiber name key value world error) ->
  (left, right : Registry name key value world error) ->
  lookupFiber @{nameEq} selected left = Just leftSelected ->
  lookupFiber @{nameEq} actor left = Just leftOwner ->
  lookupFiber @{nameEq} actor right = Just rightOwner ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    (MkSystemState ambient right) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings left) (bindings right) ->
  ((current : name) -> Not (current = selected) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    Elem (Bind current leftFiber) (bindings left) ->
    Elem (Bind current rightFiber) (bindings right) ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber))) ->
  ((wanted : key) -> Elem wanted (dependencies
    (componentDependencies (fiberComponent leftOwner))) ->
    providerCandidate @{keyEq} wanted leftSelected = False) ->
  ForeignLifecycleGuardFrame name key world error value nameEq keyEq selected
    actor (dependencies (componentDependencies (fiberComponent leftOwner)))
    leftOwner rightOwner left right
foreignLifecycleGuardFrameFromProviderExclusion nameEq keyEq selected actor
  actorDistinct leftOwner rightOwner leftSelected left right selectedFound
  ownerLeftFound ownerRightFound
  (SelectedCleanInactiveWitness cleanComponent cleanParent cleanRetired cleanTable
    cleanFound)
  ordered foreignTables selectedExcluded =
    let 0 sources : ForeignLifecycleOrderedSourcesRelated name key world error
          value nameEq keyEq selected
          (dependencies (componentDependencies (fiberComponent leftOwner)))
          (bindings left) (bindings right)
        sources = buildForeignLifecycleSources nameEq keyEq selected
          (dependencies (componentDependencies (fiberComponent leftOwner)))
          leftSelected cleanComponent cleanParent cleanRetired cleanTable
          (bindings left) (bindings right) (uniqueBindings left)
          (uniqueBindings right)
          (trans (sym (lookupFiberAsEntries nameEq selected left)) selectedFound)
          (trans (sym (lookupFiberAsEntries nameEq selected right)) cleanFound)
          selectedExcluded foreignTables ordered
        0 maybeOwnerControls : FiberControlMaybeRelated
          {name = name} {key = key} {value = value} {world = world}
          {error = error}
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor left)
          (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor right)
        maybeOwnerControls = selectedOrderedForeignLookupControls nameEq selected
          actor actorDistinct left right ordered
        0 leftReindexed : FiberControlMaybeRelated
          (Just leftOwner) (lookupFiber @{nameEq} actor right)
        leftReindexed = replace
          {p = \observed => FiberControlMaybeRelated observed
            (lookupFiber @{nameEq} actor right)}
          ownerLeftFound maybeOwnerControls
        0 exactOwnerControls : FiberControlMaybeRelated
          (Just leftOwner) (Just rightOwner)
        exactOwnerControls = replace
          {p = \observed => FiberControlMaybeRelated (Just leftOwner) observed}
          ownerRightFound leftReindexed
        0 controls : FiberControlRelated leftOwner rightOwner
        controls = exactFiberControlsFromMaybe exactOwnerControls
        0 relianceFrame :
          relied @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor left = False ->
          relied @{nameEq} {name = name} {key = key} {value = value}
            {world = world} {error = error} actor right = False
        relianceFrame leftFalse =
          foreignLifecycleSourcesPreserveFalseReliance nameEq actor
            (bindings left) (bindings right) sources leftFalse
    in MkForeignLifecycleGuardFrame sources controls relianceFrame

||| The provider-frame join consumed by retained lifecycle replay. It selects
||| the exact trace reason above and then saturates the ordered source relation;
||| no endpoint raw-name identity or registry equality is assumed.
public export
0 foreignLifecycleGuardFrameFromEvidence :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (global : Transitions initial finalState) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq}
    selected global ->
  (ambientLeft : world) ->
  (leftOwner, rightOwner, leftSelected : Fiber name key value world error) ->
  (left, right : Registry name key value world error) ->
  lookupFiber @{nameEq} selected left = Just leftSelected ->
  lookupFiber @{nameEq} actor left = Just leftOwner ->
  lookupFiber @{nameEq} actor right = Just rightOwner ->
  ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
    global selected actor (MkSystemState ambientLeft left) leftSelected leftOwner ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    (MkSystemState ambientRight right) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings left) (bindings right) ->
  ((current : name) -> Not (current = selected) ->
    {leftFiber, rightFiber : Fiber name key value world error} ->
    Elem (Bind current leftFiber) (bindings left) ->
    Elem (Bind current rightFiber) (bindings right) ->
    FiberControlRelated leftFiber rightFiber ->
    bindings (ownedValues (fiberTable leftFiber)) =
      bindings (ownedValues (fiberTable rightFiber))) ->
  ForeignLifecycleGuardFrame name key world error value nameEq keyEq selected
    actor (dependencies (componentDependencies (fiberComponent leftOwner)))
    leftOwner rightOwner left right
foreignLifecycleGuardFrameFromEvidence nameEq keyEq selected actor actorDistinct
  global noDependent ambientLeft leftOwner rightOwner leftSelected left right
  selectedFound ownerLeftFound ownerRightFound evidence cleanInactive ordered
  foreignTables =
    let 0 selectedExcluded = lifecycleProviderFrameExcludesSelected nameEq keyEq
          selected actor actorDistinct global noDependent
          (MkSystemState ambientLeft left) leftSelected leftOwner evidence
    in foreignLifecycleGuardFrameFromProviderExclusion nameEq keyEq selected actor
      actorDistinct leftOwner rightOwner leftSelected left right selectedFound
      ownerLeftFound ownerRightFound cleanInactive ordered foreignTables
      selectedExcluded
