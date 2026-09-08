module DGamma.CP5O20CanonicalPairedExtractionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

import DGamma.CP5O20CanonicalPairSelectionSpike
import DGamma.CP5O20PairedExecutionSpike

%default total
%unbound_implicits off

||| Extract BOTH actual Begin edges at the selected physical canonical cuts.
||| No pre-cut agreement or actual-stage witness is a caller premise.
||| This owns the Begin stage, not whole paired execution alignment.
export
0 o20SelectedCanonicalBeginStage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} -> {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace} ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching} ->
  {selected : name} ->
  (pair : SelectedCanonicalBlockPair name key world error value protocol nameEq keyEq leftTrace rightTrace
    sameInputs leftCapital rightCapital matching operational selected) ->
  O20PairedStage name key world error value nameEq keyEq (expectedBridgeBijection sameInputs)
    (blockPreStart (pairLeftBlock pair)) (blockPreStart (pairRightBlock pair))
    (blockStart (pairLeftBlock pair)) (blockStart (pairRightBlock pair))
o20SelectedCanonicalBeginStage {name} {key} {world} {error} {value} {sameInputs} {selected}
  nameEq keyEq pair =
    PairedBeginStage nameEq keyEq (expectedBridgeBijection sameInputs) selected
      (blockPreStart (pairLeftBlock pair)) (blockStart (pairLeftBlock pair))
      (blockPreStart (pairRightBlock pair)) (blockStart (pairRightBlock pair))
      (blockOpening (pairLeftBlock pair)) (blockOpening (pairRightBlock pair))
      (registryWellFormedPairwiseOpenAnchor {name} {key} {value} {world} {error}
        nameEq keyEq (blockPreStart (pairRightBlock pair))
        (Builtin.snd (canonicalPairCutsWellFormed nameEq keyEq pair)))
