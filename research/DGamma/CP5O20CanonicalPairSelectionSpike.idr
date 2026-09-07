module DGamma.CP5O20CanonicalPairSelectionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Derive membership of the supported actor's image in the ACTUAL right
||| canonical enumeration, using the fixed accepted matching. No renaming or
||| replacement execution is selected by this helper.
export
0 canonicalPairRightMember :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) -> (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital) ->
  (selected : name) -> (isSupported @{nameEq} @{keyEq} selected leftFinal = True) ->
  Elem (renameForward (expectedBridgeBijection sameInputs) selected) (supportOrder (canonicalSchedule rightCapital))
canonicalPairRightMember nameEq keyEq protocol leftTrace rightTrace sameInputs
  leftCapital rightCapital matching selected supported =
    leftSupportMapped matching selected
      (orderComplete (supportLinearization (canonicalSchedule leftCapital)) selected supported)
