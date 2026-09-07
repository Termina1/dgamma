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

||| Membership in the inverse-mapped operational target order, with the
||| selected name recovered using the same bijection's left inverse.
export
0 canonicalPairInverseMember :
  {name : Type} -> (renaming : NameBijection name) -> (selected : name) -> (order : List name) ->
  Elem (renameForward renaming selected) order ->
  Elem selected (map (renameBackward renaming) order)
canonicalPairInverseMember renaming selected (_ :: rest) Here =
  replace {p = \actor => Elem actor
    (map (renameBackward renaming) (renameForward renaming selected :: rest))}
    (renameLeftInverse renaming selected) Here
canonicalPairInverseMember renaming selected (head :: rest) (There later) =
  There (canonicalPairInverseMember renaming selected rest later)

||| Authoritative paired block SELECTION in the actual operational-left and
||| right-canonical executions. This asserts no effects/control/view agreement.
||| Equality fields pin both ranges to their original capital, not lookalikes.
public export
record SelectedCanonicalBlockPair
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal) (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace)
  (matching : MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq leftTrace rightTrace
    (expectedBridgeBijection sameInputs) (canonicalSchedule leftCapital) (canonicalSchedule rightCapital))
  (operational : CertifiedOperationalCanonicalPermutation name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital matching)
  (selected : name) where
  constructor MkSelectedCanonicalBlockPair
  0 pairSelectedSupported : isSupported @{nameEq} @{keyEq} selected leftFinal = True
  0 pairRightInCanonicalOrder : Elem (renameForward (expectedBridgeBijection sameInputs) selected)
    (supportOrder (canonicalSchedule rightCapital))
  0 pairLeftInOperationalOrder : Elem selected
    (map (renameBackward (expectedBridgeBijection sameInputs)) (supportOrder (canonicalSchedule rightCapital)))
  pairLeftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected
    (operationalTargetTrace operational)
  pairRightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    (renameForward (expectedBridgeBijection sameInputs) selected) (canonicalTrace (canonicalSchedule rightCapital))
  0 pairLeftBlockChosen : pairLeftBlock =
    decomposedBlock (operationalTargetBlocks operational) selected pairLeftInOperationalOrder
  0 pairRightBlockChosen : pairRightBlock =
    decomposedBlock (canonicalActorBlockDecomposition rightCapital)
      (renameForward (expectedBridgeBijection sameInputs) selected) pairRightInCanonicalOrder
