module DGamma.CP5ConfluenceCrossTraceSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total

||| One certified adjacent swap of incomparable *supported* names in the right
||| endpoint partial order.
public export
record IncomparableAdjacentOrderSwap
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error)
  (before, after : List name) where
  constructor MkIncomparableAdjacentOrderSwap
  swapPrefix : List name
  swapLeft : name
  swapRight : name
  swapSuffix : List name
  0 swapBeforeExact : before =
    swapPrefix ++ (swapLeft :: swapRight :: swapSuffix)
  0 swapAfterExact : after =
    swapPrefix ++ (swapRight :: swapLeft :: swapSuffix)
  0 swapLeftSupported : isSupported @{nameEq} swapLeft state = True
  0 swapRightSupported : isSupported @{nameEq} swapRight state = True
  0 swapNamesDistinct : Not (swapLeft = swapRight)
  0 swapLeftNotBelowRight : SupportPath nameEq state swapLeft swapRight -> Void
  0 swapRightNotBelowLeft : SupportPath nameEq state swapRight swapLeft -> Void

||| A concrete supported-order sequence, not a bare list permutation.
public export
data CertifiedIncomparablePermutation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  List name -> List name -> Type where
  PermutationDone : CertifiedIncomparablePermutation name key world error value
    nameEq keyEq state order order
  PermutationStep :
    IncomparableAdjacentOrderSwap name key world error value nameEq keyEq state
      before middle ->
    CertifiedIncomparablePermutation name key world error value nameEq keyEq state
      middle after ->
    CertifiedIncomparablePermutation name key world error value nameEq keyEq state
      before after

||| Mapped capital is deliberately restricted to actual support orders.  It no
||| longer maps arbitrary `SupportPath`s whose endpoints/intermediates may be
||| unsupported vestigials.  Instead it certifies directly that the mapped left
||| order is another `LinearizesSupport` value for the right endpoint—the exact
||| common partial-order fact consumed by the adjacent-permutation theorem.
public export
record MappedCanonicalSupportOrders
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (renaming : NameBijection name)
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace)
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) where
  constructor MkMappedCanonicalSupportOrders
  0 leftSupportMapped : (n : name) -> Elem n (supportOrder leftSchedule) ->
    Elem (renameForward renaming n) (supportOrder rightSchedule)
  0 rightSupportMapped : (n : name) -> Elem n (supportOrder rightSchedule) ->
    Elem (renameBackward renaming n) (supportOrder leftSchedule)
  0 mappedSupportDistinct : (left, right : name) ->
    Elem left (supportOrder leftSchedule) ->
    Elem right (supportOrder leftSchedule) ->
    Not (left = right) ->
    Not (renameForward renaming left = renameForward renaming right)
  mappedLeftOrderLinearizesRight : LinearizesSupport name key world error value
    nameEq keyEq rightFinal
    (map (renameForward renaming) (supportOrder leftSchedule))
  mappedOrderPermutation : CertifiedIncomparablePermutation name key world error
    value nameEq keyEq rightFinal
    (map (renameForward renaming) (supportOrder leftSchedule))
    (supportOrder rightSchedule)

||| The matching theorem consumes simultaneous one-trace capitals, not opaque
||| public schedules.  Vestigial endpoint names are absent from both support
||| orders and impose no unrestricted path-transport obligation.
public export
0 canonicalSupportOrdersMatchSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq
    leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
canonicalSupportOrdersMatchSpike = ?canonicalSupportOrdersMatchSpike_rhs

||| Operational output of the certified permutation.  The source canonical
||| bundle is available from `leftCapital`; each recursive `AdjacentSwapResult`
||| returns the bundle consumed by the next step, and the final bundle and replay
||| correspondence are retained here with the bridge.
public export
record CanonicalConvergenceResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  (mapped : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) where
  constructor MkCanonicalConvergenceResult
  permutedLeftFinal : SystemState name key value world error
  permutedLeftTrace : Transitions initial permutedLeftFinal
  permutationReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value (canonicalTrace (canonicalSchedule leftCapital)) permutedLeftTrace
  permutationReplayPremises : ReplayInvariantBundle name key world error value
    protocol nameEq keyEq permutedLeftTrace
  permutationSameExternalInputs : SameExternalOrchestration nameEq
    (canonicalTrace (canonicalSchedule leftCapital)) permutedLeftTrace
  convergenceBridge : CanonicalEndpointBridge name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs (canonicalSchedule leftCapital)
      (canonicalSchedule rightCapital)

||| Cross-trace convergence consumes both complete canonical bundles and the
||| supported-order permutation.  O/A joins the existing A/A, A/O, and O/O
||| local cases when yielded-registration-bearing whole blocks cross.
public export
0 canonicalSchedulesConvergeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (mapped : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital mapped
canonicalSchedulesConvergeSpike = ?canonicalSchedulesConvergeSpike_rhs

||| Exact final endpoint bridge consumes the typed accepted-scanner links and
||| the canonical bridge produced by the bundle-preserving permutation.
public export
0 originalEndpointsConvergeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (scanner : AcceptedDeletionScannerCapital name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital) ->
  {mapped : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital mapped ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
originalEndpointsConvergeSpike = ?originalEndpointsConvergeSpike_rhs

||| Once the two schedules and exact original endpoint bridge are available,
||| the accepted result is direct constructor assembly.
public export
0 confluenceResultFromCanonicalCapital :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  (equivalent : SystemEquivalentByRenamingModuloVestigial name key world error
    value nameEq keyEq (generatedRegistrationTree sameInputs)
      (currentNameBijection (endpointRenaming sameInputs))) ->
  ConfluenceResult name key world error value protocol nameEq keyEq leftTrace
    rightTrace (generatedGenerationBijection sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
confluenceResultFromCanonicalCapital nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftSchedule rightSchedule equivalent =
    MkConfluenceResult leftSchedule rightSchedule
      (generatedRegistrationTree sameInputs)
      (endpointRenaming sameInputs) equivalent
