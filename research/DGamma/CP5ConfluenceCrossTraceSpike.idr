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

||| One certified adjacent swap of incomparable *supported* names in the
||| endpoint partial order at which the operational trace is replayed.
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

||| Mapped capital is deliberately restricted to actual supported names.  The
||| two comparability maps require support-order membership on both endpoints;
||| they cannot be applied to unsupported vestigials.  Operationally we replay
||| the left canonical trace, so the certified permutation is indexed at the
||| left original endpoint and stays in the left raw-name namespace.
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
  ||| Forward comparability only for two names certified supported by the left
  ||| schedule.  This is the exact restriction that avoids the round-2
  ||| vestigial-path contradiction.
  0 leftSupportedComparabilityForward : (lower, upper : name) ->
    Elem lower (supportOrder leftSchedule) ->
    Elem upper (supportOrder leftSchedule) ->
    SupportPath nameEq leftFinal lower upper ->
    SupportPath nameEq rightFinal (renameForward renaming lower)
      (renameForward renaming upper)
  ||| Symmetric supported comparability reflected into the namespace/state in
  ||| which the operational left trace is replayed.
  0 rightSupportedComparabilityBackward : (lower, upper : name) ->
    Elem lower (supportOrder rightSchedule) ->
    Elem upper (supportOrder rightSchedule) ->
    SupportPath nameEq rightFinal lower upper ->
    SupportPath nameEq leftFinal (renameBackward renaming lower)
      (renameBackward renaming upper)
  backwardMappedRightOrderLinearizesLeft : LinearizesSupport name key world error
    value nameEq keyEq leftFinal
    (map (renameBackward renaming) (supportOrder rightSchedule))
  leftOperationalPermutation : CertifiedIncomparablePermutation name key world
    error value nameEq keyEq leftFinal (supportOrder leftSchedule)
    (map (renameBackward renaming) (supportOrder rightSchedule))

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

||| Operational output of the certified *left-state* permutation.  The result
||| is an enriched schedule for the left original trace, not an unrelated trace:
||| its support order is definitionally coupled by `permutedTargetOrderExact` to
||| the inverse-renamed right order, so its `canonicalBlock`,
||| `blocksFollowOrder`, placement, full replay bundle, and endpoint all describe
||| that target.  The endpoint quotient is the composition of all adjacent-swap
||| quotients, and the final bridge is indexed by this very permuted schedule.
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
  permutedLeftCapital : IndependentCanonicalSchedule name key world error value
    protocol nameEq keyEq leftTrace
  0 permutedTargetOrderExact :
    supportOrder (canonicalSchedule permutedLeftCapital) =
      map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
        (supportOrder (canonicalSchedule rightCapital))
  permutationReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value (canonicalTrace (canonicalSchedule leftCapital))
      (canonicalTrace (canonicalSchedule permutedLeftCapital))
  composedPermutationEndpoint : RelationalReplayEndpoint name key world error
    value nameEq keyEq (canonicalFinal (canonicalSchedule leftCapital))
      (canonicalFinal (canonicalSchedule permutedLeftCapital))
  permutationSameExternalInputs : SameExternalOrchestration nameEq
    (canonicalTrace (canonicalSchedule leftCapital))
      (canonicalTrace (canonicalSchedule permutedLeftCapital))
  convergenceBridge : CanonicalEndpointBridge name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs
      (canonicalSchedule permutedLeftCapital) (canonicalSchedule rightCapital)

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

||| Exact final endpoint assembly is complete: it constructs scanner capital
||| for the *permuted* left enriched schedule and feeds the bridge whose left
||| endpoint is that same schedule to O21.  There is no independent scanner or
||| pre-permutation bridge argument that could let a caller bypass replay.
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
  {mapped : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital mapped ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital convergence =
    canonicalSchedulesToOriginalEndpointSpike nameEq keyEq protocol leftTrace
      rightTrace sameInputs (permutedLeftCapital convergence) rightCapital
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs (permutedLeftCapital convergence) rightCapital)
      (convergenceBridge convergence)

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
