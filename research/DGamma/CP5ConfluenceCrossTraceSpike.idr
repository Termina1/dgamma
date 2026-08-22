module DGamma.CP5ConfluenceCrossTraceSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total

||| Internal schedule wrapper carrying the original theorem independence and
||| its generator/stage transport to the canonical trace.  Public
||| `CanonicalSchedule` stays immutable; cross-trace transpositions no longer
||| pretend that it contains Definition-60 capital.
public export
record IndependentCanonicalSchedule
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkIndependentCanonicalSchedule
  schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    original
  originalTraceIndependent : TraceIndependent name key world error value keyEq
    original
  canonicalReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original (canonicalTrace schedule)
  canonicalTraceIndependent : TraceIndependent name key world error value keyEq
    (canonicalTrace schedule)

||| One certified adjacent swap of incomparable support names in a single
||| endpoint partial order.
public export
record IncomparableAdjacentOrderSwap
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
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
  0 swapNamesDistinct : Not (swapLeft = swapRight)
  0 swapLeftNotBelowRight : SupportPath nameEq state swapLeft swapRight -> Void
  0 swapRightNotBelowLeft : SupportPath nameEq state swapRight swapLeft -> Void

||| A concrete sequence, not a bare list permutation.  Each adjacent step is
||| certified incomparable in the transported support partial order and can be
||| implemented by the A/A, A/O, and O/O operational diamonds.
public export
data CertifiedIncomparablePermutation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  List name -> List name -> Type where
  PermutationDone : CertifiedIncomparablePermutation name key world error value
    nameEq state order order
  PermutationStep :
    IncomparableAdjacentOrderSwap name key world error value nameEq state
      before middle ->
    CertifiedIncomparablePermutation name key world error value nameEq state
      middle after ->
    CertifiedIncomparablePermutation name key world error value nameEq state
      before after

||| Mapped support capital now preserves/reflexes support paths and supplies the
||| exact adjacent-incomparable sequence needed by O20.
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
  mappedSupportPathForward : (lower, upper : name) ->
    SupportPath nameEq leftFinal lower upper ->
    SupportPath nameEq rightFinal (renameForward renaming lower)
      (renameForward renaming upper)
  mappedSupportPathBackward : (lower, upper : name) ->
    SupportPath nameEq rightFinal lower upper ->
    SupportPath nameEq leftFinal (renameBackward renaming lower)
      (renameBackward renaming upper)
  mappedOrderPermutation : CertifiedIncomparablePermutation name key world error
    value nameEq rightFinal
    (map (renameForward renaming) (supportOrder leftSchedule))
    (supportOrder rightSchedule)

||| Candidate bridge from accepted generation/current renaming to the enriched
||| mapped partial orders.  The wrapper makes both original and canonical
||| independence available to the subsequent operational permutation.
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
    (schedule leftCapital) (schedule rightCapital)
canonicalSupportOrdersMatchSpike = ?canonicalSupportOrdersMatchSpike_rhs

||| Cross-trace convergence now returns the exact canonical-endpoint bridge and
||| explicitly consumes both original/canonical independence witnesses plus the
||| certified incomparable-swap sequence.  Endpoint transport back to the
||| originals is the separate exact composition spike.
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
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq
    leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (schedule leftCapital) (schedule rightCapital) ->
  CanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs (schedule leftCapital) (schedule rightCapital)
canonicalSchedulesConvergeSpike = ?canonicalSchedulesConvergeSpike_rhs

||| Exact final endpoint bridge consuming precisely the canonical bridge above
||| and the two one-trace schedules.
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
  CanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs (schedule leftCapital) (schedule rightCapital) ->
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
