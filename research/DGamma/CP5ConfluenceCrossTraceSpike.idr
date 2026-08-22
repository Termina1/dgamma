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

||| Pure actor-list transposition.  O19 proves only that the two supported actor
||| enumerations contain the same renamed names and therefore admit a sequence
||| of adjacent swaps.  It deliberately says nothing about `SupportPath`:
||| round 4 exhibited a supported-endpoint path through an omitted unsupported
||| vestigial intermediate.
public export
record AdjacentActorOrderSwap (name : Type)
  (before, after : List name) where
  constructor MkAdjacentActorOrderSwap
  actorPrefix : List name
  actorLeft : name
  actorRight : name
  actorSuffix : List name
  0 actorBeforeExact : before = actorPrefix ++
    (actorLeft :: actorRight :: actorSuffix)
  0 actorAfterExact : after = actorPrefix ++
    (actorRight :: actorLeft :: actorSuffix)
  0 actorDistinct : Not (actorLeft = actorRight)

public export
data CertifiedActorPermutation :
  (name : Type) -> List name -> List name -> Type where
  ActorPermutationDone : CertifiedActorPermutation name order order
  ActorPermutationStep :
    AdjacentActorOrderSwap name before middle ->
    CertifiedActorPermutation name middle after ->
    CertifiedActorPermutation name before after

||| Exact contiguous-block structure carried at every operational replay state.
public export
record ActorBlockDecomposition
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (order : List name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkActorBlockDecomposition
  decomposedBlock : (n : name) -> Elem n order ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n trace
  decomposedBlocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier order) ->
    (laterIn : Elem later order) ->
    BeforeIn earlier later order ->
    BlockBefore name key world error value nameEq keyEq trace earlier later
      (decomposedBlock earlier earlierIn) (decomposedBlock later laterIn)
  decomposedLifecycleCoverage : LifecycleActorsCovered order trace

||| One *actual* whole-block transposition.  This is the local swappability
||| relation consumed by O20: its producer expands the actor swap into the
||| source-sensitive A/A, A/O, O/A, and O/O `AdjacentSwapResult`s, and returns
||| the next exact trace, block decomposition, endpoint quotient, correspondence,
||| external-input witness, and complete recursive bundle.
public export
record OperationalAdjacentBlockSwap
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceOrder, targetOrder : List name}
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal : SystemState name key value world error}
  (sourceTrace : Transitions initial sourceFinal)
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace)
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) where
  constructor MkOperationalAdjacentBlockSwap
  blockSwapFinal : SystemState name key value world error
  blockSwapTrace : Transitions initial blockSwapFinal
  blockSwapBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    targetOrder blockSwapTrace
  blockSwapReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value sourceTrace blockSwapTrace
  blockSwapEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq sourceFinal blockSwapFinal
  blockSwapPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq blockSwapTrace
  blockSwapSameExternalInputs : SameExternalOrchestration nameEq sourceTrace
    blockSwapTrace

||| A certificate is operational only when every list swap is realized at the
||| current replay trace and its returned bundle/decomposition feeds the next
||| step.  Thus O20 cannot discharge a permutation with field-level order facts.
public export
data OperationalActorPermutation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceOrder, targetOrder : List name} ->
  (certificate : CertifiedActorPermutation name sourceOrder targetOrder) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions initial sourceFinal) ->
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace) ->
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) ->
  (targetTrace : Transitions initial targetFinal) -> Type where
  OperationalActorDone :
    (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
      order trace) ->
    (premises : ReplayInvariantBundle name key world error value protocol nameEq
      keyEq trace) ->
    OperationalActorPermutation name key world error value protocol nameEq keyEq
      ActorPermutationDone trace blocks premises trace
  OperationalActorStep :
    (orderSwap : AdjacentActorOrderSwap name before middle) ->
    (restCertificate : CertifiedActorPermutation name middle after) ->
    (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
      before sourceTrace) ->
    (sourcePremises : ReplayInvariantBundle name key world error value protocol
      nameEq keyEq sourceTrace) ->
    (step : OperationalAdjacentBlockSwap name key world error value protocol
      nameEq keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
    (rest : OperationalActorPermutation name key world error value protocol
      nameEq keyEq restCertificate (blockSwapTrace step) (blockSwapBlocks step)
        (blockSwapPremises step) targetTrace) ->
    OperationalActorPermutation name key world error value protocol nameEq keyEq
      (ActorPermutationStep orderSwap restCertificate) sourceTrace sourceBlocks
        sourcePremises targetTrace

||| O19 now transports only support-set membership and list identity.  It does
||| not transport direct edges, full paths, incomparability, or a linearization
||| across endpoints.  The inverse-renamed right order is merely an actor-list
||| target; O20 must realize every adjacent swap through the operational relation
||| above.  Unsupported intermediate fibers never occur in either actor list.
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
  leftActorOrderPermutation : CertifiedActorPermutation name
    (supportOrder leftSchedule)
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

||| Regression package for the round-4 blocker at the real accepted indices.
||| `leftVestigial` supplies a precise deleted birth from the accepted two-trace
||| scanner, while `pathFirst`/`pathRest` expose the unsupported withdrawn fiber
||| as an actual intermediate—not merely an endpoint field.  The path remains
||| valid on the original left endpoint, but its intermediate is proved absent
||| from the operational actor list and O19 still supplies the exact pure target
||| permutation without transporting or linearizing that path.
public export
record IntermediateVestigialPermutationRegression
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
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital))
  (lower, withdrawnMiddle, upper : name) where
  constructor MkIntermediateVestigialPermutationRegression
  pathThroughWithdrawnIntermediate : SupportPath nameEq leftFinal lower upper
  preciseWithdrawnBirth : RegistrationGeneration name
  0 preciseWithdrawnBirthCurrent : lookupCurrentGeneration @{nameEq}
    withdrawnMiddle
    (leftFinalGenerations (generatedRegistrationTree sameInputs)) =
      Just preciseWithdrawnBirth
  0 preciseWithdrawnBirthDeleted : Elem preciseWithdrawnBirth
    (leftDeletedGenerations (generatedRegistrationTree sameInputs))
  0 withdrawnIntermediateAbsentRight :
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error}
      (renameForward (currentNameBijection (endpointRenaming sameInputs))
        withdrawnMiddle) (registry rightFinal) = Nothing
  0 withdrawnIntermediateNotAnActor :
    Elem withdrawnMiddle (supportOrder (canonicalSchedule leftCapital)) -> Void
  exactOperationalActorTarget : CertifiedActorPermutation name
    (supportOrder (canonicalSchedule leftCapital))
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital)))

public export
intermediateVestigialProducerRegression :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  (mapped : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  (lower, withdrawnMiddle, upper : name) ->
  SupportEdge nameEq leftFinal lower withdrawnMiddle ->
  SupportPath nameEq leftFinal withdrawnMiddle upper ->
  (leftVestigial : VestigialEndpointGeneration name key world error value nameEq
    keyEq (leftFinalGenerations (generatedRegistrationTree sameInputs))
      (leftDeletedGenerations (generatedRegistrationTree sameInputs))
      withdrawnMiddle leftFinal) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error}
    (renameForward (currentNameBijection (endpointRenaming sameInputs))
      withdrawnMiddle) (registry rightFinal) = Nothing ->
  IntermediateVestigialPermutationRegression name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital mapped
    lower withdrawnMiddle upper
intermediateVestigialProducerRegression mapped lower withdrawnMiddle upper
  pathFirst pathRest leftVestigial rightAbsent =
    MkIntermediateVestigialPermutationRegression
      {sameInputs = sameInputs} {leftCapital = leftCapital}
      {rightCapital = rightCapital} {mapped = mapped}
      {lower = lower} {withdrawnMiddle = withdrawnMiddle} {upper = upper}
      (SupportPathMore pathFirst pathRest)
      (vestigialGeneration leftVestigial)
      (vestigialGenerationCurrent leftVestigial)
      (vestigialBirthDiscarded leftVestigial)
      rightAbsent
      (\middleIn => case trans
        (sym (orderSound
          (supportLinearization (canonicalSchedule leftCapital))
          withdrawnMiddle middleIn))
        (vestigialUnsupported leftVestigial) of Refl impossible)
      (leftActorOrderPermutation mapped)

||| Canonical schedules already expose the exact source block decomposition
||| consumed by the first operational actor swap.
public export
canonicalActorBlockDecomposition :
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    original) ->
  ActorBlockDecomposition name key world error value nameEq keyEq
    (supportOrder schedule) (canonicalTrace schedule)
canonicalActorBlockDecomposition schedule =
  MkActorBlockDecomposition (canonicalBlock schedule)
    (blocksFollowOrder schedule) (lifecycleCoverage schedule)

||| Exact operational target of O20.  It intentionally is *not* another
||| `CanonicalSchedule` for the left original endpoint: the inverse-right actor
||| order need not linearize the left full `SupportPath` relation.  Instead the
||| recursive certificate proves that every adjacent actor swap was realized by
||| actual block replay, with exact blocks and a complete bundle at every step.
public export
record PermutedCanonicalExecution
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
  constructor MkPermutedCanonicalExecution
  permutedLeftFinal : SystemState name key value world error
  permutedLeftTrace : Transitions initial permutedLeftFinal
  permutedLeftBlocks : ActorBlockDecomposition name key world error value nameEq
    keyEq
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital)))
    permutedLeftTrace
  operationalPermutationReplay : OperationalActorPermutation name key world error
    value protocol nameEq keyEq (leftActorOrderPermutation mapped)
    (canonicalTrace (canonicalSchedule leftCapital))
    (canonicalActorBlockDecomposition (canonicalSchedule leftCapital))
    (canonicalReplayPremises leftCapital) permutedLeftTrace
  permutationReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value (canonicalTrace (canonicalSchedule leftCapital)) permutedLeftTrace
  composedPermutationEndpoint : RelationalReplayEndpoint name key world error
    value nameEq keyEq (canonicalFinal (canonicalSchedule leftCapital))
      permutedLeftFinal
  permutedReplayPremises : ReplayInvariantBundle name key world error value
    protocol nameEq keyEq permutedLeftTrace
  permutationSameExternalInputs : SameExternalOrchestration nameEq
    (canonicalTrace (canonicalSchedule leftCapital)) permutedLeftTrace

||| Cross-trace convergence couples the actual operational target trace to the
||| replay→right bridge.  Neither side is retyped as a false left canonical
||| linearization.
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
  permutedLeftExecution : PermutedCanonicalExecution name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
      mapped
  convergenceBridge : ReplayedCanonicalEndpointBridge name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs
      (permutedLeftTrace permutedLeftExecution) (canonicalSchedule rightCapital)

||| Cross-trace convergence consumes the pure actor permutation, then proves an
||| `OperationalAdjacentBlockSwap` at every step.  O/A joins A/A, A/O, and O/O
||| when yielded-registration-bearing whole blocks cross.  No support-path
||| incomparability premise is used.
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

||| Exact final endpoint assembly is complete.  Scanner classifications remain
||| indexed by the original left/right canonical schedules; the operational
||| execution supplies the source→target correspondence and quotient, and its
||| exact target trace indexes the replay→right bridge.  No detached scanner,
||| replay, endpoint, or bridge premise is accepted from the caller.
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
    replayedCanonicalToOriginalEndpointSpike nameEq keyEq protocol leftTrace
      rightTrace sameInputs leftCapital rightCapital
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital)
      (permutedLeftTrace (permutedLeftExecution convergence))
      (permutationReplayCorrespondence (permutedLeftExecution convergence))
      (composedPermutationEndpoint (permutedLeftExecution convergence))
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
