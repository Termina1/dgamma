module DGamma.CP5ConfluenceCrossTraceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total

||| Pure finite-list transposition.  This remains useful matching capital, but
||| revision 6 deliberately prevents a value of this type from flowing directly
||| into O20: actor distinctness alone cannot justify a local diamond.
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

||| Executable negative evidence used at a whole-block boundary.  In particular,
||| if the left actor yields a registration of the right actor, O/A cannot move
||| that right lifecycle block before its own licensing O-Insert.
public export
data NoGeneratedChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (forbidden : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  NoGeneratedChildEnd : NoGeneratedChild forbidden NoTransitions
  NoGeneratedChildStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    ((parent : name) -> (component : Component key value world error) ->
      transitionAction transition =
        OInsert forbidden (ChildOf parent) component -> Void) ->
    NoGeneratedChild forbidden rest ->
    NoGeneratedChild forbidden (MoreTransitions transition rest)

||| The parent/child licensing mutation is rejected at the one-step safety
||| boundary, before the recursive O20 theorem is available.
public export
0 generatedChildAtHeadContradictsSafety :
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  {forbidden, parent : name} ->
  {component : Component key value world error} ->
  transitionAction transition =
    OInsert forbidden (ChildOf parent) component ->
  NoGeneratedChild forbidden (MoreTransitions transition rest) -> Void
generatedChildAtHeadContradictsSafety transition rest action
  (NoGeneratedChildStep transition rest rejected safeRest) =
    rejected parent component action

||| Exact safety reconstructed for one adjacent actor pair at its current replay
||| state.  It owns the actual two blocks, their order, the full bundle, and both
||| generated-child licensing exclusions.  These fields are intentionally not
||| reducible to `actorDistinct`.
public export
record AdjacentActorSwapSafety
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
  constructor MkAdjacentActorSwapSafety
  safetyLeftInOrder : Elem (actorLeft orderSwap) sourceOrder
  safetyRightInOrder : Elem (actorRight orderSwap) sourceOrder
  safetyLeftBeforeRight : BeforeIn (actorLeft orderSwap) (actorRight orderSwap)
    sourceOrder
  safetyBlocksOrdered : BlockBefore name key world error value nameEq keyEq
    sourceTrace (actorLeft orderSwap) (actorRight orderSwap)
    (decomposedBlock sourceBlocks (actorLeft orderSwap) safetyLeftInOrder)
    (decomposedBlock sourceBlocks (actorRight orderSwap) safetyRightInOrder)
  0 safetyLeftDoesNotGenerateRight : NoGeneratedChild (actorRight orderSwap)
    (blockBody (decomposedBlock sourceBlocks (actorLeft orderSwap)
      safetyLeftInOrder))
  0 safetyRightDoesNotGenerateLeft : NoGeneratedChild (actorLeft orderSwap)
    (blockBody (decomposedBlock sourceBlocks (actorRight orderSwap)
      safetyRightInOrder))

||| One actual whole-block transposition.  The finite derivation is mandatory:
||| every transition crossing is classified A/A, A/O, O/A, or O/O and carries
||| its concrete `AdjacentSwapResult`, including action/registration occurrence
||| correspondence.  Endpoint assertions alone cannot construct this record.
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
    nameEq keyEq sourceTrace)
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) where
  constructor MkOperationalAdjacentBlockSwap
  blockSwapFinal : SystemState name key value world error
  blockSwapTrace : Transitions initial blockSwapFinal
  blockSwapFiniteDerivation : FiniteAdjacentSwapDerivation name key world error
    value protocol nameEq keyEq sourceTrace blockSwapTrace
  blockSwapBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    targetOrder blockSwapTrace
  blockSwapEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq sourceFinal blockSwapFinal
  blockSwapPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq blockSwapTrace
  blockSwapSameExternalInputs : SameExternalOrchestration nameEq sourceTrace
    blockSwapTrace

public export
0 blockSwapReplayCorrespondence :
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  RelationalReplayCorrespondence name key world error value sourceTrace
    (blockSwapTrace step)
blockSwapReplayCorrespondence step =
  finiteDerivationReplayCorrespondence (blockSwapFiniteDerivation step)

public export
0 blockSwapOccurrenceCorrespondence :
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  ActionRegistrationReplayCorrespondence name key world error value sourceTrace
    (blockSwapTrace step)
blockSwapOccurrenceCorrespondence step =
  finiteDerivationOccurrenceCorrespondence (blockSwapFiniteDerivation step)

||| Exact one-step operational producer.  Its proof must enumerate the finite
||| Cartesian crossing of the two located blocks, derive early applicability and
||| orientation-specific premises from the current bundle/safety, invoke the
||| four local diamonds, and splice every `AdjacentSwapResult`.
public export
0 operationalAdjacentBlockSwapSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions initial sourceFinal) ->
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace) ->
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety
operationalAdjacentBlockSwapSpike = ?operationalAdjacentBlockSwapSpike_rhs

||| Every selected list step is now indexed by exact operational safety and its
||| realized block replay.  A caller cannot prepend a pure swap/inverse loop
||| without also constructing both intermediate safety proofs and finite local
||| diamond derivations.
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
    (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
      keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
    (step : OperationalAdjacentBlockSwap name key world error value protocol
      nameEq keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
    (rest : OperationalActorPermutation name key world error value protocol
      nameEq keyEq restCertificate (blockSwapTrace step) (blockSwapBlocks step)
        (blockSwapPremises step) targetTrace) ->
    OperationalActorPermutation name key world error value protocol nameEq keyEq
      (ActorPermutationStep orderSwap restCertificate) sourceTrace sourceBlocks
        sourcePremises targetTrace

public export
0 operationalPermutationReplayCorrespondence :
  OperationalActorPermutation name key world error value protocol nameEq keyEq
    certificate sourceTrace sourceBlocks sourcePremises targetTrace ->
  RelationalReplayCorrespondence name key world error value sourceTrace targetTrace
operationalPermutationReplayCorrespondence
  (OperationalActorDone blocks premises) =
    MkRelationalReplayCorrespondence (\actor, generator => generator)
      (\actor, generator, state => Refl) (\actor, stage => stage)
      (\actor, stage, state => Refl)
operationalPermutationReplayCorrespondence
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      composeRelationalReplayCorrespondence (blockSwapReplayCorrespondence step)
        (operationalPermutationReplayCorrespondence rest)

public export
0 operationalPermutationOccurrenceCorrespondence :
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  (replay : OperationalActorPermutation name key world error value protocol nameEq
    keyEq certificate sourceTrace sourceBlocks sourcePremises targetTrace) ->
  ActionRegistrationReplayCorrespondence name key world error value sourceTrace
    targetTrace
operationalPermutationOccurrenceCorrespondence {sourceTrace}
  (OperationalActorDone blocks premises) =
    identityActionRegistrationReplayCorrespondence sourceTrace
operationalPermutationOccurrenceCorrespondence
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      composeActionRegistrationReplayCorrespondence
        (blockSwapOccurrenceCorrespondence step)
        (operationalPermutationOccurrenceCorrespondence rest)

||| Cross-trace support matching now contains no certificate at all.  It is
||| publicly constructible without risk because O20 never consumes it as an
||| operational schedule; it records only renamed set equality.
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

||| Canonical schedules expose the exact first-state blocks consumed by O19.
public export
canonicalActorBlockDecomposition :
  (schedule : CanonicalSchedule name key world error value protocol nameEq keyEq
    original) ->
  ActorBlockDecomposition name key world error value nameEq keyEq
    (supportOrder schedule) (canonicalTrace schedule)
canonicalActorBlockDecomposition schedule =
  MkActorBlockDecomposition (canonicalBlock schedule)
    (blocksFollowOrder schedule) (lifecycleCoverage schedule)

||| Sealed-by-evidence O19 output.  The pure certificate and every exact
||| intermediate trace are existential fields of the same package as the
||| operational realization; there is no function from a public pure
||| certificate to O20.
public export
record CertifiedOperationalCanonicalPermutation
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
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) where
  constructor MkCertifiedOperationalCanonicalPermutation
  selectedActorPermutation : CertifiedActorPermutation name
    (supportOrder (canonicalSchedule leftCapital))
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital)))
  operationalTargetFinal : SystemState name key value world error
  operationalTargetTrace : Transitions initial operationalTargetFinal
  operationalTargetBlocks : ActorBlockDecomposition name key world error value
    nameEq keyEq
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital))) operationalTargetTrace
  operationalTargetPremises : ReplayInvariantBundle name key world error value
    protocol nameEq keyEq operationalTargetTrace
  selectedPermutationRealized : OperationalActorPermutation name key world error
    value protocol nameEq keyEq selectedActorPermutation
    (canonicalTrace (canonicalSchedule leftCapital))
    (canonicalActorBlockDecomposition (canonicalSchedule leftCapital))
    (canonicalReplayPremises leftCapital) operationalTargetTrace

||| O19 must choose a permutation and realize it simultaneously.  This is the
||| remaining existence risk when accepted support relations differ through
||| withdrawn intermediates; the type no longer hides that risk in O20.
public export
0 selectOperationalCanonicalPermutationSpike :
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
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  CertifiedOperationalCanonicalPermutation name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching
selectOperationalCanonicalPermutationSpike =
  ?selectOperationalCanonicalPermutationSpike_rhs

||| Honest revision-6 label: this is a static accepted-index interface test, not
||| a concrete reachable O19/O20 run.  It proves that the old full-path field is
||| absent while preserving the exact scanner-deleted birth and real path.
public export
record IntermediateVestigialStaticInterfaceRegression
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
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital))
  (lower, withdrawnMiddle, upper : name) where
  constructor MkIntermediateVestigialStaticInterfaceRegression
  pathThroughWithdrawnIntermediate : SupportPath nameEq leftFinal lower upper
  preciseWithdrawnBirth : RegistrationGeneration name
  0 preciseWithdrawnBirthCurrent : lookupCurrentGeneration @{nameEq}
    withdrawnMiddle (leftFinalGenerations (generatedRegistrationTree sameInputs)) =
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

public export
intermediateVestigialStaticInterfaceRegression :
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
  (matching : MappedCanonicalSupportOrders name key world error value protocol
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
  IntermediateVestigialStaticInterfaceRegression name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
      matching lower withdrawnMiddle upper
intermediateVestigialStaticInterfaceRegression matching lower withdrawnMiddle
  upper pathFirst pathRest leftVestigial rightAbsent =
    MkIntermediateVestigialStaticInterfaceRegression
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

||| O20 packages the exact already-safe operational target with its endpoint
||| quotient and bridge.  Occurrence correspondence is derived structurally from
||| the sealed operational fold, not asserted from effect-generator capital.
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
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)}
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) where
  constructor MkPermutedCanonicalExecution
  composedPermutationEndpoint : RelationalReplayEndpoint name key world error
    value nameEq keyEq (canonicalFinal (canonicalSchedule leftCapital))
      (operationalTargetFinal operational)
  permutationSameExternalInputs : SameExternalOrchestration nameEq
    (canonicalTrace (canonicalSchedule leftCapital))
      (operationalTargetTrace operational)

public export
0 permutationReplayCorrespondence :
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  RelationalReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital))
    (operationalTargetTrace operational)
permutationReplayCorrespondence {operational} execution =
  operationalPermutationReplayCorrespondence
    (selectedPermutationRealized operational)

public export
0 permutationOccurrenceCorrespondence :
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital))
    (operationalTargetTrace operational)
permutationOccurrenceCorrespondence {operational} execution =
  operationalPermutationOccurrenceCorrespondence
    (selectedPermutationRealized operational)

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
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)}
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) where
  constructor MkCanonicalConvergenceResult
  permutedLeftExecution : PermutedCanonicalExecution name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
      operational
  convergenceBridge : ReplayedCanonicalEndpointBridge name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs
      (canonicalTrace (canonicalSchedule leftCapital))
      (operationalTargetTrace operational)
      (permutationOccurrenceCorrespondence permutedLeftExecution)
      (canonicalSchedule rightCapital)

||| O20 no longer quantifies over a public pure certificate.  It accepts only
||| O19's package containing exact safety and finite local derivations.
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
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational
canonicalSchedulesConvergeSpike = ?canonicalSchedulesConvergeSpike_rhs

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
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital convergence =
    replayedCanonicalToOriginalEndpointSpike nameEq keyEq protocol leftTrace
      rightTrace sameInputs leftCapital rightCapital
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital)
      (operationalTargetTrace operational)
      (permutationReplayCorrespondence (permutedLeftExecution convergence))
      (composedPermutationEndpoint (permutedLeftExecution convergence))
      (permutationOccurrenceCorrespondence (permutedLeftExecution convergence))
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
