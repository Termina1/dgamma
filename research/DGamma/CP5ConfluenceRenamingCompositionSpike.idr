module DGamma.CP5ConfluenceRenamingCompositionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Data.List.Elem
import Decidable.Equality

%default total

||| Generation renamings compose without statement repair.
public export
composeGenerationBijection : RegistrationGenerationBijection name ->
  RegistrationGenerationBijection name -> RegistrationGenerationBijection name
composeGenerationBijection left right =
  MkRegistrationGenerationBijection
    (generationForward right . generationForward left)
    (generationBackward left . generationBackward right)
    (\generation =>
      trans
        (cong (generationBackward left)
          (generationLeftInverse right (generationForward left generation)))
        (generationLeftInverse left generation))
    (\generation =>
      trans
        (cong (generationForward right)
          (generationRightInverse left (generationBackward right generation)))
        (generationRightInverse right generation))

||| Current raw-name renamings compose pointwise as ordinary bijections.
public export
composeNameBijection : NameBijection name -> NameBijection name ->
  NameBijection name
composeNameBijection left right =
  MkNameBijection
    (renameForward right . renameForward left)
    (renameBackward left . renameBackward right)
    (\n => trans
      (cong (renameBackward left)
        (renameLeftInverse right (renameForward left n)))
      (renameLeftInverse left n))
    (\n => trans
      (cong (renameForward right)
        (renameRightInverse left (renameBackward right n)))
      (renameRightInverse right n))

||| Corrected generic transitivity package.  Unlike the round-1 record, the
||| `CurrentEndpointRenaming` is propositionally coupled to the same composed
||| raw-name bijection that indexes the endpoint equivalence.
public export
record CoupledComposedModuloVestigialEndpoint
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, middleFinal, rightFinal :
    SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (middleTrace : Transitions initial middleFinal)
  (rightTrace : Transitions initial rightFinal)
  (leftGenerationRenaming : RegistrationGenerationBijection name)
  (rightGenerationRenaming : RegistrationGenerationBijection name)
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftGenerationRenaming leftTrace middleTrace)
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightGenerationRenaming middleTrace rightTrace)
  (leftCurrentRenaming : NameBijection name)
  (rightCurrentRenaming : NameBijection name) where
  constructor MkCoupledComposedModuloVestigialEndpoint
  composedRegistrations : RegistrationCorrespondenceByGeneration nameEq
    (composeGenerationBijection leftGenerationRenaming rightGenerationRenaming)
    leftTrace rightTrace
  composedNameBijection : NameBijection name
  0 composedNameBijectionExact : composedNameBijection =
    composeNameBijection leftCurrentRenaming rightCurrentRenaming
  composedCurrentEndpoint : CurrentEndpointRenaming nameEq keyEq
    (composeGenerationBijection leftGenerationRenaming rightGenerationRenaming)
    leftTrace rightTrace composedRegistrations
  0 composedCurrentUsesBijection :
    currentNameBijection composedCurrentEndpoint = composedNameBijection
  composedEndpointRelation : SystemEquivalentByRenamingModuloVestigial
    name key world error value nameEq keyEq composedRegistrations
    composedNameBijection

||| Generic vestigial transitivity remains useful algebra, now with the coupling
||| defect repaired.  It is not misrepresented as the one-trace canonicalization
||| bridge: that exact interface appears below.
public export
0 composeModuloVestigialEndpointSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, middleFinal, rightFinal :
    SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (middleTrace : Transitions initial middleFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (leftGenerationRenaming : RegistrationGenerationBijection name) ->
  (rightGenerationRenaming : RegistrationGenerationBijection name) ->
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftGenerationRenaming leftTrace middleTrace) ->
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightGenerationRenaming middleTrace rightTrace) ->
  (leftCurrent : CurrentEndpointRenaming nameEq keyEq leftGenerationRenaming
    leftTrace middleTrace leftRegistrations) ->
  (rightCurrent : CurrentEndpointRenaming nameEq keyEq rightGenerationRenaming
    middleTrace rightTrace rightRegistrations) ->
  (leftRelation : SystemEquivalentByRenamingModuloVestigial name key world error
    value nameEq keyEq leftRegistrations (currentNameBijection leftCurrent)) ->
  (rightRelation : SystemEquivalentByRenamingModuloVestigial name key world error
    value nameEq keyEq rightRegistrations (currentNameBijection rightCurrent)) ->
  CoupledComposedModuloVestigialEndpoint name key world error value nameEq keyEq
    leftTrace middleTrace rightTrace leftGenerationRenaming
    rightGenerationRenaming leftRegistrations rightRegistrations
    (currentNameBijection leftCurrent) (currentNameBijection rightCurrent)
composeModuloVestigialEndpointSpike = ?composeModuloVestigialEndpointSpike_rhs

||| Exact bridge from an operationally replayed left block trace to the right
||| canonical endpoint.  The left trace need not itself be a `CanonicalSchedule`:
||| round 4 exhibited accepted vestigial intermediates for which the inverse
||| right order cannot linearize the left full `SupportPath` relation.  The
||| fixed-bijection field and explicit trace/final indices still prevent bridge
||| detachment.
public export
record ReplayedCanonicalEndpointBridge
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal, replayedLeftFinal :
    SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (replayedLeftTrace : Transitions initial replayedLeftFinal)
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) where
  constructor MkReplayedCanonicalEndpointBridge
  replayBridgeBijection : NameBijection name
  0 replayBridgeBijectionFixed : replayBridgeBijection =
    currentNameBijection (endpointRenaming sameInputs)
  0 replayBridgeAmbient : worldState replayedLeftFinal =
    worldState (canonicalFinal rightSchedule)
  0 replayBridgeTables : (n : name) -> (k : key) ->
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq} replayedLeftFinal) n) =
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq}
        (canonicalFinal rightSchedule))
        (renameForward replayBridgeBijection n))
  0 replayBridgeControls : (n : name) ->
    MaybeFiberRelatedBy replayBridgeBijection
      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
        {error = error} n (registry replayedLeftFinal))
      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
        {error = error} (renameForward replayBridgeBijection n)
        (registry (canonicalFinal rightSchedule)))
  0 replayedGeneratedBirthMatched :
    {child, parent : name} ->
    {component : Component key value world error} ->
    LocatedGeneratedRegistration child parent component replayedLeftTrace ->
    (rightOccurrence : LocatedGeneratedRegistration
      (renameForward replayBridgeBijection child)
      (renameForward replayBridgeBijection parent) component
      (canonicalTrace rightSchedule) ** Unit)

||| Typed link from each one-trace withdrawal to the accepted two-trace
||| registration scanner.  The trace correspondence is exposed at its exact
||| index, and every canonical endpoint withdrawal is a member of the scanner's
||| left/right deleted-generation list with its original closed-parent
||| classification still available.
public export
record AcceptedDeletionScannerCapital
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
    nameEq keyEq rightTrace) where
  constructor MkAcceptedDeletionScannerCapital
  acceptedRegistrationTrace : RegistrationTraceCorrespondence nameEq
    (generatedGenerationBijection sameInputs)
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    leftTrace (leftFinalIndex (generatedRegistrationTree sameInputs))
    0 (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    rightTrace (rightFinalIndex (generatedRegistrationTree sameInputs)) [] []
  0 leftWithdrawnInAcceptedScanner :
    (generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (canonicalEndpoint (canonicalSchedule leftCapital))) ->
    Elem generation (leftDeletedGenerations
      (generatedRegistrationTree sameInputs))
  0 rightWithdrawnInAcceptedScanner :
    (generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (canonicalEndpoint (canonicalSchedule rightCapital))) ->
    Elem generation (rightDeletedGenerations
      (generatedRegistrationTree sameInputs))
  leftDeletedClosingClassification :
    (generation : RegistrationGeneration name) ->
    (withdrawn : Elem generation (endpointWithdrawnGenerations
      (canonicalEndpoint (canonicalSchedule leftCapital)))) ->
    DeletedGenerationClassification name key world error value nameEq leftTrace
      generation
  rightDeletedClosingClassification :
    (generation : RegistrationGeneration name) ->
    (withdrawn : Elem generation (endpointWithdrawnGenerations
      (canonicalEndpoint (canonicalSchedule rightCapital)))) ->
    DeletedGenerationClassification name key world error value nameEq rightTrace
      generation

||| Exact producer boundary for O21 scanner capital.  No deleted-set membership
||| is accepted as an input: the two one-trace classifiers are fed to the
||| left/right scanner-discard inductions against the *accepted* correspondence
||| stored by `sameInputs`.
public export
0 acceptedDeletionScannerCapitalSpike :
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
  AcceptedDeletionScannerCapital name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital
acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital =
    MkAcceptedDeletionScannerCapital
      (generationTraceCorrespondence (generatedRegistrationTree sameInputs))
      (\generation, withdrawn =>
        deletedClassificationForcesLeftScannerDiscardSpike nameEq
          (generatedGenerationBijection sameInputs)
          (leftFinalIndex (generatedRegistrationTree sameInputs))
          (rightFinalIndex (generatedRegistrationTree sameInputs))
          (generationTraceCorrespondence (generatedRegistrationTree sameInputs))
          generation
          (canonicalWithdrawnClassified leftCapital generation withdrawn))
      (\generation, withdrawn =>
        deletedClassificationForcesRightScannerDiscardSpike nameEq
          (generatedGenerationBijection sameInputs)
          (leftFinalIndex (generatedRegistrationTree sameInputs))
          (rightFinalIndex (generatedRegistrationTree sameInputs))
          (generationTraceCorrespondence (generatedRegistrationTree sameInputs))
          generation
          (canonicalWithdrawnClassified rightCapital generation withdrawn))
      (canonicalWithdrawnClassified leftCapital)
      (canonicalWithdrawnClassified rightCapital)

||| Corrected O21 boundary.  Scanner classifications remain indexed by the two
||| original canonical schedules, while operational convergence may pass through
||| a noncanonical target actor order.  The source→replay correspondence,
||| relational endpoint quotient, and exact replay→right bridge expose every
||| composition step instead of pretending the replay is another left
||| `CanonicalSchedule`.
public export
0 replayedCanonicalToOriginalEndpointSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal, replayedLeftFinal :
    SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  AcceptedDeletionScannerCapital name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital ->
  (replayedLeftTrace : Transitions initial replayedLeftFinal) ->
  RelationalReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital)) replayedLeftTrace ->
  RelationalReplayEndpoint name key world error value nameEq keyEq
    (canonicalFinal (canonicalSchedule leftCapital)) replayedLeftFinal ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs replayedLeftTrace
      (canonicalSchedule rightCapital) ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
replayedCanonicalToOriginalEndpointSpike =
  ?replayedCanonicalToOriginalEndpointSpike_rhs
