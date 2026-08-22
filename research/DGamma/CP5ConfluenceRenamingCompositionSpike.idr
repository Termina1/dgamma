module DGamma.CP5ConfluenceRenamingCompositionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
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

||| Exact bridge between the two *canonical endpoints*.  It is intentionally a
||| trace-local relation because accepted cross-trace registration/current-name
||| records are indexed by the two original traces.  The fixed-bijection field
||| prevents a bridge from silently choosing a different current renaming.
public export
record CanonicalEndpointBridge
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace)
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) where
  constructor MkCanonicalEndpointBridge
  canonicalBridgeBijection : NameBijection name
  0 canonicalBridgeBijectionFixed : canonicalBridgeBijection =
    currentNameBijection (endpointRenaming sameInputs)
  0 canonicalBridgeAmbient :
    worldState (canonicalFinal leftSchedule) =
      worldState (canonicalFinal rightSchedule)
  0 canonicalBridgeTables : (n : name) -> (k : key) ->
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq}
        (canonicalFinal leftSchedule)) n) =
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq}
        (canonicalFinal rightSchedule))
        (renameForward canonicalBridgeBijection n))
  0 canonicalBridgeControls : (n : name) ->
    MaybeFiberRelatedBy canonicalBridgeBijection
      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
        {error = error} n (registry (canonicalFinal leftSchedule)))
      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
        {error = error} (renameForward canonicalBridgeBijection n)
        (registry (canonicalFinal rightSchedule)))
  0 canonicalGeneratedBirthMatched :
    {child, parent : name} ->
    {component : Component key value world error} ->
    LocatedGeneratedRegistration child parent component
      (canonicalTrace leftSchedule) ->
    (rightOccurrence : LocatedGeneratedRegistration
      (renameForward canonicalBridgeBijection child)
      (renameForward canonicalBridgeBijection parent) component
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

||| The corrected O21 interface consumes exactly what one-trace canonicalization
||| produces, plus the typed accepted-scanner links above.  These fields are what
||| allow every unmatched original-present fiber to inhabit
||| `VestigialEndpointGeneration` using `leftDeletedGenerations` or
||| `rightDeletedGenerations`; no plain list history is accepted.
public export
0 canonicalSchedulesToOriginalEndpointSpike :
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
    leftTrace rightTrace sameInputs leftCapital rightCapital ->
  CanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs (canonicalSchedule leftCapital)
      (canonicalSchedule rightCapital) ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
canonicalSchedulesToOriginalEndpointSpike =
  ?canonicalSchedulesToOriginalEndpointSpike_rhs
