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

0 composeRegistrationEventMatch :
  (leftRenaming, rightRenaming : RegistrationGenerationBijection name) ->
  {left, middle, right : RegistrationEvent name key world error value} ->
  RegistrationEventMatch leftRenaming left middle ->
  RegistrationEventMatch rightRenaming middle right ->
  RegistrationEventMatch
    (composeGenerationBijection leftRenaming rightRenaming) left right
composeRegistrationEventMatch leftRenaming rightRenaming leftMatch rightMatch =
  let 0 middleActivationSame :
        (rightMatchedActivation leftMatch = leftMatchedActivation rightMatch)
      middleActivationSame = justInjective
        (trans (sym (rightActivationPresent leftMatch))
          (leftActivationPresent rightMatch))
  in MkRegistrationEventMatch
    (trans (matchedComponent leftMatch) (matchedComponent rightMatch))
    (leftMatchedActivation leftMatch)
    (rightMatchedActivation rightMatch)
    (leftActivationPresent leftMatch)
    (rightActivationPresent rightMatch)
    (trans
      (cong (generationForward rightRenaming)
        (matchedChildGeneration leftMatch))
      (matchedChildGeneration rightMatch))
    (trans
      (cong (generationForward rightRenaming)
        (matchedParentGeneration leftMatch))
      (trans
        (cong
          (generationForward rightRenaming . activationParentGeneration)
          middleActivationSame)
        (matchedParentGeneration rightMatch)))
    (trans (matchedPerActivationPosition leftMatch)
      (matchedPerActivationPosition rightMatch))

0 noParentUnloadRejectsOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {parent : name} -> {trace : Transitions first finalState} ->
  NoParentUnload parent trace -> ActionOccurs (LUnload parent) trace -> Void
noParentUnloadRejectsOccurrence NoParentUnloadEnd occurrence impossible
noParentUnloadRejectsOccurrence
  (NoParentUnloadStep transition rest different laterSafe)
  (ActionOccursHere transition rest unload) = different unload
noParentUnloadRejectsOccurrence
  (NoParentUnloadStep transition rest different laterSafe)
  (ActionOccursLater transition rest laterOccurrence) =
    noParentUnloadRejectsOccurrence laterSafe laterOccurrence

0 survivingDeletedRegistrationImpossible :
  {event : RegistrationEvent name key world error value} ->
  {rest : Transitions first finalState} ->
  SurvivingRegistration event rest -> DeletedClosingRegistration event rest ->
  Void
survivingDeletedRegistrationImpossible surviving deleted =
  noParentUnloadRejectsOccurrence
    (survivingParentEpisodeOpen surviving)
    (deletedParentEpisodeCloses deleted)

||| One side of the accepted asynchronous registration scanner.  This private
||| projection forgets only the interleaving and pending-list bookkeeping; it
||| retains every exact index transition and the surviving/deleted decision at
||| each generated birth.  Scanner composition will use the two projections of
||| the shared middle trace as its synchronization spine.
data RegistrationSideScan :
  (nameEq : DecEq name) ->
  (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (finalIndex : RegistrationIndexState name) -> Type where
  RegistrationSideScanEnd :
    RegistrationSideScan nameEq ordinal index NoTransitions index
  RegistrationSideScanNonRegistration :
    (action : Action name key value world error) ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionAction transition = action ->
    isGeneratedRegistrationAction action = False ->
    RegistrationSideScan nameEq (S ordinal)
      (advanceRegistrationIndex @{nameEq} ordinal action index)
      rest finalIndex ->
    RegistrationSideScan nameEq ordinal index
      (MoreTransitions transition rest) finalIndex
  RegistrationSideScanDeleted :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    DeletedClosingRegistration
      (registrationEventAt @{nameEq} ordinal index child parent component)
      rest ->
    RegistrationSideScan nameEq (S ordinal)
      (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component
        index)
      rest finalIndex ->
    RegistrationSideScan nameEq ordinal index
      (MoreTransitions transition rest) finalIndex
  RegistrationSideScanSurviving :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionAction transition = OInsert child (ChildOf parent) component ->
    SurvivingRegistration
      (registrationEventAt @{nameEq} ordinal index child parent component)
      rest ->
    RegistrationSideScan nameEq (S ordinal)
      (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component
        index)
      rest finalIndex ->
    RegistrationSideScan nameEq ordinal index
      (MoreTransitions transition rest) finalIndex

0 leftRegistrationSideScan :
  RegistrationTraceCorrespondence nameEq renaming
    leftOrdinal leftIndex left leftResultIndex
    rightOrdinal rightIndex right rightResultIndex pendingLeft pendingRight ->
  RegistrationSideScan nameEq leftOrdinal leftIndex left leftResultIndex
leftRegistrationSideScan RegistrationCorrespondenceEnd = RegistrationSideScanEnd
leftRegistrationSideScan
  (SkipLeftNonRegistration action transition rest actionExact notRegistration
    correspondence) =
      RegistrationSideScanNonRegistration action transition rest actionExact
        notRegistration (leftRegistrationSideScan correspondence)
leftRegistrationSideScan (SkipRightNonRegistration _ _ _ _ _ correspondence) =
  leftRegistrationSideScan correspondence
leftRegistrationSideScan
  (DiscardLeftDeletedRegistration transition rest actionExact deleted
    correspondence) =
      RegistrationSideScanDeleted transition rest actionExact deleted
        (leftRegistrationSideScan correspondence)
leftRegistrationSideScan
  (DiscardRightDeletedRegistration _ _ _ _ correspondence) =
    leftRegistrationSideScan correspondence
leftRegistrationSideScan
  (QueueLeftGeneratedRegistration transition rest actionExact surviving
    correspondence) =
      RegistrationSideScanSurviving transition rest actionExact surviving
        (leftRegistrationSideScan correspondence)
leftRegistrationSideScan
  (QueueRightGeneratedRegistration _ _ _ _ correspondence) =
    leftRegistrationSideScan correspondence
leftRegistrationSideScan
  (MatchLeftWithPendingRight transition rest actionExact surviving _ _ _ _
    correspondence) =
      RegistrationSideScanSurviving transition rest actionExact surviving
        (leftRegistrationSideScan correspondence)
leftRegistrationSideScan
  (MatchRightWithPendingLeft _ _ _ _ _ _ _ _ correspondence) =
    leftRegistrationSideScan correspondence

0 rightRegistrationSideScan :
  RegistrationTraceCorrespondence nameEq renaming
    leftOrdinal leftIndex left leftResultIndex
    rightOrdinal rightIndex right rightResultIndex pendingLeft pendingRight ->
  RegistrationSideScan nameEq rightOrdinal rightIndex right rightResultIndex
rightRegistrationSideScan RegistrationCorrespondenceEnd = RegistrationSideScanEnd
rightRegistrationSideScan (SkipLeftNonRegistration _ _ _ _ _ correspondence) =
  rightRegistrationSideScan correspondence
rightRegistrationSideScan
  (SkipRightNonRegistration action transition rest actionExact notRegistration
    correspondence) =
      RegistrationSideScanNonRegistration action transition rest actionExact
        notRegistration (rightRegistrationSideScan correspondence)
rightRegistrationSideScan
  (DiscardLeftDeletedRegistration _ _ _ _ correspondence) =
    rightRegistrationSideScan correspondence
rightRegistrationSideScan
  (DiscardRightDeletedRegistration transition rest actionExact deleted
    correspondence) =
      RegistrationSideScanDeleted transition rest actionExact deleted
        (rightRegistrationSideScan correspondence)
rightRegistrationSideScan
  (QueueLeftGeneratedRegistration _ _ _ _ correspondence) =
    rightRegistrationSideScan correspondence
rightRegistrationSideScan
  (QueueRightGeneratedRegistration transition rest actionExact surviving
    correspondence) =
      RegistrationSideScanSurviving transition rest actionExact surviving
        (rightRegistrationSideScan correspondence)
rightRegistrationSideScan
  (MatchLeftWithPendingRight _ _ _ _ _ _ _ _ correspondence) =
    rightRegistrationSideScan correspondence
rightRegistrationSideScan
  (MatchRightWithPendingLeft transition rest actionExact surviving _ _ _ _
    correspondence) =
      RegistrationSideScanSurviving transition rest actionExact surviving
        (rightRegistrationSideScan correspondence)

0 falseIsNotTrue : False = True -> Void
falseIsNotTrue Refl impossible

0 nonRegistrationCannotBeGenerated :
  {transition : Transition first middle} ->
  transitionAction transition = action ->
  isGeneratedRegistrationAction action = False ->
  transitionAction transition = OInsert child (ChildOf parent) component ->
  Void
nonRegistrationCannotBeGenerated actionExact notRegistration generatedExact =
  let actionSame = trans (sym actionExact) generatedExact
      classifiedAsGenerated = cong isGeneratedRegistrationAction actionSame
  in falseIsNotTrue (trans (sym notRegistration) classifiedAsGenerated)

||| A trace and starting index have one scanner result.  In particular, the
||| same shared-middle birth cannot be deleted by one correspondence and
||| surviving in the other: that would require and forbid the same later
||| parent unload.  This is the first synchronization theorem needed by the
||| registration-correspondence composition.
0 registrationSideScanFinalIndexUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {ordinal : Nat} -> {index : RegistrationIndexState name} ->
  {leftResult, rightResult : RegistrationIndexState name} ->
  (leftScan : RegistrationSideScan nameEq ordinal index trace leftResult) ->
  (rightScan : RegistrationSideScan nameEq ordinal index trace rightResult) ->
  leftResult = rightResult
registrationSideScanFinalIndexUnique RegistrationSideScanEnd
  RegistrationSideScanEnd = Refl
registrationSideScanFinalIndexUnique
  (RegistrationSideScanNonRegistration leftAction transition rest leftExact
    leftNotRegistration leftLater)
  (RegistrationSideScanNonRegistration rightAction transition rest rightExact
    rightNotRegistration rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => registrationSideScanFinalIndexUnique leftLater rightLater
registrationSideScanFinalIndexUnique
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration later)
  (RegistrationSideScanDeleted transition rest generatedExact deleted
    rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideScanFinalIndexUnique
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration later)
  (RegistrationSideScanSurviving transition rest generatedExact surviving
    rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideScanFinalIndexUnique
  (RegistrationSideScanDeleted transition rest generatedExact deleted leftLater)
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideScanFinalIndexUnique
  (RegistrationSideScanSurviving transition rest generatedExact surviving
    leftLater)
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideScanFinalIndexUnique
  (RegistrationSideScanDeleted transition rest leftExact leftDeleted leftLater)
  (RegistrationSideScanDeleted transition rest rightExact rightDeleted
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => registrationSideScanFinalIndexUnique leftLater rightLater
registrationSideScanFinalIndexUnique
  (RegistrationSideScanDeleted transition rest leftExact leftDeleted leftLater)
  (RegistrationSideScanSurviving transition rest rightExact rightSurviving
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => void (survivingDeletedRegistrationImpossible rightSurviving
          leftDeleted)
registrationSideScanFinalIndexUnique
  (RegistrationSideScanSurviving transition rest leftExact leftSurviving
    leftLater)
  (RegistrationSideScanDeleted transition rest rightExact rightDeleted
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => void (survivingDeletedRegistrationImpossible leftSurviving
          rightDeleted)
registrationSideScanFinalIndexUnique
  (RegistrationSideScanSurviving transition rest leftExact leftSurviving
    leftLater)
  (RegistrationSideScanSurviving transition rest rightExact rightSurviving
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => registrationSideScanFinalIndexUnique leftLater rightLater

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
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (replayedLeftTrace : Transitions initial replayedLeftFinal)
  (replayedOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value (canonicalTrace (canonicalSchedule leftCapital)) replayedLeftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) where
  constructor MkReplayedCanonicalEndpointBridge
  replayBridgeBijection : NameBijection name
  0 replayBridgeBijectionFixed : replayBridgeBijection =
    currentNameBijection (endpointRenaming sameInputs)
  0 replayBridgeAmbient : worldState replayedLeftFinal =
    worldState (canonicalFinal (canonicalSchedule rightCapital))
  0 replayBridgeTables : (n : name) -> (k : key) ->
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq} replayedLeftFinal) n) =
    lookupBinding {key = key} {value = value} k
      (effectTables (projectEffectState @{nameEq}
        (canonicalFinal (canonicalSchedule rightCapital)))
        (renameForward replayBridgeBijection n))
  0 replayBridgeControls : (n : name) ->
    MaybeFiberRelatedBy replayBridgeBijection
      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
        {error = error} n (registry replayedLeftFinal))
      (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
        {error = error} (renameForward replayBridgeBijection n)
        (registry (canonicalFinal (canonicalSchedule rightCapital))))
  0 replayedGeneratedBirthMatched :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (replayedOccurrence : LocatedGeneratedRegistration child parent component
      replayedLeftTrace) ->
    (sourceOccurrence : LocatedGeneratedRegistration child parent component
      (canonicalTrace (canonicalSchedule leftCapital)) **
      (sourceOccurrence = replayGeneratedRegistrationOrigin replayedOccurrences
        replayedOccurrence,
       (rightOccurrence : LocatedGeneratedRegistration
         (renameForward replayBridgeBijection child)
         (renameForward replayBridgeBijection parent) component
         (canonicalTrace (canonicalSchedule rightCapital)) **
         generationForward (generatedGenerationBijection sameInputs)
           (registrationGeneration
             (replayGeneratedRegistrationOrigin
               (canonicalOccurrenceCorrespondence leftCapital)
               sourceOccurrence)) =
         registrationGeneration
           (replayGeneratedRegistrationOrigin
             (canonicalOccurrenceCorrespondence rightCapital)
             rightOccurrence))))

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

||| Every accepted scanner step now retains its constructor class.  Generated
||| registration events additionally retain the exact raw name and birth
||| ordinal; discard evidence can no longer be simulated by an unrelated skip.
public export
data ScannerEvent : Type -> Type where
  ScannerLeftNonRegistration : Nat -> ScannerEvent name
  ScannerRightNonRegistration : Nat -> ScannerEvent name
  ScannerLeftDiscard : RegistrationGeneration name -> ScannerEvent name
  ScannerRightDiscard : RegistrationGeneration name -> ScannerEvent name
  ScannerLeftQueue : RegistrationGeneration name -> ScannerEvent name
  ScannerRightQueue : RegistrationGeneration name -> ScannerEvent name
  ScannerLeftMatch : RegistrationGeneration name -> ScannerEvent name
  ScannerRightMatch : RegistrationGeneration name -> ScannerEvent name

public export
0 scannerEventSequence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftOrdinal : Nat} -> {leftIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {leftResultIndex : RegistrationIndexState name} ->
  {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  {right : Transitions rightFirst rightFinal} ->
  {rightResultIndex : RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq renaming leftOrdinal leftIndex left
    leftResultIndex rightOrdinal rightIndex right rightResultIndex pendingLeft
    pendingRight -> List (ScannerEvent name)
scannerEventSequence RegistrationCorrespondenceEnd = []
scannerEventSequence {leftOrdinal}
  (SkipLeftNonRegistration _ _ _ _ _ rest) =
    ScannerLeftNonRegistration leftOrdinal :: scannerEventSequence rest
scannerEventSequence {rightOrdinal}
  (SkipRightNonRegistration _ _ _ _ _ rest) =
    ScannerRightNonRegistration rightOrdinal :: scannerEventSequence rest
scannerEventSequence {leftOrdinal}
  (DiscardLeftDeletedRegistration {child} _ _ _ _ rest) =
    ScannerLeftDiscard (MkRegistrationGeneration child leftOrdinal) ::
      scannerEventSequence rest
scannerEventSequence {rightOrdinal}
  (DiscardRightDeletedRegistration {child} _ _ _ _ rest) =
    ScannerRightDiscard (MkRegistrationGeneration child rightOrdinal) ::
      scannerEventSequence rest
scannerEventSequence {leftOrdinal}
  (QueueLeftGeneratedRegistration {child} _ _ _ _ rest) =
    ScannerLeftQueue (MkRegistrationGeneration child leftOrdinal) ::
      scannerEventSequence rest
scannerEventSequence {rightOrdinal}
  (QueueRightGeneratedRegistration {child} _ _ _ _ rest) =
    ScannerRightQueue (MkRegistrationGeneration child rightOrdinal) ::
      scannerEventSequence rest
scannerEventSequence {leftOrdinal}
  (MatchLeftWithPendingRight {child} _ _ _ _ _ _ _ _ rest) =
    ScannerLeftMatch (MkRegistrationGeneration child leftOrdinal) ::
      scannerEventSequence rest
scannerEventSequence {rightOrdinal}
  (MatchRightWithPendingLeft {child} _ _ _ _ _ _ _ _ rest) =
    ScannerRightMatch (MkRegistrationGeneration child rightOrdinal) ::
      scannerEventSequence rest

||| The four exact target discards—not merely four side labels—alternate in the
||| accepted scanner.  Pairwise `BeforeIn` witnesses tie each ordinal to its
||| real discard constructor and reject clumped target deletions.
public export
0 TargetDiscardsInterleaved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftOrdinal : Nat} -> {leftIndex : RegistrationIndexState name} ->
  {leftFirst, leftFinal : SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {leftResultIndex : RegistrationIndexState name} ->
  {rightOrdinal : Nat} -> {rightIndex : RegistrationIndexState name} ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  {right : Transitions rightFirst rightFinal} ->
  {rightResultIndex : RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  (correspondence : RegistrationTraceCorrespondence nameEq renaming leftOrdinal
    leftIndex left leftResultIndex rightOrdinal rightIndex right rightResultIndex
    pendingLeft pendingRight) ->
  (leftEarlier, leftLater, rightEarlier, rightLater :
    RegistrationGeneration name) -> Type
TargetDiscardsInterleaved correspondence leftEarlier leftLater rightEarlier
  rightLater =
    ( BeforeIn (ScannerLeftDiscard leftEarlier)
        (ScannerRightDiscard rightEarlier) (scannerEventSequence correspondence)
    , BeforeIn (ScannerRightDiscard rightEarlier)
        (ScannerLeftDiscard leftLater) (scannerEventSequence correspondence)
    , BeforeIn (ScannerLeftDiscard leftLater)
        (ScannerRightDiscard rightLater) (scannerEventSequence correspondence)
    )

||| Same-raw-name/multiple-birth regression at accepted indices.  Each exact
||| generation has both scanner-position evidence and final-list membership.
public export
record SameRawNameScannerRegression
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
  (leftEarlier, leftLater, rightEarlier, rightLater :
    RegistrationGeneration name) where
  constructor MkSameRawNameScannerRegression
  targetedDiscardsInterleaved : TargetDiscardsInterleaved
    (generationTraceCorrespondence (generatedRegistrationTree sameInputs))
    leftEarlier leftLater rightEarlier rightLater
  0 leftRawNameReused : generationName leftEarlier = generationName leftLater
  0 rightRawNameReused : generationName rightEarlier = generationName rightLater
  0 leftBirthsDistinct : Not (leftEarlier = leftLater)
  0 rightBirthsDistinct : Not (rightEarlier = rightLater)
  0 leftEarlierDeletedExactly : Elem leftEarlier
    (leftDeletedGenerations (generatedRegistrationTree sameInputs))
  0 leftLaterDeletedExactly : Elem leftLater
    (leftDeletedGenerations (generatedRegistrationTree sameInputs))
  0 rightEarlierDeletedExactly : Elem rightEarlier
    (rightDeletedGenerations (generatedRegistrationTree sameInputs))
  0 rightLaterDeletedExactly : Elem rightLater
    (rightDeletedGenerations (generatedRegistrationTree sameInputs))

public export
sameRawNameScannerRegression :
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
  (leftEarlier, leftLater, rightEarlier, rightLater :
    RegistrationGeneration name) ->
  generationName leftEarlier = generationName leftLater ->
  generationName rightEarlier = generationName rightLater ->
  Not (generationBirthOrdinal leftEarlier = generationBirthOrdinal leftLater) ->
  Not (generationBirthOrdinal rightEarlier = generationBirthOrdinal rightLater) ->
  Elem leftEarlier (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule leftCapital))) ->
  Elem leftLater (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule leftCapital))) ->
  Elem rightEarlier (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule rightCapital))) ->
  Elem rightLater (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule rightCapital))) ->
  TargetDiscardsInterleaved
    (generationTraceCorrespondence (generatedRegistrationTree sameInputs))
    leftEarlier leftLater rightEarlier rightLater ->
  SameRawNameScannerRegression name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital leftEarlier leftLater
    rightEarlier rightLater
sameRawNameScannerRegression nameEq keyEq protocol leftTrace rightTrace sameInputs
  leftCapital rightCapital leftEarlier leftLater rightEarlier rightLater
  leftNames rightNames leftOrdinals rightOrdinals leftEarlierWithdrawn
  leftLaterWithdrawn rightEarlierWithdrawn rightLaterWithdrawn interleaved =
    MkSameRawNameScannerRegression interleaved leftNames rightNames
      (\same => leftOrdinals (cong generationBirthOrdinal same))
      (\same => rightOrdinals (cong generationBirthOrdinal same))
      (leftWithdrawnInAcceptedScanner
        (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
          rightTrace sameInputs leftCapital rightCapital)
        leftEarlier leftEarlierWithdrawn)
      (leftWithdrawnInAcceptedScanner
        (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
          rightTrace sameInputs leftCapital rightCapital)
        leftLater leftLaterWithdrawn)
      (rightWithdrawnInAcceptedScanner
        (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
          rightTrace sameInputs leftCapital rightCapital)
        rightEarlier rightEarlierWithdrawn)
      (rightWithdrawnInAcceptedScanner
        (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
          rightTrace sameInputs leftCapital rightCapital)
        rightLater rightLaterWithdrawn)

||| Concrete executable scanner-index regression.  It is intentionally retained
||| in the branch (rather than only in /tmp): the same raw name is born at exact
||| left ordinals 6/18 and right ordinals 9/14, and three different cross-side
||| schedules compute the same exact per-side deleted lists.
FixtureValue : Unit -> Type
FixtureValue _ = Unit

fixtureSpec : CoeffectSpec Unit
fixtureSpec = MkCoeffectSpec [] UniqueNil

fixtureComponent : Component Unit FixtureValue Unit String
fixtureComponent = MkComponent fixtureSpec fixtureSpec []

public export
record ConcreteScannerIndexes where
  constructor MkConcreteScannerIndexes
  concreteLeftIndex : RegistrationIndexState Nat
  concreteRightIndex : RegistrationIndexState Nat

concreteEmptyIndexes : ConcreteScannerIndexes
concreteEmptyIndexes = MkConcreteScannerIndexes
  DGamma.CP3.emptyRegistrationIndex DGamma.CP3.emptyRegistrationIndex

advanceConcreteScannerEvent : ScannerEvent Nat -> ConcreteScannerIndexes ->
  ConcreteScannerIndexes
advanceConcreteScannerEvent
  (ScannerLeftDiscard (MkRegistrationGeneration child ordinal))
  (MkConcreteScannerIndexes left right) =
    MkConcreteScannerIndexes
      (advanceDeletedRegistrationIndex ordinal child 0 fixtureComponent left)
      right
advanceConcreteScannerEvent
  (ScannerRightDiscard (MkRegistrationGeneration child ordinal))
  (MkConcreteScannerIndexes left right) =
    MkConcreteScannerIndexes left
      (advanceDeletedRegistrationIndex ordinal child 0 fixtureComponent right)
advanceConcreteScannerEvent _ indexes = indexes

runConcreteScannerEvents : List (ScannerEvent Nat) -> ConcreteScannerIndexes ->
  ConcreteScannerIndexes
runConcreteScannerEvents [] indexes = indexes
runConcreteScannerEvents (event :: rest) indexes =
  runConcreteScannerEvents rest (advanceConcreteScannerEvent event indexes)

public export
leftBirth6 : RegistrationGeneration Nat
leftBirth6 = MkRegistrationGeneration 1 6

public export
leftBirth18 : RegistrationGeneration Nat
leftBirth18 = MkRegistrationGeneration 1 18

public export
rightBirth9 : RegistrationGeneration Nat
rightBirth9 = MkRegistrationGeneration 1 9

public export
rightBirth14 : RegistrationGeneration Nat
rightBirth14 = MkRegistrationGeneration 1 14

concreteTargetDiscardOrder : List (ScannerEvent Nat)
concreteTargetDiscardOrder =
  [ ScannerLeftDiscard leftBirth6
  , ScannerRightDiscard rightBirth9
  , ScannerLeftDiscard leftBirth18
  , ScannerRightDiscard rightBirth14
  ]

concreteReorderedTargetDiscards : List (ScannerEvent Nat)
concreteReorderedTargetDiscards =
  [ ScannerRightDiscard rightBirth9
  , ScannerLeftDiscard leftBirth6
  , ScannerRightDiscard rightBirth14
  , ScannerLeftDiscard leftBirth18
  ]

concreteThirdTargetDiscards : List (ScannerEvent Nat)
concreteThirdTargetDiscards =
  [ ScannerLeftDiscard leftBirth6
  , ScannerRightDiscard rightBirth9
  , ScannerRightDiscard rightBirth14
  , ScannerLeftDiscard leftBirth18
  ]

public export
concreteTargetFinalIndexes : ConcreteScannerIndexes
concreteTargetFinalIndexes =
  runConcreteScannerEvents concreteTargetDiscardOrder concreteEmptyIndexes

public export
concreteReorderedFinalIndexes : ConcreteScannerIndexes
concreteReorderedFinalIndexes =
  runConcreteScannerEvents concreteReorderedTargetDiscards concreteEmptyIndexes

public export
concreteThirdFinalIndexes : ConcreteScannerIndexes
concreteThirdFinalIndexes =
  runConcreteScannerEvents concreteThirdTargetDiscards concreteEmptyIndexes

public export
0 concreteTargetIndexesExact :
  DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetFinalIndexes =
    MkConcreteScannerIndexes
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
        , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ])
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
        , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
concreteTargetIndexesExact = Refl

public export
0 concreteReorderedIndexesExact :
  DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedFinalIndexes =
    MkConcreteScannerIndexes
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
        , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ])
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
        , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
concreteReorderedIndexesExact = Refl

public export
0 concreteThirdIndexesExact :
  DGamma.CP5ConfluenceRenamingCompositionSpike.concreteThirdFinalIndexes =
    MkConcreteScannerIndexes
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
        , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ])
      (MkRegistrationIndexState
        [(1, DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14)] [] []
        [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
        , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ])
concreteThirdIndexesExact = Refl

public export
0 concreteTargetDeletedListsExact :
  ( indexedDeletedGenerations (concreteLeftIndex
      DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetFinalIndexes) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
      , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ]
  , indexedDeletedGenerations (concreteRightIndex
      DGamma.CP5ConfluenceRenamingCompositionSpike.concreteTargetFinalIndexes) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
      , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ]
  )
concreteTargetDeletedListsExact = (Refl, Refl)

public export
0 concreteReorderedDeletedListsExact :
  ( indexedDeletedGenerations (concreteLeftIndex
      DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedFinalIndexes) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
      , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ]
  , indexedDeletedGenerations (concreteRightIndex
      DGamma.CP5ConfluenceRenamingCompositionSpike.concreteReorderedFinalIndexes) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
      , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ]
  )
concreteReorderedDeletedListsExact = (Refl, Refl)

public export
0 concreteThirdDeletedListsExact :
  ( indexedDeletedGenerations (concreteLeftIndex
      DGamma.CP5ConfluenceRenamingCompositionSpike.concreteThirdFinalIndexes) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth18
      , DGamma.CP5ConfluenceRenamingCompositionSpike.leftBirth6 ]
  , indexedDeletedGenerations (concreteRightIndex
      DGamma.CP5ConfluenceRenamingCompositionSpike.concreteThirdFinalIndexes) =
      [ DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth14
      , DGamma.CP5ConfluenceRenamingCompositionSpike.rightBirth9 ]
  )
concreteThirdDeletedListsExact = (Refl, Refl)

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
  (replayedOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value (canonicalTrace (canonicalSchedule leftCapital))
      replayedLeftTrace) ->
  ReplayedCanonicalEndpointBridge name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital replayedLeftTrace
      replayedOccurrences rightCapital ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
replayedCanonicalToOriginalEndpointSpike =
  ?replayedCanonicalToOriginalEndpointSpike_rhs
