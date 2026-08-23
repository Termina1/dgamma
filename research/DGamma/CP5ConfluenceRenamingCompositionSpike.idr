module DGamma.CP5ConfluenceRenamingCompositionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%hide Data.List.index

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

0 registrationSideSurvivingEvents :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {ordinal : Nat} -> {index, finalIndex : RegistrationIndexState name} ->
  RegistrationSideScan nameEq ordinal index trace finalIndex ->
  List (RegistrationEvent name key world error value)
registrationSideSurvivingEvents RegistrationSideScanEnd = []
registrationSideSurvivingEvents
  (RegistrationSideScanNonRegistration _ _ _ _ _ later) =
    registrationSideSurvivingEvents later
registrationSideSurvivingEvents
  (RegistrationSideScanDeleted _ _ _ _ later) =
    registrationSideSurvivingEvents later
registrationSideSurvivingEvents {ordinal} {index}
  (RegistrationSideScanSurviving {child} {parent} {component}
    transition rest actionExact surviving later) =
      registrationEventAt @{nameEq} ordinal index child parent component ::
        registrationSideSurvivingEvents later

0 registrationSideSurvivingEventsUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {ordinal : Nat} -> {index : RegistrationIndexState name} ->
  {leftResult, rightResult : RegistrationIndexState name} ->
  (leftScan : RegistrationSideScan nameEq ordinal index trace leftResult) ->
  (rightScan : RegistrationSideScan nameEq ordinal index trace rightResult) ->
  registrationSideSurvivingEvents leftScan =
    registrationSideSurvivingEvents rightScan
registrationSideSurvivingEventsUnique RegistrationSideScanEnd
  RegistrationSideScanEnd = Refl
registrationSideSurvivingEventsUnique
  (RegistrationSideScanNonRegistration leftAction transition rest leftExact
    leftNotRegistration leftLater)
  (RegistrationSideScanNonRegistration rightAction transition rest rightExact
    rightNotRegistration rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => registrationSideSurvivingEventsUnique leftLater rightLater
registrationSideSurvivingEventsUnique
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration later)
  (RegistrationSideScanDeleted transition rest generatedExact deleted
    rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideSurvivingEventsUnique
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration later)
  (RegistrationSideScanSurviving transition rest generatedExact surviving
    rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideSurvivingEventsUnique
  (RegistrationSideScanDeleted transition rest generatedExact deleted leftLater)
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideSurvivingEventsUnique
  (RegistrationSideScanSurviving transition rest generatedExact surviving
    leftLater)
  (RegistrationSideScanNonRegistration action transition rest actionExact
    notRegistration rightLater) =
      void (nonRegistrationCannotBeGenerated actionExact notRegistration
        generatedExact)
registrationSideSurvivingEventsUnique
  (RegistrationSideScanDeleted transition rest leftExact leftDeleted leftLater)
  (RegistrationSideScanDeleted transition rest rightExact rightDeleted
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => registrationSideSurvivingEventsUnique leftLater rightLater
registrationSideSurvivingEventsUnique
  (RegistrationSideScanDeleted transition rest leftExact leftDeleted leftLater)
  (RegistrationSideScanSurviving transition rest rightExact rightSurviving
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => void (survivingDeletedRegistrationImpossible rightSurviving
          leftDeleted)
registrationSideSurvivingEventsUnique
  (RegistrationSideScanSurviving transition rest leftExact leftSurviving
    leftLater)
  (RegistrationSideScanDeleted transition rest rightExact rightDeleted
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => void (survivingDeletedRegistrationImpossible leftSurviving
          rightDeleted)
registrationSideSurvivingEventsUnique {ordinal} {index}
  (RegistrationSideScanSurviving {child = leftChild} {parent = leftParent}
    {component = leftComponent} transition rest leftExact leftSurviving
    leftLater)
  (RegistrationSideScanSurviving {child = rightChild} {parent = rightParent}
    {component = rightComponent} transition rest rightExact rightSurviving
    rightLater) =
      case trans (sym leftExact) rightExact of
        Refl => cong
          (registrationEventAt @{nameEq} ordinal index leftChild leftParent
            leftComponent ::)
          (registrationSideSurvivingEventsUnique leftLater rightLater)

0 leftCorrespondenceSurvivingEvents :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftIndex, leftResultIndex, rightIndex, rightResultIndex :
    RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq renaming
    leftOrdinal leftIndex left leftResultIndex
    rightOrdinal rightIndex right rightResultIndex pendingLeft pendingRight ->
  List (RegistrationEvent name key world error value)
leftCorrespondenceSurvivingEvents RegistrationCorrespondenceEnd = []
leftCorrespondenceSurvivingEvents
  (SkipLeftNonRegistration _ _ _ _ _ correspondence) =
    leftCorrespondenceSurvivingEvents correspondence
leftCorrespondenceSurvivingEvents
  (SkipRightNonRegistration _ _ _ _ _ correspondence) =
    leftCorrespondenceSurvivingEvents correspondence
leftCorrespondenceSurvivingEvents
  (DiscardLeftDeletedRegistration _ _ _ _ correspondence) =
    leftCorrespondenceSurvivingEvents correspondence
leftCorrespondenceSurvivingEvents
  (DiscardRightDeletedRegistration _ _ _ _ correspondence) =
    leftCorrespondenceSurvivingEvents correspondence
leftCorrespondenceSurvivingEvents {leftOrdinal} {leftIndex}
  (QueueLeftGeneratedRegistration {child} {parent} {component}
    _ _ _ _ correspondence) =
      registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component ::
        leftCorrespondenceSurvivingEvents correspondence
leftCorrespondenceSurvivingEvents
  (QueueRightGeneratedRegistration _ _ _ _ correspondence) =
    leftCorrespondenceSurvivingEvents correspondence
leftCorrespondenceSurvivingEvents {leftOrdinal} {leftIndex}
  (MatchLeftWithPendingRight {child} {parent} {component}
    _ _ _ _ _ _ _ _ correspondence) =
      registrationEventAt @{nameEq} leftOrdinal leftIndex child parent component ::
        leftCorrespondenceSurvivingEvents correspondence
leftCorrespondenceSurvivingEvents
  (MatchRightWithPendingLeft _ _ _ _ _ _ _ _ correspondence) =
    leftCorrespondenceSurvivingEvents correspondence

0 rightCorrespondenceSurvivingEvents :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {left : Transitions leftFirst leftFinal} ->
  {right : Transitions rightFirst rightFinal} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftIndex, leftResultIndex, rightIndex, rightResultIndex :
    RegistrationIndexState name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq renaming
    leftOrdinal leftIndex left leftResultIndex
    rightOrdinal rightIndex right rightResultIndex pendingLeft pendingRight ->
  List (RegistrationEvent name key world error value)
rightCorrespondenceSurvivingEvents RegistrationCorrespondenceEnd = []
rightCorrespondenceSurvivingEvents
  (SkipLeftNonRegistration _ _ _ _ _ correspondence) =
    rightCorrespondenceSurvivingEvents correspondence
rightCorrespondenceSurvivingEvents
  (SkipRightNonRegistration _ _ _ _ _ correspondence) =
    rightCorrespondenceSurvivingEvents correspondence
rightCorrespondenceSurvivingEvents
  (DiscardLeftDeletedRegistration _ _ _ _ correspondence) =
    rightCorrespondenceSurvivingEvents correspondence
rightCorrespondenceSurvivingEvents
  (DiscardRightDeletedRegistration _ _ _ _ correspondence) =
    rightCorrespondenceSurvivingEvents correspondence
rightCorrespondenceSurvivingEvents
  (QueueLeftGeneratedRegistration _ _ _ _ correspondence) =
    rightCorrespondenceSurvivingEvents correspondence
rightCorrespondenceSurvivingEvents {rightOrdinal} {rightIndex}
  (QueueRightGeneratedRegistration {child} {parent} {component}
    _ _ _ _ correspondence) =
      registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component ::
        rightCorrespondenceSurvivingEvents correspondence
rightCorrespondenceSurvivingEvents
  (MatchLeftWithPendingRight _ _ _ _ _ _ _ _ correspondence) =
    rightCorrespondenceSurvivingEvents correspondence
rightCorrespondenceSurvivingEvents {rightOrdinal} {rightIndex}
  (MatchRightWithPendingLeft {child} {parent} {component}
    _ _ _ _ _ _ _ _ correspondence) =
      registrationEventAt @{nameEq} rightOrdinal rightIndex child parent component ::
        rightCorrespondenceSurvivingEvents correspondence

||| Finite matching semantics of the scanner's two pending lists. Queue
||| constructors retain an unmatched event; match constructors remove an exact
||| pending occurrence. Thus a value indexed by `[] []` is a perfect finite
||| matching process, not merely a list of independently supplied event pairs.
data FiniteRegistrationMatchingPlan :
  (renaming : RegistrationGenerationBijection name) ->
  (pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)) -> Type where
  FiniteRegistrationMatchingEnd :
    FiniteRegistrationMatchingPlan renaming [] []
  FiniteRegistrationMatchingQueueLeft :
    (event : RegistrationEvent name key world error value) ->
    FiniteRegistrationMatchingPlan renaming (event :: pendingLeft) pendingRight ->
    FiniteRegistrationMatchingPlan renaming pendingLeft pendingRight
  FiniteRegistrationMatchingQueueRight :
    (event : RegistrationEvent name key world error value) ->
    FiniteRegistrationMatchingPlan renaming pendingLeft (event :: pendingRight) ->
    FiniteRegistrationMatchingPlan renaming pendingLeft pendingRight
  FiniteRegistrationMatchingMatchLeft :
    (leftEvent : RegistrationEvent name key world error value) ->
    (rightPrefix : List (RegistrationEvent name key world error value)) ->
    (rightEvent : RegistrationEvent name key world error value) ->
    (rightSuffix : List (RegistrationEvent name key world error value)) ->
    RegistrationEventMatch renaming leftEvent rightEvent ->
    FiniteRegistrationMatchingPlan renaming pendingLeft
      (rightPrefix ++ rightSuffix) ->
    FiniteRegistrationMatchingPlan renaming pendingLeft
      (rightPrefix ++ (rightEvent :: rightSuffix))
  FiniteRegistrationMatchingMatchRight :
    (rightEvent : RegistrationEvent name key world error value) ->
    (leftPrefix : List (RegistrationEvent name key world error value)) ->
    (leftEvent : RegistrationEvent name key world error value) ->
    (leftSuffix : List (RegistrationEvent name key world error value)) ->
    RegistrationEventMatch renaming leftEvent rightEvent ->
    FiniteRegistrationMatchingPlan renaming
      (leftPrefix ++ leftSuffix) pendingRight ->
    FiniteRegistrationMatchingPlan renaming
      (leftPrefix ++ (leftEvent :: leftSuffix)) pendingRight

0 finiteRegistrationMatchingPlan :
  RegistrationTraceCorrespondence nameEq renaming
    leftOrdinal leftIndex left leftResultIndex
    rightOrdinal rightIndex right rightResultIndex pendingLeft pendingRight ->
  FiniteRegistrationMatchingPlan renaming pendingLeft pendingRight
finiteRegistrationMatchingPlan RegistrationCorrespondenceEnd =
  FiniteRegistrationMatchingEnd
finiteRegistrationMatchingPlan
  (SkipLeftNonRegistration _ _ _ _ _ correspondence) =
    finiteRegistrationMatchingPlan correspondence
finiteRegistrationMatchingPlan
  (SkipRightNonRegistration _ _ _ _ _ correspondence) =
    finiteRegistrationMatchingPlan correspondence
finiteRegistrationMatchingPlan
  (DiscardLeftDeletedRegistration _ _ _ _ correspondence) =
    finiteRegistrationMatchingPlan correspondence
finiteRegistrationMatchingPlan
  (DiscardRightDeletedRegistration _ _ _ _ correspondence) =
    finiteRegistrationMatchingPlan correspondence
finiteRegistrationMatchingPlan {leftOrdinal} {leftIndex}
  (QueueLeftGeneratedRegistration {child} {parent} {component}
    _ _ _ _ correspondence) =
      FiniteRegistrationMatchingQueueLeft
        (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
          component)
        (finiteRegistrationMatchingPlan correspondence)
finiteRegistrationMatchingPlan {rightOrdinal} {rightIndex}
  (QueueRightGeneratedRegistration {child} {parent} {component}
    _ _ _ _ correspondence) =
      FiniteRegistrationMatchingQueueRight
        (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent
          component)
        (finiteRegistrationMatchingPlan correspondence)
finiteRegistrationMatchingPlan {leftOrdinal} {leftIndex}
  (MatchLeftWithPendingRight {child} {parent} {component}
    _ _ _ _ rightPrefix rightEvent rightSuffix matched correspondence) =
      FiniteRegistrationMatchingMatchLeft
        (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
          component)
        rightPrefix rightEvent rightSuffix matched
        (finiteRegistrationMatchingPlan correspondence)
finiteRegistrationMatchingPlan {rightOrdinal} {rightIndex}
  (MatchRightWithPendingLeft {child} {parent} {component}
    _ _ _ _ leftPrefix leftEvent leftSuffix matched correspondence) =
      FiniteRegistrationMatchingMatchRight
        (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent
          component)
        leftPrefix leftEvent leftSuffix matched
        (finiteRegistrationMatchingPlan correspondence)

0 matchingPlanLeftEvents :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : RegistrationGenerationBijection name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  FiniteRegistrationMatchingPlan renaming pendingLeft pendingRight ->
  List (RegistrationEvent name key world error value)
matchingPlanLeftEvents FiniteRegistrationMatchingEnd = []
matchingPlanLeftEvents (FiniteRegistrationMatchingQueueLeft event later) =
  event :: matchingPlanLeftEvents later
matchingPlanLeftEvents (FiniteRegistrationMatchingQueueRight event later) =
  matchingPlanLeftEvents later
matchingPlanLeftEvents
  (FiniteRegistrationMatchingMatchLeft leftEvent _ _ _ _ later) =
    leftEvent :: matchingPlanLeftEvents later
matchingPlanLeftEvents
  (FiniteRegistrationMatchingMatchRight _ _ _ _ _ later) =
    matchingPlanLeftEvents later

0 matchingPlanRightEvents :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : RegistrationGenerationBijection name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  FiniteRegistrationMatchingPlan renaming pendingLeft pendingRight ->
  List (RegistrationEvent name key world error value)
matchingPlanRightEvents FiniteRegistrationMatchingEnd = []
matchingPlanRightEvents (FiniteRegistrationMatchingQueueLeft event later) =
  matchingPlanRightEvents later
matchingPlanRightEvents (FiniteRegistrationMatchingQueueRight event later) =
  event :: matchingPlanRightEvents later
matchingPlanRightEvents
  (FiniteRegistrationMatchingMatchLeft _ _ _ _ _ later) =
    matchingPlanRightEvents later
matchingPlanRightEvents
  (FiniteRegistrationMatchingMatchRight rightEvent _ _ _ _ later) =
    rightEvent :: matchingPlanRightEvents later

0 acceptedFiniteRegistrationMatchingPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {renaming : RegistrationGenerationBijection name} ->
  {leftFirst, leftFinal, rightFirst, rightFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions leftFirst leftFinal} ->
  {rightTrace : Transitions rightFirst rightFinal} ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq renaming
    leftTrace rightTrace) ->
  FiniteRegistrationMatchingPlan {key = key} {value = value} {world = world}
    {error = error} renaming [] []
acceptedFiniteRegistrationMatchingPlan registrations =
  finiteRegistrationMatchingPlan (generationTraceCorrespondence registrations)

||| Structural event folds avoid relying on reduction of nested dependent
||| projections.  Both folds expose the exact event list while retaining the
||| producer-built plan/scan value that authorized each event.
data MatchingPlanEventFold :
  {renaming : RegistrationGenerationBijection name} ->
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  FiniteRegistrationMatchingPlan renaming pendingLeft pendingRight ->
  List (RegistrationEvent name key world error value) ->
  List (RegistrationEvent name key world error value) -> Type where
  MatchingPlanEventFoldEnd :
    MatchingPlanEventFold FiniteRegistrationMatchingEnd [] []
  MatchingPlanEventFoldQueueLeft :
    (event : RegistrationEvent name key world error value) ->
    {pendingLeft, pendingRight :
      List (RegistrationEvent name key world error value)} ->
    {later : FiniteRegistrationMatchingPlan renaming
      (event :: pendingLeft) pendingRight} ->
    MatchingPlanEventFold later leftEvents rightEvents ->
    MatchingPlanEventFold
      (FiniteRegistrationMatchingQueueLeft event later)
      (event :: leftEvents) rightEvents
  MatchingPlanEventFoldQueueRight :
    (event : RegistrationEvent name key world error value) ->
    {pendingLeft, pendingRight :
      List (RegistrationEvent name key world error value)} ->
    {later : FiniteRegistrationMatchingPlan renaming pendingLeft
      (event :: pendingRight)} ->
    MatchingPlanEventFold later leftEvents rightEvents ->
    MatchingPlanEventFold
      (FiniteRegistrationMatchingQueueRight event later)
      leftEvents (event :: rightEvents)
  MatchingPlanEventFoldMatchLeft :
    (leftEvent : RegistrationEvent name key world error value) ->
    (rightPrefix : List (RegistrationEvent name key world error value)) ->
    (rightEvent : RegistrationEvent name key world error value) ->
    (rightSuffix : List (RegistrationEvent name key world error value)) ->
    (matched : RegistrationEventMatch renaming leftEvent rightEvent) ->
    {pendingLeft : List (RegistrationEvent name key world error value)} ->
    {later : FiniteRegistrationMatchingPlan renaming pendingLeft
      (rightPrefix ++ rightSuffix)} ->
    MatchingPlanEventFold later leftEvents rightEvents ->
    MatchingPlanEventFold
      (FiniteRegistrationMatchingMatchLeft leftEvent rightPrefix rightEvent
        rightSuffix matched later)
      (leftEvent :: leftEvents) rightEvents
  MatchingPlanEventFoldMatchRight :
    (rightEvent : RegistrationEvent name key world error value) ->
    (leftPrefix : List (RegistrationEvent name key world error value)) ->
    (leftEvent : RegistrationEvent name key world error value) ->
    (leftSuffix : List (RegistrationEvent name key world error value)) ->
    (matched : RegistrationEventMatch renaming leftEvent rightEvent) ->
    {pendingRight : List (RegistrationEvent name key world error value)} ->
    {later : FiniteRegistrationMatchingPlan renaming
      (leftPrefix ++ leftSuffix) pendingRight} ->
    MatchingPlanEventFold later leftEvents rightEvents ->
    MatchingPlanEventFold
      (FiniteRegistrationMatchingMatchRight rightEvent leftPrefix leftEvent
        leftSuffix matched later)
      leftEvents (rightEvent :: rightEvents)

data RegistrationSideEventFold :
  {nameEq : DecEq name} ->
  {ordinal : Nat} -> {index : RegistrationIndexState name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {finalIndex : RegistrationIndexState name} ->
  RegistrationSideScan nameEq ordinal index trace finalIndex ->
  List (RegistrationEvent name key world error value) -> Type where
  RegistrationSideEventFoldEnd :
    RegistrationSideEventFold RegistrationSideScanEnd []
  RegistrationSideEventFoldNonRegistration :
    {ordinal : Nat} ->
    {index, finalIndex : RegistrationIndexState name} ->
    {events : List (RegistrationEvent name key world error value)} ->
    (action : Action name key value world error) ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (actionExact : transitionAction transition = action) ->
    (notRegistration : isGeneratedRegistrationAction action = False) ->
    {later : RegistrationSideScan nameEq (S ordinal)
      (advanceRegistrationIndex @{nameEq} ordinal action index)
      rest finalIndex} ->
    RegistrationSideEventFold later events ->
    RegistrationSideEventFold
      (RegistrationSideScanNonRegistration {ordinal = ordinal} {index = index}
        action transition rest actionExact notRegistration later) events
  RegistrationSideEventFoldDeleted :
    {ordinal : Nat} ->
    {index, finalIndex : RegistrationIndexState name} ->
    {child, parent : name} ->
    {component : Component key value world error} ->
    {events : List (RegistrationEvent name key world error value)} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (actionExact : transitionAction transition =
      OInsert child (ChildOf parent) component) ->
    (deleted : DeletedClosingRegistration
      (registrationEventAt @{nameEq} ordinal index child parent component)
      rest) ->
    {later : RegistrationSideScan nameEq (S ordinal)
      (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component
        index) rest finalIndex} ->
    RegistrationSideEventFold later events ->
    RegistrationSideEventFold
      (RegistrationSideScanDeleted {ordinal = ordinal} {index = index}
        transition rest actionExact deleted later)
      events
  RegistrationSideEventFoldSurviving :
    {ordinal : Nat} ->
    {index, finalIndex : RegistrationIndexState name} ->
    {child, parent : name} ->
    {component : Component key value world error} ->
    {events : List (RegistrationEvent name key world error value)} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (actionExact : transitionAction transition =
      OInsert child (ChildOf parent) component) ->
    (surviving : SurvivingRegistration
      (registrationEventAt @{nameEq} ordinal index child parent component)
      rest) ->
    {later : RegistrationSideScan nameEq (S ordinal)
      (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent
        component index) rest finalIndex} ->
    RegistrationSideEventFold later events ->
    RegistrationSideEventFold
      (RegistrationSideScanSurviving {ordinal = ordinal} {index = index}
        transition rest actionExact surviving later)
      (registrationEventAt @{nameEq} ordinal index child parent component ::
        events)

||| A simultaneous standalone projection.  The same event-list values index
||| both the pending plan fold and the exact side scanner folds, so downstream
||| composition does not need nested equality rewriting.
record AlignedFiniteRegistrationProjection
  (nameEq : DecEq name) (renaming : RegistrationGenerationBijection name)
  (leftOrdinal : Nat) (leftIndex : RegistrationIndexState name)
  {leftFirst, leftFinal : SystemState name key value world error}
  (left : Transitions leftFirst leftFinal)
  (leftResultIndex : RegistrationIndexState name)
  (rightOrdinal : Nat) (rightIndex : RegistrationIndexState name)
  {rightFirst, rightFinal : SystemState name key value world error}
  (right : Transitions rightFirst rightFinal)
  (rightResultIndex : RegistrationIndexState name)
  (pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)) where
  constructor MkAlignedFiniteRegistrationProjection
  alignedMatchingPlan : FiniteRegistrationMatchingPlan renaming pendingLeft
    pendingRight
  alignedLeftScan : RegistrationSideScan nameEq leftOrdinal leftIndex left
    leftResultIndex
  alignedRightScan : RegistrationSideScan nameEq rightOrdinal rightIndex right
    rightResultIndex
  alignedLeftEvents : List (RegistrationEvent name key world error value)
  alignedRightEvents : List (RegistrationEvent name key world error value)
  0 alignedMatchingFold : MatchingPlanEventFold alignedMatchingPlan
    alignedLeftEvents alignedRightEvents
  0 alignedLeftFold : RegistrationSideEventFold alignedLeftScan alignedLeftEvents
  0 alignedRightFold : RegistrationSideEventFold alignedRightScan
    alignedRightEvents

0 alignFiniteRegistrationProjection :
  RegistrationTraceCorrespondence nameEq renaming
    leftOrdinal leftIndex left leftResultIndex
    rightOrdinal rightIndex right rightResultIndex pendingLeft pendingRight ->
  AlignedFiniteRegistrationProjection nameEq renaming leftOrdinal leftIndex left
    leftResultIndex rightOrdinal rightIndex right rightResultIndex pendingLeft
    pendingRight
alignFiniteRegistrationProjection RegistrationCorrespondenceEnd =
  MkAlignedFiniteRegistrationProjection
    FiniteRegistrationMatchingEnd RegistrationSideScanEnd
    RegistrationSideScanEnd [] [] MatchingPlanEventFoldEnd
    RegistrationSideEventFoldEnd RegistrationSideEventFoldEnd
alignFiniteRegistrationProjection
  (SkipLeftNonRegistration action transition rest actionExact notRegistration
    correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection plan
              (RegistrationSideScanNonRegistration action transition rest
                actionExact notRegistration leftScan)
              rightScan leftEvents rightEvents planFold
              (RegistrationSideEventFoldNonRegistration action transition rest
                actionExact notRegistration leftFold)
              rightFold
alignFiniteRegistrationProjection
  (SkipRightNonRegistration action transition rest actionExact notRegistration
    correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection plan leftScan
              (RegistrationSideScanNonRegistration action transition rest
                actionExact notRegistration rightScan)
              leftEvents rightEvents planFold leftFold
              (RegistrationSideEventFoldNonRegistration action transition rest
                actionExact notRegistration rightFold)
alignFiniteRegistrationProjection
  (DiscardLeftDeletedRegistration transition rest actionExact deleted
    correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection plan
              (RegistrationSideScanDeleted transition rest actionExact deleted
                leftScan)
              rightScan leftEvents rightEvents planFold
              (RegistrationSideEventFoldDeleted transition rest actionExact
                deleted leftFold)
              rightFold
alignFiniteRegistrationProjection
  (DiscardRightDeletedRegistration transition rest actionExact deleted
    correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection plan leftScan
              (RegistrationSideScanDeleted transition rest actionExact deleted
                rightScan)
              leftEvents rightEvents planFold leftFold
              (RegistrationSideEventFoldDeleted transition rest actionExact
                deleted rightFold)
alignFiniteRegistrationProjection {leftOrdinal} {leftIndex}
  (QueueLeftGeneratedRegistration {child} {parent} {component}
    transition rest actionExact surviving correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection
              (FiniteRegistrationMatchingQueueLeft
                (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
                  component) plan)
              (RegistrationSideScanSurviving transition rest actionExact
                surviving leftScan)
              rightScan
              (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
                component :: leftEvents)
              rightEvents
              (MatchingPlanEventFoldQueueLeft
                (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
                  component) planFold)
              (RegistrationSideEventFoldSurviving transition rest actionExact
                surviving leftFold)
              rightFold
alignFiniteRegistrationProjection {rightOrdinal} {rightIndex}
  (QueueRightGeneratedRegistration {child} {parent} {component}
    transition rest actionExact surviving correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection
              (FiniteRegistrationMatchingQueueRight
                (registrationEventAt @{nameEq} rightOrdinal rightIndex child
                  parent component) plan)
              leftScan
              (RegistrationSideScanSurviving transition rest actionExact
                surviving rightScan)
              leftEvents
              (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent
                component :: rightEvents)
              (MatchingPlanEventFoldQueueRight
                (registrationEventAt @{nameEq} rightOrdinal rightIndex child
                  parent component) planFold)
              leftFold
              (RegistrationSideEventFoldSurviving transition rest actionExact
                surviving rightFold)
alignFiniteRegistrationProjection {leftOrdinal} {leftIndex}
  (MatchLeftWithPendingRight {child} {parent} {component}
    transition rest actionExact surviving rightPrefix rightEvent rightSuffix
    matched correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection
              (FiniteRegistrationMatchingMatchLeft
                (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
                  component)
                rightPrefix rightEvent rightSuffix matched plan)
              (RegistrationSideScanSurviving transition rest actionExact
                surviving leftScan)
              rightScan
              (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
                component :: leftEvents)
              rightEvents
              (MatchingPlanEventFoldMatchLeft
                (registrationEventAt @{nameEq} leftOrdinal leftIndex child parent
                  component)
                rightPrefix rightEvent rightSuffix matched planFold)
              (RegistrationSideEventFoldSurviving transition rest actionExact
                surviving leftFold)
              rightFold
alignFiniteRegistrationProjection {rightOrdinal} {rightIndex}
  (MatchRightWithPendingLeft {child} {parent} {component}
    transition rest actionExact surviving leftPrefix leftEvent leftSuffix
    matched correspondence) =
      case alignFiniteRegistrationProjection correspondence of
        MkAlignedFiniteRegistrationProjection plan leftScan rightScan leftEvents
          rightEvents planFold leftFold rightFold =>
            MkAlignedFiniteRegistrationProjection
              (FiniteRegistrationMatchingMatchRight
                (registrationEventAt @{nameEq} rightOrdinal rightIndex child
                  parent component)
                leftPrefix leftEvent leftSuffix matched plan)
              leftScan
              (RegistrationSideScanSurviving transition rest actionExact
                surviving rightScan)
              leftEvents
              (registrationEventAt @{nameEq} rightOrdinal rightIndex child parent
                component :: rightEvents)
              (MatchingPlanEventFoldMatchRight
                (registrationEventAt @{nameEq} rightOrdinal rightIndex child
                  parent component)
                leftPrefix leftEvent leftSuffix matched planFold)
              leftFold
              (RegistrationSideEventFoldSurviving transition rest actionExact
                surviving rightFold)

||| Pending lists are newest-first.  `pendingChronology pending future` restores
||| their occurrence order before the not-yet-scanned future, and reduces
||| definitionally across queue constructors.
pendingChronology : List a -> List a -> List a
pendingChronology [] future = future
pendingChronology (event :: pending) future =
  pendingChronology pending (event :: future)

data RemoveListOccurrence : a -> List a -> List a -> Type where
  RemoveListHere : RemoveListOccurrence event (event :: rest) rest
  RemoveListThere : RemoveListOccurrence event events remainder ->
    RemoveListOccurrence event (other :: events) (other :: remainder)

0 appendNilRightLocal : (items : List a) -> items ++ [] = items
appendNilRightLocal [] = Refl
appendNilRightLocal (item :: items) =
  cong (item ::) (appendNilRightLocal items)

0 appendAssociativeLocal :
  (left, middle, right : List a) ->
  (left ++ middle) ++ right = left ++ (middle ++ right)
appendAssociativeLocal [] middle right = Refl
appendAssociativeLocal (item :: left) middle right =
  cong (item ::) (appendAssociativeLocal left middle right)

record ReversedRemovalDecomposition
  (selected : event) (source, remainder : List event) where
  constructor MkReversedRemovalDecomposition
  reversedPrefix : List event
  reversedSuffix : List event
  0 reversedSourceSplit : reverse source =
    reversedPrefix ++ (selected :: reversedSuffix)
  0 reversedRemainderSplit : reverse remainder =
    reversedPrefix ++ reversedSuffix

0 reverseRemovalDecomposition :
  RemoveListOccurrence selected source remainder ->
  ReversedRemovalDecomposition selected source remainder
reverseRemovalDecomposition {remainder = rest} RemoveListHere =
  MkReversedRemovalDecomposition (reverse rest) []
    (sym (revAppend [selected] rest))
    (sym (appendNilRightLocal (reverse rest)))
reverseRemovalDecomposition {source = other :: sourceTail}
  {remainder = other :: remainderTail} (RemoveListThere later) =
    case reverseRemovalDecomposition later of
      MkReversedRemovalDecomposition before after sourceSplit remainderSplit =>
        MkReversedRemovalDecomposition before (after ++ [other])
          (trans (sym (revAppend [other] sourceTail))
            (trans (cong (++ [other]) sourceSplit)
              (appendAssociativeLocal before (selected :: after) [other])))
          (trans (sym (revAppend [other] remainderTail))
            (trans (cong (++ [other]) remainderSplit)
              (appendAssociativeLocal before after [other])))

0 reversePendingChronology :
  (pending, future : List event) ->
  reverse (pendingChronology pending future) = reverse future ++ pending
reversePendingChronology [] future =
  sym (appendNilRightLocal (reverse future))
reversePendingChronology (queued :: pending) future =
  trans (reversePendingChronology pending (queued :: future))
    (trans
      (cong (++ pending) (sym (revAppend [queued] future)))
      (appendAssociativeLocal (reverse future) [queued] pending))

record PendingRemovalDecomposition
  (selected : event) (pending, chronologicalRemainder : List event) where
  constructor MkPendingRemovalDecomposition
  pendingPrefix : List event
  pendingSuffix : List event
  0 pendingSourceSplit : pending =
    pendingPrefix ++ (selected :: pendingSuffix)
  0 pendingRemainderSplit : reverse chronologicalRemainder =
    pendingPrefix ++ pendingSuffix

0 pendingRemovalDecomposition :
  RemoveListOccurrence selected (pendingChronology pending [])
    chronologicalRemainder ->
  PendingRemovalDecomposition selected pending chronologicalRemainder
pendingRemovalDecomposition removal =
  case reverseRemovalDecomposition removal of
    MkReversedRemovalDecomposition before after sourceSplit remainderSplit =>
      MkPendingRemovalDecomposition before after
        (trans (sym (reversePendingChronology pending [])) sourceSplit)
        remainderSplit

0 removeAfterPrefix :
  {eventType : Type} ->
  (before : List eventType) -> (selected : eventType) ->
  {future : List eventType} ->
  RemoveListOccurrence selected (before ++ (selected :: future))
    (before ++ future)
removeAfterPrefix [] selected = RemoveListHere
removeAfterPrefix (event :: before) selected =
  RemoveListThere (removeAfterPrefix before selected)

0 removeChronologyFutureAfter :
  {eventType : Type} ->
  (pending, before : List eventType) -> (selected : eventType) ->
  {future : List eventType} ->
  RemoveListOccurrence selected
    (pendingChronology pending (before ++ (selected :: future)))
    (pendingChronology pending (before ++ future))
removeChronologyFutureAfter [] before selected =
  removeAfterPrefix before selected
removeChronologyFutureAfter (event :: pending) before selected =
  removeChronologyFutureAfter pending (event :: before) selected

0 removeChronologyFutureHead :
  {eventType : Type} ->
  (pending : List eventType) -> (selected : eventType) ->
  {future : List eventType} ->
  RemoveListOccurrence selected
    (pendingChronology pending (selected :: future))
    (pendingChronology pending future)
removeChronologyFutureHead pending selected =
  removeChronologyFutureAfter pending [] selected

0 queuedEventRemoval :
  {eventType : Type} ->
  (before : List eventType) -> (selected : eventType) ->
  (suffix : List eventType) ->
  {future : List eventType} ->
  RemoveListOccurrence selected
    (pendingChronology (before ++ (selected :: suffix)) future)
    (pendingChronology (before ++ suffix) future)
queuedEventRemoval [] selected suffix =
  removeChronologyFutureHead suffix selected
queuedEventRemoval (event :: before) selected suffix =
  queuedEventRemoval before selected suffix

||| An occurrence-authenticated perfect matching.  Each step removes the exact
||| left and right occurrences justified by one scanner-produced event match.
data RegistrationPairing :
  (renaming : RegistrationGenerationBijection name) ->
  List (RegistrationEvent name key world error value) ->
  List (RegistrationEvent name key world error value) -> Type where
  RegistrationPairingEnd : RegistrationPairing renaming [] []
  RegistrationPairingStep :
    {leftEvent, rightEvent : RegistrationEvent name key world error value} ->
    {leftEvents, leftRemainder, rightEvents, rightRemainder :
      List (RegistrationEvent name key world error value)} ->
    RegistrationEventMatch renaming leftEvent rightEvent ->
    RemoveListOccurrence leftEvent leftEvents leftRemainder ->
    RemoveListOccurrence rightEvent rightEvents rightRemainder ->
    RegistrationPairing renaming leftRemainder rightRemainder ->
    RegistrationPairing renaming leftEvents rightEvents

||| Normalize pending-list execution into an occurrence-removal pairing. Queue
||| steps disappear definitionally; match steps become exact paired removals.
0 matchingPlanPairing :
  {pendingLeft, pendingRight :
    List (RegistrationEvent name key world error value)} ->
  {plan : FiniteRegistrationMatchingPlan renaming pendingLeft pendingRight} ->
  {leftEvents, rightEvents :
    List (RegistrationEvent name key world error value)} ->
  MatchingPlanEventFold plan leftEvents rightEvents ->
  RegistrationPairing renaming
    (pendingChronology pendingLeft leftEvents)
    (pendingChronology pendingRight rightEvents)
matchingPlanPairing MatchingPlanEventFoldEnd = RegistrationPairingEnd
matchingPlanPairing
  (MatchingPlanEventFoldQueueLeft event laterFold) =
    matchingPlanPairing laterFold
matchingPlanPairing
  (MatchingPlanEventFoldQueueRight event laterFold) =
    matchingPlanPairing laterFold
matchingPlanPairing {pendingLeft}
  (MatchingPlanEventFoldMatchLeft leftEvent rightPrefix rightEvent rightSuffix
    matched laterFold) =
      RegistrationPairingStep matched
        (removeChronologyFutureHead pendingLeft leftEvent)
        (queuedEventRemoval rightPrefix rightEvent rightSuffix)
        (matchingPlanPairing laterFold)
matchingPlanPairing {pendingRight}
  (MatchingPlanEventFoldMatchRight rightEvent leftPrefix leftEvent leftSuffix
    matched laterFold) =
      RegistrationPairingStep matched
        (queuedEventRemoval leftPrefix leftEvent leftSuffix)
        (removeChronologyFutureHead pendingRight rightEvent)
        (matchingPlanPairing laterFold)

0 registrationSideEventFoldExact :
  {scan : RegistrationSideScan nameEq ordinal index trace finalIndex} ->
  {events : List (RegistrationEvent name key world error value)} ->
  RegistrationSideEventFold scan events ->
  events = registrationSideSurvivingEvents scan
registrationSideEventFoldExact RegistrationSideEventFoldEnd = Refl
registrationSideEventFoldExact
  (RegistrationSideEventFoldNonRegistration _ _ _ _ _ laterFold) =
    case registrationSideEventFoldExact laterFold of Refl => Refl
registrationSideEventFoldExact
  (RegistrationSideEventFoldDeleted _ _ _ _ laterFold) =
    case registrationSideEventFoldExact laterFold of Refl => Refl
registrationSideEventFoldExact
  (RegistrationSideEventFoldSurviving _ _ _ _ laterFold) =
    case registrationSideEventFoldExact laterFold of Refl => Refl

0 alignedSideFoldEventsSame :
  {leftScan : RegistrationSideScan nameEq ordinal index trace leftResultIndex} ->
  {rightScan : RegistrationSideScan nameEq ordinal index trace
    rightResultIndex} ->
  {leftEvents, rightEvents :
    List (RegistrationEvent name key world error value)} ->
  RegistrationSideEventFold leftScan leftEvents ->
  RegistrationSideEventFold rightScan rightEvents ->
  leftEvents = rightEvents
alignedSideFoldEventsSame leftFold rightFold =
  trans (registrationSideEventFoldExact leftFold)
    (trans (registrationSideSurvivingEventsUnique _ _)
      (sym (registrationSideEventFoldExact rightFold)))

0 compareListRemovals :
  (first : RemoveListOccurrence firstEvent source firstRemainder) ->
  (second : RemoveListOccurrence secondEvent source secondRemainder) ->
  Either
    (firstEvent = secondEvent, firstRemainder = secondRemainder)
    (commonRemainder : List event **
      (RemoveListOccurrence secondEvent firstRemainder commonRemainder,
       RemoveListOccurrence firstEvent secondRemainder commonRemainder))
compareListRemovals RemoveListHere RemoveListHere = Left (Refl, Refl)
compareListRemovals RemoveListHere (RemoveListThere second) =
  Right (_ ** (second, RemoveListHere))
compareListRemovals (RemoveListThere first) RemoveListHere =
  Right (_ ** (RemoveListHere, first))
compareListRemovals {source = other :: sourceTail}
  (RemoveListThere first) (RemoveListThere second) =
  case compareListRemovals first second of
    Left (eventSame, remainderSame) =>
      Left (eventSame, cong (other ::) remainderSame)
    Right (common ** (secondAfterFirst, firstAfterSecond)) =>
      Right (_ ** (RemoveListThere secondAfterFirst,
        RemoveListThere firstAfterSecond))

0 commuteRemovalAfter :
  RemoveListOccurrence firstEvent source firstRemainder ->
  RemoveListOccurrence secondEvent firstRemainder commonRemainder ->
  (secondRemainder : List event **
    (RemoveListOccurrence secondEvent source secondRemainder,
     RemoveListOccurrence firstEvent secondRemainder commonRemainder))
commuteRemovalAfter RemoveListHere second =
  (_ ** (RemoveListThere second, RemoveListHere))
commuteRemovalAfter (RemoveListThere first) RemoveListHere =
  (_ ** (RemoveListHere, first))
commuteRemovalAfter (RemoveListThere first) (RemoveListThere second) =
  case commuteRemovalAfter first second of
    (secondRemainder ** (secondFromSource, firstFromSecond)) =>
      (_ ** (RemoveListThere secondFromSource,
        RemoveListThere firstFromSecond))

record PairingRightExtraction
  (renaming : RegistrationGenerationBijection name)
  (selectedRight : RegistrationEvent name key world error value)
  (leftEvents, rightEvents, rightRemainder :
    List (RegistrationEvent name key world error value)) where
  constructor MkPairingRightExtraction
  extractedLeftEvent : RegistrationEvent name key world error value
  extractedLeftRemainder :
    List (RegistrationEvent name key world error value)
  0 extractedEventMatch : RegistrationEventMatch renaming extractedLeftEvent
    selectedRight
  0 extractedLeftRemoval : RemoveListOccurrence extractedLeftEvent leftEvents
    extractedLeftRemainder
  0 extractedRemainderPairing : RegistrationPairing renaming
    extractedLeftRemainder rightRemainder

0 extractPairingRight :
  RegistrationPairing renaming leftEvents rightEvents ->
  RemoveListOccurrence selectedRight rightEvents rightRemainder ->
  PairingRightExtraction renaming selectedRight leftEvents rightEvents
    rightRemainder
extractPairingRight RegistrationPairingEnd removal impossible
extractPairingRight
  (RegistrationPairingStep matched leftRemoval rightRemoval laterPairing)
  selectedRemoval =
    case compareListRemovals rightRemoval selectedRemoval of
      Left (eventSame, remainderSame) =>
        case eventSame of
          Refl => case remainderSame of
            Refl => MkPairingRightExtraction _ _ matched leftRemoval laterPairing
      Right (common ** (selectedAfterRight, rightAfterSelected)) =>
        case extractPairingRight laterPairing selectedAfterRight of
          MkPairingRightExtraction selectedLeft selectedLeftRemainder
            selectedMatch selectedLeftAfterRight selectedLaterPairing =>
              case commuteRemovalAfter leftRemoval selectedLeftAfterRight of
                (leftAfterSelected **
                  (selectedFromLeft, rightFromLeftAfterSelected)) =>
                    MkPairingRightExtraction selectedLeft leftAfterSelected
                      selectedMatch selectedFromLeft
                      (RegistrationPairingStep matched
                        rightFromLeftAfterSelected rightAfterSelected
                        selectedLaterPairing)

0 pairingRightEmptyForcesLeftEmpty :
  RegistrationPairing renaming leftEvents [] -> leftEvents = []
pairingRightEmptyForcesLeftEmpty RegistrationPairingEnd = Refl
pairingRightEmptyForcesLeftEmpty
  (RegistrationPairingStep matched leftRemoval rightRemoval later) impossible

0 composeRegistrationPairings :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {leftEvents, middleEvents, rightEvents :
    List (RegistrationEvent name key world error value)} ->
  (leftRenaming, rightRenaming : RegistrationGenerationBijection name) ->
  RegistrationPairing leftRenaming leftEvents middleEvents ->
  RegistrationPairing rightRenaming middleEvents rightEvents ->
  RegistrationPairing
    (composeGenerationBijection leftRenaming rightRenaming)
    leftEvents rightEvents
composeRegistrationPairings leftRenaming rightRenaming leftPairing
  RegistrationPairingEnd =
    case pairingRightEmptyForcesLeftEmpty leftPairing of
      Refl => RegistrationPairingEnd
composeRegistrationPairings leftRenaming rightRenaming leftPairing
  (RegistrationPairingStep middleRightMatch middleRemoval rightRemoval
    rightLater) =
      case extractPairingRight leftPairing middleRemoval of
        MkPairingRightExtraction leftEvent leftRemainder leftMiddleMatch
          leftRemoval leftLater =>
            RegistrationPairingStep
              (composeRegistrationEventMatch leftRenaming rightRenaming
                leftMiddleMatch middleRightMatch)
              leftRemoval rightRemoval
              (composeRegistrationPairings leftRenaming rightRenaming leftLater
                rightLater)

||| Checked synchronization capital for the shared middle trace of two scanner
||| correspondences.  The asynchronous interleavings may differ, but their
||| side projections make exactly the same surviving/deleted decision and
||| therefore compute the same full registration index.
record SharedMiddleRegistrationSynchronization
  (nameEq : DecEq name)
  {initial, leftFinal, middleFinal, rightFinal :
    SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (middleTrace : Transitions initial middleFinal)
  (rightTrace : Transitions initial rightFinal)
  (leftRenaming, rightRenaming : RegistrationGenerationBijection name)
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftRenaming leftTrace middleTrace)
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightRenaming middleTrace rightTrace) where
  constructor MkSharedMiddleRegistrationSynchronization
  middleAsRightScan : RegistrationSideScan nameEq 0
    (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    middleTrace (rightFinalIndex leftRegistrations)
  middleAsLeftScan : RegistrationSideScan nameEq 0
    (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    middleTrace (leftFinalIndex rightRegistrations)
  0 sharedMiddleFinalIndex : rightFinalIndex leftRegistrations =
    leftFinalIndex rightRegistrations

0 synchronizeMiddleRegistrationScanners :
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftRenaming leftTrace middleTrace) ->
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightRenaming middleTrace rightTrace) ->
  SharedMiddleRegistrationSynchronization nameEq leftTrace middleTrace
    rightTrace leftRenaming rightRenaming leftRegistrations rightRegistrations
synchronizeMiddleRegistrationScanners leftRegistrations rightRegistrations =
  let leftScan = rightRegistrationSideScan
        (generationTraceCorrespondence leftRegistrations)
      rightScan = leftRegistrationSideScan
        (generationTraceCorrespondence rightRegistrations)
  in MkSharedMiddleRegistrationSynchronization leftScan rightScan
    (registrationSideScanFinalIndexUnique leftScan rightScan)

0 sharedMiddleSurvivingEventsSame :
  (synchronization : SharedMiddleRegistrationSynchronization nameEq leftTrace
    middleTrace rightTrace leftRenaming rightRenaming leftRegistrations
    rightRegistrations) ->
  registrationSideSurvivingEvents (middleAsRightScan synchronization) =
    registrationSideSurvivingEvents (middleAsLeftScan synchronization)
sharedMiddleSurvivingEventsSame synchronization =
  registrationSideSurvivingEventsUnique (middleAsRightScan synchronization)
    (middleAsLeftScan synchronization)

0 sharedMiddleLiveGenerationsSame :
  (synchronization : SharedMiddleRegistrationSynchronization nameEq leftTrace
    middleTrace rightTrace leftRenaming rightRenaming leftRegistrations
    rightRegistrations) ->
  rightFinalGenerations leftRegistrations =
    leftFinalGenerations rightRegistrations
sharedMiddleLiveGenerationsSame synchronization =
  cong indexedLiveGenerations (sharedMiddleFinalIndex synchronization)

0 sharedMiddleDeletedGenerationsSame :
  (synchronization : SharedMiddleRegistrationSynchronization nameEq leftTrace
    middleTrace rightTrace leftRenaming rightRenaming leftRegistrations
    rightRegistrations) ->
  rightDeletedGenerations leftRegistrations =
    leftDeletedGenerations rightRegistrations
sharedMiddleDeletedGenerationsSame synchronization =
  cong indexedDeletedGenerations (sharedMiddleFinalIndex synchronization)

record AcceptedComposedRegistrationPairing
  (nameEq : DecEq name)
  {initial, leftFinal, middleFinal, rightFinal :
    SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (middleTrace : Transitions initial middleFinal)
  (rightTrace : Transitions initial rightFinal)
  (leftRenaming, rightRenaming : RegistrationGenerationBijection name)
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftRenaming leftTrace middleTrace)
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightRenaming middleTrace rightTrace) where
  constructor MkAcceptedComposedRegistrationPairing
  acceptedLeftProjection : AlignedFiniteRegistrationProjection nameEq
    leftRenaming 0
    (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    leftTrace (leftFinalIndex leftRegistrations) 0
    (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    middleTrace (rightFinalIndex leftRegistrations) [] []
  acceptedRightProjection : AlignedFiniteRegistrationProjection nameEq
    rightRenaming 0
    (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    middleTrace (leftFinalIndex rightRegistrations) 0
    (the (RegistrationIndexState name) DGamma.CP3.emptyRegistrationIndex)
    rightTrace (rightFinalIndex rightRegistrations) [] []
  0 acceptedMiddleEventsSame :
    alignedRightEvents acceptedLeftProjection =
      alignedLeftEvents acceptedRightProjection
  acceptedComposedPairing : RegistrationPairing
    (composeGenerationBijection leftRenaming rightRenaming)
    (alignedLeftEvents acceptedLeftProjection)
    (alignedRightEvents acceptedRightProjection)

0 acceptedComposedRegistrationPairing :
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftRenaming leftTrace middleTrace) ->
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightRenaming middleTrace rightTrace) ->
  AcceptedComposedRegistrationPairing nameEq leftTrace middleTrace rightTrace
    leftRenaming rightRenaming leftRegistrations rightRegistrations
acceptedComposedRegistrationPairing leftRegistrations rightRegistrations =
  case alignFiniteRegistrationProjection
    (generationTraceCorrespondence leftRegistrations) of
    leftProjection@(MkAlignedFiniteRegistrationProjection leftPlan leftScan
      middleScan leftEvents middleEvents leftPlanFold leftScanFold
      middleScanFold) =>
        case alignFiniteRegistrationProjection
          (generationTraceCorrespondence rightRegistrations) of
          rightProjection@(MkAlignedFiniteRegistrationProjection middlePlan
            otherMiddleScan rightScan otherMiddleEvents rightEvents
            rightPlanFold otherMiddleScanFold rightScanFold) =>
              case alignedSideFoldEventsSame middleScanFold
                otherMiddleScanFold of
                Refl => MkAcceptedComposedRegistrationPairing
                  (MkAlignedFiniteRegistrationProjection leftPlan leftScan
                    middleScan leftEvents middleEvents leftPlanFold leftScanFold
                    middleScanFold)
                  (MkAlignedFiniteRegistrationProjection middlePlan
                    otherMiddleScan rightScan middleEvents rightEvents
                    rightPlanFold otherMiddleScanFold rightScanFold)
                  Refl
                  (composeRegistrationPairings leftRenaming rightRenaming
                    (matchingPlanPairing leftPlanFold)
                    (matchingPlanPairing rightPlanFold))

0 pendingChronologyEmptyIsReverse :
  (pending : List event) -> pendingChronology pending [] = reverse pending
pendingChronologyEmptyIsReverse pending =
  trans (sym (reverseInvolutive (pendingChronology pending [])))
    (cong reverse (reversePendingChronology pending []))

0 pendingChronologyFromReversed :
  (chronological, pending : List event) ->
  reverse chronological = pending ->
  pendingChronology pending [] = chronological
pendingChronologyFromReversed chronological pending reversed =
  trans (pendingChronologyEmptyIsReverse pending)
    (trans (cong reverse (sym reversed))
      (reverseInvolutive chronological))

0 pendingChronologyEmptyForcesPendingEmpty :
  (pending : List event) -> pendingChronology pending [] = [] -> pending = []
pendingChronologyEmptyForcesPendingEmpty pending chronologicalEmpty =
  trans (sym (reversePendingChronology pending []))
    (cong reverse chronologicalEmpty)

0 synthesizeRightRegistrationScanner :
  {leftOrdinal : Nat} -> {leftIndex : RegistrationIndexState name} ->
  {pendingLeft : List (RegistrationEvent name key world error value)} ->
  {rightOrdinal : Nat} -> {rightIndex, rightResultIndex :
    RegistrationIndexState name} ->
  {rightFirst, rightFinal : SystemState name key value world error} ->
  {right : Transitions rightFirst rightFinal} ->
  {rightScan : RegistrationSideScan nameEq rightOrdinal rightIndex right
    rightResultIndex} ->
  {rightEvents : List (RegistrationEvent name key world error value)} ->
  RegistrationSideEventFold rightScan rightEvents ->
  RegistrationPairing renaming (pendingChronology pendingLeft []) rightEvents ->
  RegistrationTraceCorrespondence nameEq renaming
    leftOrdinal leftIndex NoTransitions leftIndex
    rightOrdinal rightIndex right rightResultIndex pendingLeft []
synthesizeRightRegistrationScanner {pendingLeft}
  RegistrationSideEventFoldEnd pairing =
  case pairingRightEmptyForcesLeftEmpty pairing of
    chronologicalEmpty =>
      case pendingChronologyEmptyForcesPendingEmpty pendingLeft
        chronologicalEmpty of
        Refl => RegistrationCorrespondenceEnd
synthesizeRightRegistrationScanner
  (RegistrationSideEventFoldNonRegistration action transition rest actionExact
    notRegistration laterFold) pairing =
      SkipRightNonRegistration action transition rest actionExact
        notRegistration
        (synthesizeRightRegistrationScanner laterFold pairing)
synthesizeRightRegistrationScanner
  (RegistrationSideEventFoldDeleted transition rest actionExact deleted
    laterFold) pairing =
      DiscardRightDeletedRegistration transition rest actionExact deleted
        (synthesizeRightRegistrationScanner laterFold pairing)
synthesizeRightRegistrationScanner {pendingLeft}
  (RegistrationSideEventFoldSurviving transition rest actionExact surviving
    laterFold) pairing =
      case extractPairingRight pairing RemoveListHere of
        MkPairingRightExtraction leftEvent chronologicalRemainder matched
          leftRemoval laterPairing =>
            case pendingRemovalDecomposition {pending = pendingLeft}
              leftRemoval of
              MkPendingRemovalDecomposition before after pendingSplit
                remainderSplit =>
                  case pendingSplit of
                    Refl =>
                      case pendingChronologyFromReversed chronologicalRemainder
                        (before ++ after) remainderSplit of
                        Refl => MatchRightWithPendingLeft transition rest
                          actionExact surviving before leftEvent after matched
                          (synthesizeRightRegistrationScanner laterFold
                            laterPairing)

0 retargetVestigialEndpointIndex :
  {fromIndex, toIndex : RegistrationIndexState name} ->
  fromIndex = toIndex ->
  VestigialEndpointGeneration name key world error value nameEq keyEq
    (indexedLiveGenerations fromIndex) (indexedDeletedGenerations fromIndex)
    selected state ->
  VestigialEndpointGeneration name key world error value nameEq keyEq
    (indexedLiveGenerations toIndex) (indexedDeletedGenerations toIndex)
    selected state
retargetVestigialEndpointIndex Refl vestigial = vestigial

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
