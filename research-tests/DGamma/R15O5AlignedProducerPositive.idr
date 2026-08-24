module DGamma.R15O5AlignedProducerPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| A genuine O/O source pair is selected from a replay bundle owned by the
||| sorting/block producer.  Orientation is irrelevant to dictionary alignment.
0 alignedOrchestrationPairFromReplayBundle :
  (premises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq
    (MoreTransitions left (MoreTransitions right suffix))) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
alignedOrchestrationPairFromReplayBundle premises with (replayAligned premises)
  alignedOrchestrationPairFromReplayBundle premises |
      (AlignedStep leftAction leftTag leftChecked _
        (AlignedStep rightAction rightTag rightChecked _ _)) =
    AlignedStep leftAction leftTag leftChecked
      (MoreTransitions
        (Fired nameEq keyEq rightAction rightTag rightChecked) NoTransitions)
      (AlignedStep rightAction rightTag rightChecked NoTransitions AlignedEnd)

||| A genuine O5 producer evaluates the early orchestration with the outer
||| dictionaries and definitionally retains singleton alignment for that exact
||| checked transition.
0 alignedEarlyOrchestrationFromChecked :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, earlyFinal : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first =
    Just (tag, earlyFinal)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = earlyFinal}
        nameEq keyEq action tag checked) NoTransitions)
alignedEarlyOrchestrationFromChecked nameEq keyEq action tag checked =
  AlignedStep action tag checked NoTransitions AlignedEnd

||| Together these are exactly the two erased inputs authorized for revision 15.
0 genuineO5AlignmentCapital :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, earlyFinal : SystemState name key value world error} ->
  (premises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq
    (MoreTransitions left (MoreTransitions right suffix))) ->
  (earlyAction : Action name key value world error) ->
  (earlyTag : RuleTag) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq} earlyAction first =
    Just (earlyTag, earlyFinal)) ->
  ( AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions left (MoreTransitions right NoTransitions))
  , AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions
        (Fired {before = first} {afterState = earlyFinal}
          nameEq keyEq earlyAction earlyTag earlyChecked) NoTransitions)
  )
genuineO5AlignmentCapital nameEq keyEq premises earlyAction earlyTag
  earlyChecked =
    ( alignedOrchestrationPairFromReplayBundle premises
    , alignedEarlyOrchestrationFromChecked nameEq keyEq earlyAction earlyTag
        earlyChecked
    )

||| Strong revision-15 producer check: construct `OrchestrationSwapSafety` around
||| the actual outer-dictionary early transition, build the singleton indexed by
||| exactly `earlyRight safety`, and call O5 without transporting dictionaries.
0 genuineSafetyIndexedO5Application :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal, earlyFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  Not (transitionActor left = transitionActor right) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (transitionAction right) first =
      Just (transitionTag right, earlyFinal)) ->
  (sourceDiscipline : RegistrationDiscipline protocol nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment name) ->
  (endOrdinal : Nat) -> (endLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq startOrdinal startLive
    (MoreTransitions left (MoreTransitions right NoTransitions))
    endOrdinal endLive ->
  ((leftChild, rightChild : name) ->
    (leftParent, rightParent : Parent name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left = OInsert leftChild leftParent leftComponent ->
    transitionAction right = OInsert rightChild rightParent rightComponent ->
    Not (leftChild = rightChild)) ->
  ((leftChild, leftParent, rightChild, rightParent : name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left =
      OInsert leftChild (ChildOf leftParent) leftComponent ->
    transitionAction right =
      OInsert rightChild (ChildOf rightParent) rightComponent ->
    (Not (leftChild = rightParent), Not (rightChild = leftParent))) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
genuineSafetyIndexedO5Application nameEq keyEq protocol left right sourceAligned
  leftPaper rightPaper distinct earlyChecked sourceDiscipline startOrdinal
  startLive endOrdinal endLive scan insertedDistinct licenses =
    let early : Transition first earlyFinal
        early = Fired nameEq keyEq (transitionAction right)
          (transitionTag right) earlyChecked
        safety : OrchestrationSwapSafety name key world error value protocol
          nameEq keyEq left right
        safety = MkOrchestrationSwapSafety earlyFinal early Refl Refl
          sourceDiscipline startOrdinal startLive endOrdinal endLive scan
          insertedDistinct licenses
        0 earlyAligned : AlignedTransitions name key world error value nameEq
          keyEq (MoreTransitions (earlyRight safety) NoTransitions)
        earlyAligned = AlignedStep (transitionAction right) (transitionTag right)
          earlyChecked NoTransitions AlignedEnd
    in orchestrationOrchestrationDiamondSpike nameEq keyEq protocol left right
      sourceAligned leftPaper rightPaper distinct safety earlyAligned

||| Revision 17 replacement witness for the exact case that made the retired
||| ordered endpoint Void: two distinct checked, prepending O-Insert actions,
||| no suffix, and the genuine outer dictionaries. The endpoint is now directly
||| constructible because controls are compared by actor-name lookup.
0 genuineSuffixFreeDistinctInsertEndpoint :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal, earlyFinal :
    SystemState name key value world error} ->
  (leftActor, rightActor : name) ->
  (distinct : Not (leftActor = rightActor)) ->
  (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor leftParent leftComponent) first =
      Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) middle =
      Just (rightTag, originalFinal)) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) first =
      Just (rightTag, earlyFinal)) ->
  (sourceDiscipline : RegistrationDiscipline protocol nameEq
    (MoreTransitions
      (Fired nameEq keyEq (OInsert leftActor leftParent leftComponent)
        leftTag leftChecked)
      (MoreTransitions
        (Fired nameEq keyEq (OInsert rightActor rightParent rightComponent)
          rightTag rightChecked)
        NoTransitions))) ->
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment name) ->
  (endOrdinal : Nat) -> (endLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq startOrdinal startLive
    (MoreTransitions
      (Fired nameEq keyEq (OInsert leftActor leftParent leftComponent)
        leftTag leftChecked)
      (MoreTransitions
        (Fired nameEq keyEq (OInsert rightActor rightParent rightComponent)
          rightTag rightChecked)
        NoTransitions)) endOrdinal endLive ->
  (licenses : (leftChild, leftParentName, rightChild, rightParentName : name) ->
    (candidateLeft, candidateRight : Component key value world error) ->
    OInsert leftActor leftParent leftComponent =
      OInsert leftChild (ChildOf leftParentName) candidateLeft ->
    OInsert rightActor rightParent rightComponent =
      OInsert rightChild (ChildOf rightParentName) candidateRight ->
    (Not (leftChild = rightParentName),
     Not (rightChild = leftParentName))) ->
  (swapped : SystemState name key value world error **
    RelationalReplayEndpoint name key world error value nameEq keyEq
      originalFinal swapped)
genuineSuffixFreeDistinctInsertEndpoint nameEq keyEq protocol leftActor rightActor
  distinct leftParent rightParent leftComponent rightComponent leftChecked
  rightChecked earlyChecked sourceDiscipline startOrdinal startLive endOrdinal
  endLive scan licenses =
    let left : Transition first middle
        left = Fired nameEq keyEq
          (OInsert leftActor leftParent leftComponent) leftTag leftChecked
        right : Transition middle originalFinal
        right = Fired nameEq keyEq
          (OInsert rightActor rightParent rightComponent) rightTag rightChecked
        0 sourceAligned : AlignedTransitions name key world error value nameEq
          keyEq (MoreTransitions left (MoreTransitions right NoTransitions))
        sourceAligned = AlignedStep
          (OInsert leftActor leftParent leftComponent) leftTag leftChecked
          (MoreTransitions right NoTransitions)
          (AlignedStep (OInsert rightActor rightParent rightComponent) rightTag
            rightChecked NoTransitions AlignedEnd)
        early : Transition first earlyFinal
        early = Fired nameEq keyEq
          (OInsert rightActor rightParent rightComponent) rightTag earlyChecked
        insertedDistinct : (leftChild, rightChild : name) ->
          (candidateLeftParent, candidateRightParent : Parent name) ->
          (candidateLeft, candidateRight : Component key value world error) ->
          transitionAction left =
            OInsert leftChild candidateLeftParent candidateLeft ->
          transitionAction right =
            OInsert rightChild candidateRightParent candidateRight ->
          Not (leftChild = rightChild)
        insertedDistinct leftActor rightActor leftParent rightParent leftComponent
          rightComponent Refl Refl = distinct
        safety : OrchestrationSwapSafety name key world error value protocol
          nameEq keyEq left right
        safety = MkOrchestrationSwapSafety earlyFinal early Refl Refl
          sourceDiscipline startOrdinal startLive endOrdinal endLive scan
          insertedDistinct licenses
        0 earlyAligned : AlignedTransitions name key world error value nameEq
          keyEq (MoreTransitions (earlyRight safety) NoTransitions)
        earlyAligned = AlignedStep
          (OInsert rightActor rightParent rightComponent) rightTag earlyChecked
          NoTransitions AlignedEnd
        diamond : LocalRelationalDiamond name key world error value nameEq keyEq
          left right
        diamond = orchestrationOrchestrationDiamondSpike nameEq keyEq protocol
          left right sourceAligned (PaperInsertStep Refl) (PaperInsertStep Refl)
          distinct safety earlyAligned
    in (swappedFinal diamond **
      MkRelationalReplayEndpoint (swappedEffects diamond)
        (swappedControlEquivalent diamond) (swappedWellFormed diamond))
