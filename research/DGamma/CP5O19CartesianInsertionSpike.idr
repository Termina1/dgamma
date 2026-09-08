module DGamma.CP5O19CartesianInsertionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP4DeletionGenerationScan
import DGamma.CP5O19InsertionInsertionRowSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Project the actual source provenance at an occurrence. No replacement
||| component, source parent yield, or pair-discipline premise is invented.
export
0 o19ProvenanceAtOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  {initial, finalState, before, afterState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (step : Transition before afterState) ->
  OccursIn step source -> RegistrationProvenance protocol nameEq source ->
  RegistrationStepProvenance protocol nameEq (transitionAction step) before
o19ProvenanceAtOccurrence protocol nameEq _ _ OccursHere (RegistrationProvenanceStep _ _ head rest) = head
o19ProvenanceAtOccurrence protocol nameEq _ step (OccursLater occurs) (RegistrationProvenanceStep _ rest head remaining) =
  o19ProvenanceAtOccurrence protocol nameEq rest step occurs remaining

||| An actual insertion is not any parent recovery transition. This makes
||| retirement discipline of the finite O/O pair genuinely vacuous locally,
||| without dropping the original whole-source retirement discipline.
export
0 o19InsertionCannotRecover :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) -> (child, owner : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (transitionAction step = OInsert child parent component) ->
  ParentRecoveryStep owner step -> Void
o19InsertionCannotRecover step child owner parent component inserted (ParentLeaves action) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))
o19InsertionCannotRecover step child owner parent component inserted (ParentDivertsBefore action) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))
o19InsertionCannotRecover step child owner parent component inserted (ParentDivertsAfter action tag) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))
o19InsertionCannotRecover step child owner parent component inserted (ParentRaises action tag) =
  uninhabited (cong isLifecycleAction (trans (sym inserted) action))

||| Reconstruct finite insertion discipline from ACTUAL pointwise provenance
||| and explicit no-recovery evidence for that short suffix.
export
0 o19InsertionDisciplineFromProvenance :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (before : SystemState name key value world error) ->
  {afterState, finalState : SystemState name key value world error} ->
  (rest : Transitions afterState finalState) ->
  RegistrationStepProvenance protocol nameEq (OInsert child parent component) before ->
  ((owner : name) -> NoParentRecovery owner rest) ->
  RegistrationStepDiscipline protocol nameEq (OInsert child parent component) before rest
o19InsertionDisciplineFromProvenance protocol nameEq child Root component before rest provenance noRecovery = provenance
o19InsertionDisciplineFromProvenance protocol nameEq child (ChildOf owner) component before rest provenance noRecovery =
  (provenance, ParentDoesNotRecover (noRecovery owner))

||| The actual checked equation under the declared dictionaries, obtained by
||| eliminating alignment once rather than assuming dictionary equality.
export
0 o19AlignedHeadChecked :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {before, afterState, finalState : SystemState name key value world error} ->
  (step : Transition before afterState) -> (rest : Transitions afterState finalState) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest) ->
  (checkedApplyAction @{nameEq} @{keyEq} (transitionAction step) before = Just (transitionTag step, afterState))
o19AlignedHeadChecked nameEq keyEq _ _ (AlignedStep action tag checked rest remaining) = checked

||| Construct O/O safety from the SAME source bundle and actual early result.
||| Local retirement discipline is derived, and generation scanning starts at
||| the genuine scanned untouched prefix, never a reset ordinal/environment.
export
0 o19InsertionPairSafetyObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  (leftChild, rightChild : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) -> (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (transitionAction left = OInsert leftChild leftParent leftComponent) ->
  (transitionAction right = OInsert rightChild rightParent rightComponent) ->
  Not (rightChild = leftChild) ->
  ((licensor : name) -> (leftParent = ChildOf licensor) -> Not (rightChild = licensor)) ->
  ((licensor : name) -> (rightParent = ChildOf licensor) -> Not (leftChild = licensor)) ->
  (early : CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right)) ->
  (safety : OrchestrationSwapSafety name key world error value protocol nameEq keyEq left right **
    AlignedTransitions name key world error value nameEq keyEq (MoreTransitions (earlyRight safety) NoTransitions))
o19InsertionPairSafetyObserved {name} {key} {value} {world} {error} {first} {middle} {last}
  nameEq keyEq protocol leftChild rightChild leftParent rightParent leftComponent rightComponent
  source earlier left right later decomposition premises leftInsert rightInsert distinct leftLicense rightLicense early =
    (MkOrchestrationSwapSafety (earlyApplicationFinal early)
      (Fired {before = first} {afterState = earlyApplicationFinal early} nameEq keyEq
        (transitionAction right) (transitionTag right) (earlyApplicationChecked early)) Refl Refl
      (RegistrationDisciplineStep left (MoreTransitions right NoTransitions)
        (replace {p = \action => RegistrationStepDiscipline protocol nameEq action first (MoreTransitions right NoTransitions)} (sym leftInsert)
          (o19InsertionDisciplineFromProvenance protocol nameEq leftChild leftParent leftComponent first (MoreTransitions right NoTransitions)
            (replace {p = \action => RegistrationStepProvenance protocol nameEq action first} leftInsert
            (o19ProvenanceAtOccurrence protocol nameEq source left
              (replace {p = OccursIn left} decomposition (o19PairOccurrence earlier left right later left OccursHere))
              (replayProvenance premises))) (\owner => NoParentRecoveryStep right NoTransitions
            (o19InsertionCannotRecover right rightChild owner rightParent rightComponent rightInsert) NoParentRecoveryEnd)))
        (RegistrationDisciplineStep right NoTransitions
          (replace {p = \action => RegistrationStepDiscipline protocol nameEq action middle (NoTransitions {state = last})} (sym rightInsert)
          (o19InsertionDisciplineFromProvenance protocol nameEq rightChild rightParent rightComponent middle (NoTransitions {state = last})
            (replace {p = \action => RegistrationStepProvenance protocol nameEq action middle} rightInsert
            (o19ProvenanceAtOccurrence protocol nameEq source right
              (replace {p = OccursIn right} decomposition (o19PairOccurrence earlier left right later right (OccursLater OccursHere)))
              (replayProvenance premises))) (\owner => NoParentRecoveryEnd))) RegistrationDisciplineEnd))
      (scanFinalOrdinal (scanGenerations nameEq 0 [] earlier)) (scanFinalLive (scanGenerations nameEq 0 [] earlier))
      (scanFinalOrdinal (scanGenerations nameEq (scanFinalOrdinal (scanGenerations nameEq 0 [] earlier)) (scanFinalLive (scanGenerations nameEq 0 [] earlier)) (MoreTransitions left (MoreTransitions right NoTransitions))))
      (scanFinalLive (scanGenerations nameEq (scanFinalOrdinal (scanGenerations nameEq 0 [] earlier)) (scanFinalLive (scanGenerations nameEq 0 [] earlier)) (MoreTransitions left (MoreTransitions right NoTransitions))))
      (generationScan (scanGenerations nameEq (scanFinalOrdinal (scanGenerations nameEq 0 [] earlier)) (scanFinalLive (scanGenerations nameEq 0 [] earlier)) (MoreTransitions left (MoreTransitions right NoTransitions))))
      (\otherLeft, otherRight, otherLeftParent, otherRightParent, otherLeftComponent, otherRightComponent, leftSame, rightSame, collision =>
        distinct (trans (cong actionOwner (trans (sym rightInsert) rightSame))
          (trans (sym collision) (sym (cong actionOwner (trans (sym leftInsert) leftSame))))))
      (\otherLeft, otherLeftParent, otherRight, otherRightParent, otherLeftComponent, otherRightComponent, leftSame, rightSame =>
        (\collision => rightLicense otherRightParent
          (o19InsertParentInjective rightChild otherRight rightParent (ChildOf otherRightParent) rightComponent otherRightComponent
            (trans (sym rightInsert) rightSame))
          (trans (cong actionOwner (trans (sym leftInsert) leftSame)) collision),
         \collision => leftLicense otherLeftParent
          (o19InsertParentInjective leftChild otherLeft leftParent (ChildOf otherLeftParent) leftComponent otherLeftComponent
            (trans (sym leftInsert) leftSame))
          (trans (cong actionOwner (trans (sym rightInsert) rightSame)) collision))) **
     AlignedStep (transitionAction right) (transitionTag right) (earlyApplicationChecked early) NoTransitions AlignedEnd)


||| Derive the early O/O certificate from the SAME bundle/aligned pair.
||| Exact insertion tags are internal source shape, never a changed O19 premise.
export
0 o19InsertionPairEarly :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  (leftChild, rightChild : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) -> (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (transitionAction left = OInsert leftChild leftParent leftComponent) ->
  (transitionAction right = OInsert rightChild rightParent rightComponent) ->
  Not (rightChild = leftChild) ->
  ((licensor : name) -> (rightParent = ChildOf licensor) -> Not (leftChild = licensor)) ->
  (transitionTag right = OInsertTag) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first
    (transitionAction right) (transitionTag right)
o19InsertionPairEarly {first} {middle} {last} nameEq keyEq protocol leftChild rightChild leftParent rightParent
  leftComponent rightComponent source earlier left right later decomposition premises leftInsert rightInsert distinct rightLicense rightTag =
    o19EarlyLabels nameEq keyEq (OInsert rightChild rightParent rightComponent) (transitionAction right)
      OInsertTag (transitionTag right) rightInsert rightTag
      (o19InsertionBeforeCheckedPair nameEq keyEq leftChild rightChild leftParent rightParent leftComponent rightComponent
        first middle last (transitionTag left) (transitionTag right)
        (trans (cong (\action => checkedApplyAction @{nameEq} @{keyEq} action first) (sym leftInsert))
          (o19AlignedHeadChecked nameEq keyEq left (MoreTransitions right NoTransitions)
            (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))))
        (trans (cong (\action => checkedApplyAction @{nameEq} @{keyEq} action middle) (sym rightInsert))
          (o19AlignedHeadChecked nameEq keyEq right NoTransitions
            (Builtin.snd (alignedAppendSplit (MoreTransitions left NoTransitions) (MoreTransitions right NoTransitions)
              (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))))))
        distinct (\licensor, parentSame, collision => rightLicense licensor parentSame (sym collision))
        (Builtin.fst (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))))

||| Both generated insertion nodes are internal in the source and in the
||| actual diamond. Root/root transposition is deliberately NOT licensed.
export
0 o19GeneratedInsertionPairExternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftChild, rightChild, leftParent, rightParent : name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent) ->
  (transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions))
o19GeneratedInsertionPairExternal nameEq keyEq leftChild rightChild leftParent rightParent leftComponent rightComponent
  left right leftInsert rightInsert diamond =
    SkipLeftInternal left (MoreTransitions right NoTransitions) (childInsertCannotBeRoot left leftInsert)
      (SkipLeftInternal right NoTransitions (childInsertCannotBeRoot right rightInsert)
        (SkipRightInternal (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
          (childInsertCannotBeRoot (movedRight diamond) (trans (movedRightAction diamond) rightInsert))
          (SkipRightInternal (movedLeft diamond) NoTransitions
            (childInsertCannotBeRoot (movedLeft diamond) (trans (movedLeftAction diamond) leftInsert))
            SameExternalOrchestrationEnd)))

||| Consume the EXPLICIT produced safety+alignment once and construct the
||| actual O/O diamond, external evidence and FROZEN sealed suffix replay.
export
0 o19GeneratedInsertionReplayObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  (leftChild, rightChild, leftParent, rightParent : name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) -> (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent) ->
  (transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent) ->
  Not (rightChild = leftChild) ->
  (observed : (safety : OrchestrationSwapSafety name key world error value protocol nameEq keyEq left right **
    AlignedTransitions name key world error value nameEq keyEq (MoreTransitions (earlyRight safety) NoTransitions))) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq source earlier left right later diamond)
o19GeneratedInsertionReplayObserved nameEq keyEq protocol leftChild rightChild leftParent rightParent leftComponent rightComponent
  source earlier left right later decomposition premises leftInsert rightInsert distinct (safety ** earlyAligned) =
    ((orchestrationOrchestrationDiamondSpike nameEq keyEq protocol left right
        (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))
        (PaperInsertStep leftInsert) (PaperInsertStep rightInsert)
        (\same => distinct (trans (sym (cong actionOwner rightInsert))
          (trans (sym (o19TransitionActorOwner right))
            (trans (sym same) (trans (o19TransitionActorOwner left) (cong actionOwner leftInsert)))))) safety earlyAligned) **
     adjacentSwapSuffixSpike nameEq keyEq protocol source earlier left right later decomposition premises
       (orchestrationOrchestrationDiamondSpike nameEq keyEq protocol left right
        (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))
        (PaperInsertStep leftInsert) (PaperInsertStep rightInsert)
        (\same => distinct (trans (sym (cong actionOwner rightInsert))
          (trans (sym (o19TransitionActorOwner right))
            (trans (sym same) (trans (o19TransitionActorOwner left) (cong actionOwner leftInsert)))))) safety earlyAligned)
       (o19GeneratedInsertionPairExternal nameEq keyEq leftChild rightChild leftParent rightParent leftComponent rightComponent
         left right leftInsert rightInsert
         (orchestrationOrchestrationDiamondSpike nameEq keyEq protocol left right
        (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))
        (PaperInsertStep leftInsert) (PaperInsertStep rightInsert)
        (\same => distinct (trans (sym (cong actionOwner rightInsert))
          (trans (sym (o19TransitionActorOwner right))
            (trans (sym same) (trans (o19TransitionActorOwner left) (cong actionOwner leftInsert)))))) safety earlyAligned)))


||| Complete source-derived O/O node producer; no safety, early guard,
||| generation scan, local diamond or replay is accepted from the caller.
export
0 o19GeneratedInsertionReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  (leftChild, rightChild, leftParent, rightParent : name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) -> (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent) ->
  (transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent) ->
  Not (rightChild = leftChild) ->
  ((licensor : name) -> (ChildOf leftParent = ChildOf licensor) -> Not (rightChild = licensor)) ->
  ((licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (leftChild = licensor)) ->
  (transitionTag right = OInsertTag) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq source earlier left right later diamond)
o19GeneratedInsertionReplay nameEq keyEq protocol leftChild rightChild leftParent rightParent leftComponent rightComponent
  source earlier left right later decomposition premises leftInsert rightInsert distinct leftLicense rightLicense rightTag =
    o19GeneratedInsertionReplayObserved nameEq keyEq protocol leftChild rightChild leftParent rightParent leftComponent rightComponent
      source earlier left right later decomposition premises leftInsert rightInsert distinct
      (o19InsertionPairSafetyObserved nameEq keyEq protocol leftChild rightChild (ChildOf leftParent) (ChildOf rightParent)
        leftComponent rightComponent source earlier left right later decomposition premises leftInsert rightInsert distinct
        leftLicense rightLicense
        (o19InsertionPairEarly nameEq keyEq protocol leftChild rightChild (ChildOf leftParent) (ChildOf rightParent)
          leftComponent rightComponent source earlier left right later decomposition premises leftInsert rightInsert distinct
          rightLicense rightTag))


||| O/O observed row successor builds cursor, full bundle, original
||| uniqueness, same-chain derivation and exact count simultaneously.
export
0 o19InsertionInsertionStepObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) ->
  (crossings : Nat) ->
  (previous : O19OrchestrationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (leftOrchestration : PaperOrchestrationStep left) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left (orchestrationRowRight previous) **
    AdjacentSwapResult name key world error value protocol nameEq keyEq
      (cursorTrace (orchestrationRowCursor previous)) earlier left (orchestrationRowRight previous) (orchestrationRowRest previous) diamond) ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19InsertionInsertionStepObserved {name} {key} {world} {error} {value}
  nameEq keyEq protocol source earlier left sourceRight crossings previous
  leftOrchestration (diamond ** result) =
    MkO19OrchestrationRow
      (MkO19ReachedCursor (replayedFinal result) (swappedTrace result) (swappedPremises result)
        (uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
          (FiniteAdjacentSwapStep (cursorTrace (orchestrationRowCursor previous)) earlier left
          (orchestrationRowRight previous) (orchestrationRowRest previous)
          (AdjacentOrchestrationOrchestration left (orchestrationRowRight previous) leftOrchestration (orchestrationRowClass previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone) (cursorUnique (orchestrationRowCursor previous)))
        (o19AppendFinite (cursorDerivation (orchestrationRowCursor previous)) (FiniteAdjacentSwapStep (cursorTrace (orchestrationRowCursor previous)) earlier left
          (orchestrationRowRight previous) (orchestrationRowRest previous)
          (AdjacentOrchestrationOrchestration left (orchestrationRowRight previous) leftOrchestration (orchestrationRowClass previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone)))
      (swappedMiddle diamond) (movedRight diamond)
      (MoreTransitions (movedLeft diamond) (replayedSuffix result))
      (sym (swappedDecomposition result))
      (trans (movedRightAction diamond) (orchestrationRowAction previous))
      (trans (movedRightTag diamond) (orchestrationRowTag previous))
      (trans (o19TransitionActorOwner (movedRight diamond))
        (trans (cong actionOwner (trans (movedRightAction diamond) (orchestrationRowAction previous)))
          (sym (o19TransitionActorOwner sourceRight))))
      (movedRightOrchestrationBranch diamond (orchestrationRowClass previous))
      (trans (o19AppendFiniteCount (cursorDerivation (orchestrationRowCursor previous)) (FiniteAdjacentSwapStep (cursorTrace (orchestrationRowCursor previous)) earlier left
          (orchestrationRowRight previous) (orchestrationRowRest previous)
          (AdjacentOrchestrationOrchestration left (orchestrationRowRight previous) leftOrchestration (orchestrationRowClass previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone))
        (trans (cong (\count => count + 1) (orchestrationRowNodeCount previous))
          (plusCommutative crossings 1)))



||| Consume one explicit generated-insertion SOURCE class, then produce the
||| actual next O/O crossing. All executable/safety/replay fields are derived.
export
0 o19GeneratedInsertionRowStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  (rightChild, leftParent, rightParent : name) -> (rightComponent : Component key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) -> (crossings : Nat) ->
  (previous : O19OrchestrationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (transitionAction sourceRight = OInsert rightChild (ChildOf rightParent) rightComponent) ->
  (transitionTag sourceRight = OInsertTag) ->
  (observed : (leftChild : name ** (leftComponent : Component key value world error **
    ((transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent),
     Not (rightChild = leftChild),
     ((licensor : name) -> (ChildOf leftParent = ChildOf licensor) -> Not (rightChild = licensor)),
     ((licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (leftChild = licensor)))))) ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19GeneratedInsertionRowStep nameEq keyEq protocol rightChild leftParent rightParent rightComponent
  source earlier left sourceRight crossings previous rightInsert rightTag
  (leftChild ** (leftComponent ** (leftInsert, distinct, leftLicense, rightLicense))) =
    o19InsertionInsertionStepObserved nameEq keyEq protocol source earlier left sourceRight crossings previous
      (PaperInsertStep leftInsert)
      (o19GeneratedInsertionReplay nameEq keyEq protocol leftChild rightChild leftParent rightParent leftComponent rightComponent
        (cursorTrace (orchestrationRowCursor previous)) earlier left (orchestrationRowRight previous) (orchestrationRowRest previous)
        (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions)
          (MoreTransitions (orchestrationRowRight previous) (orchestrationRowRest previous)))) (orchestrationRowDecomposition previous))
        (cursorBundle (orchestrationRowCursor previous)) leftInsert
        (trans (orchestrationRowAction previous) rightInsert) distinct leftLicense rightLicense
        (trans (orchestrationRowTag previous) rightTag))

||| Arbitrary-length generated O/O row with SAME-source licensing classes.
||| Every cut guard, actual diamond, sealed replay, reached bundle, original
||| uniqueness, complete finite derivation and exact count are constructed.
||| Mixed activation/insertion spines and Cartesian column iteration are next.
export
0 o19BubbleGeneratedInsertionRow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  (rightChild, leftParent, rightParent : name) -> (rightComponent : Component key value world error) ->
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (spine : Transitions before rightBefore) -> (right : Transition rightBefore rightAfter) ->
  (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (appendTransitions spine (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent) ->
  (transitionTag right = OInsertTag) ->
  (0 classes : {first, last : SystemState name key value world error} ->
    (step : Transition first last) -> OccursIn step spine ->
    (leftChild : name ** (leftComponent : Component key value world error **
      ((transitionAction step = OInsert leftChild (ChildOf leftParent) leftComponent),
       Not (rightChild = leftChild),
       ((licensor : name) -> (ChildOf leftParent = ChildOf licensor) -> Not (rightChild = licensor)),
       ((licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (leftChild = licensor)))))) ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier right (transitionCount spine)
o19BubbleGeneratedInsertionRow nameEq keyEq protocol rightChild leftParent rightParent rightComponent source earlier
  NoTransitions right later decomposition premises unique rightInsert rightTag classes =
    o19OrchestrationRowZero nameEq keyEq protocol source earlier right later decomposition premises unique (PaperInsertStep rightInsert)
o19BubbleGeneratedInsertionRow nameEq keyEq protocol rightChild leftParent rightParent rightComponent source earlier
  (MoreTransitions left rest) right later decomposition premises unique rightInsert rightTag classes =
    o19GeneratedInsertionRowStep nameEq keyEq protocol rightChild leftParent rightParent rightComponent source earlier left right
      (transitionCount rest)
      (o19BubbleGeneratedInsertionRow nameEq keyEq protocol rightChild leftParent rightParent rightComponent source
        (appendTransitions earlier (MoreTransitions left NoTransitions)) rest right later
        (trans (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions)
          (appendTransitions rest (MoreTransitions right later))) decomposition)
        premises unique rightInsert rightTag (\step, occurs => classes step (OccursLater occurs)))
      rightInsert rightTag (classes left OccursHere)


||| First mixed-row dependency: classify the ACTUAL left source node and
||| dispatch A/O or O/O without accepting a guard/diamond/replay oracle.
export
0 o19MixedInsertionRowStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  (rightChild, leftParent, rightParent : name) -> (rightComponent : Component key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) -> (crossings : Nat) ->
  (previous : O19OrchestrationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (transitionAction sourceRight = OInsert rightChild (ChildOf rightParent) rightComponent) ->
  (transitionTag sourceRight = OInsertTag) ->
  (observed : Either
    (PaperActivationStep left, Not (rightChild = transitionActor left),
      ((licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (transitionActor left = licensor)))
    (leftChild : name ** (leftComponent : Component key value world error **
    ((transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent),
     Not (rightChild = leftChild),
     ((licensor : name) -> (ChildOf leftParent = ChildOf licensor) -> Not (rightChild = licensor)),
     ((licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (leftChild = licensor)))))) ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19MixedInsertionRowStep nameEq keyEq protocol rightChild leftParent rightParent rightComponent
  source earlier left sourceRight crossings previous rightInsert rightTag
  (Left (activation, distinct, licensing)) =
    o19ActivationInsertionStep nameEq keyEq protocol rightChild (ChildOf rightParent) rightComponent
      source earlier left sourceRight crossings previous activation rightInsert distinct licensing
o19MixedInsertionRowStep nameEq keyEq protocol rightChild leftParent rightParent rightComponent
  source earlier left sourceRight crossings previous rightInsert rightTag (Right generated) =
    o19GeneratedInsertionRowStep nameEq keyEq protocol rightChild leftParent rightParent rightComponent
      source earlier left sourceRight crossings previous rightInsert rightTag generated
