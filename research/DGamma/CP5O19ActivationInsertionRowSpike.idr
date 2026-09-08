module DGamma.CP5O19ActivationInsertionRowSpike

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
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Same simultaneous row boundary for a moved orchestration node.
public export
record O19OrchestrationRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal)
  (earlier : Transitions initial before)
  (sourceRight : Transition rightBefore rightAfter)
  (crossings : Nat) where
  constructor MkO19OrchestrationRow
  orchestrationRowCursor : O19ReachedCursor name key world error value protocol nameEq keyEq source
  orchestrationRowMiddle : SystemState name key value world error
  orchestrationRowRight : Transition before orchestrationRowMiddle
  orchestrationRowRest : Transitions orchestrationRowMiddle (cursorFinal orchestrationRowCursor)
  0 orchestrationRowDecomposition : appendTransitions earlier (MoreTransitions orchestrationRowRight orchestrationRowRest) = cursorTrace orchestrationRowCursor
  0 orchestrationRowAction : transitionAction orchestrationRowRight = transitionAction sourceRight
  0 orchestrationRowTag : transitionTag orchestrationRowRight = transitionTag sourceRight
  0 orchestrationRowActor : transitionActor orchestrationRowRight = transitionActor sourceRight
  0 orchestrationRowClass : PaperOrchestrationStep orchestrationRowRight
  0 orchestrationRowNodeCount : finiteAdjacentSwapNodeCount (cursorDerivation orchestrationRowCursor) = crossings


||| Constructor-owned zero row; its count observes only finite Done.
export
0 o19OrchestrationRowZero :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (right : Transition before rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (MoreTransitions right later) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  PaperOrchestrationStep right ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier right 0
o19OrchestrationRowZero {sourceFinal} {rightAfter} nameEq keyEq protocol source earlier
  right later decomposition premises unique activation =
    MkO19OrchestrationRow
      (MkO19ReachedCursor sourceFinal source premises unique FiniteAdjacentSwapDone)
      rightAfter right later decomposition Refl Refl Refl activation Refl


||| A/O pair external evidence: actual moved labels authenticate both root
||| matching and generated internality. The activation remains internal.
export
0 o19ActivationInsertExternal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  PaperActivationStep left -> (transitionAction right = OInsert child parent component) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions))
o19ActivationInsertExternal nameEq keyEq child Root component left right activation inserted diamond =
  SkipLeftInternal left (MoreTransitions right NoTransitions) (o19ActivationInternal nameEq left activation)
    (MatchExternalInput (OInsert child Root component) right NoTransitions
      (RootInsertStep inserted) (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
      (RootInsertStep (trans (movedRightAction diamond) inserted))
      inserted (trans (movedRightAction diamond) inserted)
      (SkipRightInternal (movedLeft diamond) NoTransitions
        (o19ActivationInternal nameEq (movedLeft diamond) (movedLeftActivationBranch diamond activation))
        SameExternalOrchestrationEnd))
o19ActivationInsertExternal nameEq keyEq child (ChildOf parent) component left right activation inserted diamond =
  SkipLeftInternal left (MoreTransitions right NoTransitions) (o19ActivationInternal nameEq left activation)
    (SkipLeftInternal right NoTransitions (childInsertCannotBeRoot right inserted)
      (SkipRightInternal (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
        (childInsertCannotBeRoot (movedRight diamond) (trans (movedRightAction diamond) inserted))
        (SkipRightInternal (movedLeft diamond) NoTransitions
          (o19ActivationInternal nameEq (movedLeft diamond) (movedLeftActivationBranch diamond activation))
          SameExternalOrchestrationEnd)))


||| Actual A/O diamond AND frozen suffix replay. Its early insertion is
||| derived by the A/O producer; no intermediate checked guard is assumed.
export
0 o19ActivationInsertReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last finalState) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  PaperActivationStep left -> (transitionAction right = OInsert child parent component) ->
  Not (child = transitionActor left) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (transitionActor left = licensor)) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
   AdjacentSwapResult name key world error value protocol nameEq keyEq source earlier left right later diamond)
o19ActivationInsertReplay nameEq keyEq protocol child parent component source earlier left right later
  decomposition premises activation inserted childSafe parentSafe =
    ((activationOrchestrationDiamondSpike nameEq keyEq left right
        (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))
        activation (PaperInsertStep inserted)
        (\same => childSafe (trans (sym (cong actionOwner inserted))
          (trans (sym (o19TransitionActorOwner right)) (sym same))))
        (\otherChild, licensor, otherComponent, same => parentSafe licensor
          (o19InsertParentInjective child otherChild parent (ChildOf licensor) component otherComponent
            (trans (sym inserted) same)))
        (Builtin.fst (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))
        (Builtin.snd (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))) **
     adjacentSwapSuffixSpike nameEq keyEq protocol source earlier left right later decomposition premises
       (activationOrchestrationDiamondSpike nameEq keyEq left right
        (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))
        activation (PaperInsertStep inserted)
        (\same => childSafe (trans (sym (cong actionOwner inserted))
          (trans (sym (o19TransitionActorOwner right)) (sym same))))
        (\otherChild, licensor, otherComponent, same => parentSafe licensor
          (o19InsertParentInjective child otherChild parent (ChildOf licensor) component otherComponent
            (trans (sym inserted) same)))
        (Builtin.fst (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))
        (Builtin.snd (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))))
       (o19ActivationInsertExternal nameEq keyEq child parent component left right activation inserted
         (activationOrchestrationDiamondSpike nameEq keyEq left right
        (Builtin.fst (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))
        activation (PaperInsertStep inserted)
        (\same => childSafe (trans (sym (cong actionOwner inserted))
          (trans (sym (o19TransitionActorOwner right)) (sym same))))
        (\otherChild, licensor, otherComponent, same => parentSafe licensor
          (o19InsertParentInjective child otherChild parent (ChildOf licensor) component otherComponent
            (trans (sym inserted) same)))
        (Builtin.fst (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises)))
        (Builtin.snd (Builtin.snd (o19SourcePairFacts nameEq keyEq protocol source earlier left right later decomposition premises))))))

||| Observe one actual A/O result and extend all row evidence simultaneously.
export
0 o19ActivationInsertionStepObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) ->
  (crossings : Nat) ->
  (previous : O19OrchestrationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (leftActivation : PaperActivationStep left) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left (orchestrationRowRight previous) **
    AdjacentSwapResult name key world error value protocol nameEq keyEq
      (cursorTrace (orchestrationRowCursor previous)) earlier left (orchestrationRowRight previous) (orchestrationRowRest previous) diamond) ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19ActivationInsertionStepObserved {name} {key} {world} {error} {value}
  nameEq keyEq protocol source earlier left sourceRight crossings previous
  leftActivation (diamond ** result) =
    MkO19OrchestrationRow
      (MkO19ReachedCursor (replayedFinal result) (swappedTrace result) (swappedPremises result)
        (uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
          (FiniteAdjacentSwapStep (cursorTrace (orchestrationRowCursor previous)) earlier left
          (orchestrationRowRight previous) (orchestrationRowRest previous)
          (AdjacentActivationOrchestration left (orchestrationRowRight previous) leftActivation (orchestrationRowClass previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone) (cursorUnique (orchestrationRowCursor previous)))
        (o19AppendFinite (cursorDerivation (orchestrationRowCursor previous)) (FiniteAdjacentSwapStep (cursorTrace (orchestrationRowCursor previous)) earlier left
          (orchestrationRowRight previous) (orchestrationRowRest previous)
          (AdjacentActivationOrchestration left (orchestrationRowRight previous) leftActivation (orchestrationRowClass previous))
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
          (AdjacentActivationOrchestration left (orchestrationRowRight previous) leftActivation (orchestrationRowClass previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone))
        (trans (cong (\count => count + 1) (orchestrationRowNodeCount previous))
          (plusCommutative crossings 1)))



||| The next A/O crossing consumes only the actual previous row and classes.
export
0 o19ActivationInsertionStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) ->
  (crossings : Nat) ->
  (previous : O19OrchestrationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  PaperActivationStep left -> (transitionAction sourceRight = OInsert child parent component) ->
  Not (child = transitionActor left) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (transitionActor left = licensor)) ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19ActivationInsertionStep nameEq keyEq protocol child parent component source earlier left sourceRight crossings
  previous activation inserted childSafe parentSafe =
    o19ActivationInsertionStepObserved nameEq keyEq protocol source earlier left sourceRight crossings
      previous activation
      (o19ActivationInsertReplay nameEq keyEq protocol child parent component
        (cursorTrace (orchestrationRowCursor previous)) earlier left
        (orchestrationRowRight previous) (orchestrationRowRest previous)
        (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions)
          (MoreTransitions (orchestrationRowRight previous) (orchestrationRowRest previous))))
          (orchestrationRowDecomposition previous))
        (cursorBundle (orchestrationRowCursor previous)) activation
        (trans (orchestrationRowAction previous) inserted) childSafe parentSafe)

||| Arbitrary-length A/O INSERT row. The A/O diamond derives early execution
||| at every crossing, so no per-cut applicability oracle is required. Reached
||| bundle, original uniqueness, derivation and count are built simultaneously.
export
0 o19BubbleActivationInsertionRow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (spine : Transitions before rightBefore) -> (right : Transition rightBefore rightAfter) ->
  (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (appendTransitions spine (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (transitionAction right = OInsert child parent component) ->
  (0 classes : {first, last : SystemState name key value world error} ->
    (step : Transition first last) -> OccursIn step spine ->
    (PaperActivationStep step, Not (child = transitionActor step))) ->
  (0 licensing : {first, last : SystemState name key value world error} ->
    (step : Transition first last) -> OccursIn step spine ->
    (licensor : name) -> (parent = ChildOf licensor) -> Not (transitionActor step = licensor)) ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier right (transitionCount spine)
o19BubbleActivationInsertionRow nameEq keyEq protocol child parent component source earlier
  NoTransitions right later decomposition premises unique inserted classes licensing =
    o19OrchestrationRowZero nameEq keyEq protocol source earlier right later decomposition premises unique
      (PaperInsertStep inserted)
o19BubbleActivationInsertionRow nameEq keyEq protocol child parent component source earlier
  (MoreTransitions left rest) right later decomposition premises unique inserted classes licensing =
    o19ActivationInsertionStep nameEq keyEq protocol child parent component source earlier left right
      (transitionCount rest)
      (o19BubbleActivationInsertionRow nameEq keyEq protocol child parent component source
        (appendTransitions earlier (MoreTransitions left NoTransitions)) rest right later
        (trans (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions)
          (appendTransitions rest (MoreTransitions right later))) decomposition)
        premises unique inserted (\step, occurs => classes step (OccursLater occurs))
        (\step, occurs => licensing step (OccursLater occurs)))
      (Builtin.fst (classes left OccursHere)) inserted (Builtin.snd (classes left OccursHere))
      (licensing left OccursHere)
