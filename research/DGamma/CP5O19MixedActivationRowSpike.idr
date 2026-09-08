module DGamma.CP5O19MixedActivationRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O19AdvanceObservationSpike
import DGamma.CP5O19ActivationRowSpike
import Data.Nat
import DGamma.CP5O19BodyMetadataSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Dispatch the ACTUAL right activation constructor to the sanctioned
||| reached Begin/Iter/Finish guards, preserving its own checked equation.
export
0 o19ReplayedActivationChecked :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq source) ->
  (earlier : Transitions initial first) -> (later : Transitions last (cursorFinal cursor)) ->
  (leftAction, rightAction : Action name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle = Just (rightTag, last)) ->
  (appendTransitions earlier
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq rightAction rightTag rightChecked) later)) = cursorTrace cursor) ->
  (actionOwner leftAction = actorLeft swap) ->
  (actionOwner rightAction = actorRight swap) ->
  PaperActivationStep (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked) ->
  PaperActivationStep (Fired {before = middle} {afterState = last} nameEq keyEq rightAction rightTag rightChecked) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first rightAction rightTag
o19ReplayedActivationChecked nameEq keyEq protocol swap source blocks premises safety unique cursor earlier later
  leftAction rightAction leftTag rightTag leftChecked rightChecked decomposition leftOwner rightOwner leftActivation rightActivation =
    case rightActivation of
      PaperBeginStep sameAction sameTag => case sameAction of
        Refl => case sameTag of
          Refl => case rightOwner of
            Refl => o19SanctionedReplayedBegin nameEq keyEq protocol swap source blocks premises safety unique cursor earlier later
              leftAction leftTag leftChecked rightChecked decomposition leftOwner leftActivation
      PaperIterStep sameAction sameTag => case sameAction of
        Refl => case sameTag of
          Refl => case rightOwner of
            Refl => o19SanctionedReplayedAdvance nameEq keyEq protocol swap source blocks premises safety unique cursor earlier later
              leftAction leftTag LIterTag leftChecked rightChecked decomposition leftOwner (Left Refl) leftActivation
      PaperFinishStep sameAction sameTag => case sameAction of
        Refl => case sameTag of
          Refl => case rightOwner of
            Refl => o19SanctionedReplayedAdvance nameEq keyEq protocol swap source blocks premises safety unique cursor earlier later
              leftAction leftTag LFinishTag leftChecked rightChecked decomposition leftOwner (Right Refl) leftActivation

||| Eliminate one EXPLICIT actual pair alignment; all stored dictionaries,
||| labels and check equations now agree with the sanctioned guard producer.
export
0 o19ReplayedActivationAligned :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, first, middle, last, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq source) ->
  (earlier : Transitions initial first) -> (later : Transitions last (cursorFinal cursor)) ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = cursorTrace cursor) ->
  (transitionActor left = actorLeft swap) -> (transitionActor right = actorRight swap) ->
  PaperActivationStep left -> PaperActivationStep right ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first (transitionAction right) (transitionTag right)
o19ReplayedActivationAligned nameEq keyEq protocol swap source blocks premises safety unique cursor earlier later
  _ _ decomposition leftOwner rightOwner leftActivation rightActivation
  (AlignedStep leftAction leftTag leftChecked _ (AlignedStep rightAction rightTag rightChecked _ AlignedEnd)) =
    o19ReplayedActivationChecked nameEq keyEq protocol swap source blocks premises safety unique cursor earlier later
      leftAction rightAction leftTag rightTag leftChecked rightChecked decomposition
      (trans (sym (o19TransitionActorOwner (Fired nameEq keyEq leftAction leftTag leftChecked))) leftOwner)
      (trans (sym (o19TransitionActorOwner (Fired nameEq keyEq rightAction rightTag rightChecked))) rightOwner)
      leftActivation rightActivation

||| Backwards insertion/Begin guard from the EXPLICIT actual insertion plan
||| and the actual later Begin observation. A fresh inactive insertion changes
||| neither a distinct owner's clean fiber nor any successfully resolved view.
export
0 o19BeginBeforeInsertPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor, child : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (middle, last : SystemState name key value world error) -> (tag : RuleTag) ->
  Not (actor = child) ->
  ForeignInsertPlanView name key world error value nameEq keyEq child parent component ambient fibers tag middle ->
  (opening : O20BeginObservation name key world error value nameEq keyEq actor middle last) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkSystemState ambient fibers) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (MkSystemState ambient fibers) (LBegin actor) LBeginTag
o19BeginBeforeInsertPlan {name} {key} {world} {error} {value} nameEq keyEq actor child parent component ambient fibers
  _ last _ distinct (MkForeignInsertPlanView absent guards) opening wellFormed =
    o19BeginAtResolvedState nameEq keyEq actor (MkSystemState ambient fibers)
      (beginObservedComponent opening) (beginObservedParent opening) (beginObservedTable opening) (beginObservedView opening)
      (trans (sym (lookupInsertOther @{nameEq} actor child distinct (freshFiber component parent) fibers absent))
        (beginObservedFound opening))
      (trans (sym (resolveViewInactiveInsert {name} {key} {world} {error} {value} nameEq keyEq
        (dependencies (componentDependencies (beginObservedComponent opening))) child component parent fibers absent))
        (beginObservedResolved opening)) wellFormed

||| TOTAL checked O/A guard dispatcher: Begin uses the actual insertion plan
||| and later opening; Iter/Finish use actual pair independence/domain proof.
||| No early edge, target/resolver observation or callback is requested.
export
0 o19InsertionActivationChecked :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (first, middle, last : SystemState name key value world error) ->
  (rightAction : Action name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert child parent component) first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction middle = Just (rightTag, last)) ->
  Not (child = actionOwner rightAction) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq (OInsert child parent component) leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = last} nameEq keyEq rightAction rightTag rightChecked) NoTransitions)) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} first = True) ->
  PaperActivationStep (Fired {before = middle} {afterState = last} nameEq keyEq rightAction rightTag rightChecked) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first rightAction rightTag
o19InsertionActivationChecked nameEq keyEq child parent component (MkSystemState ambient fibers) middle last rightAction
  leftTag rightTag leftChecked rightChecked distinct independent wellFormed activation = case activation of
    PaperBeginStep {actor} sameAction sameTag => case sameAction of
      Refl => case sameTag of
        Refl => o19BeginBeforeInsertPlan nameEq keyEq actor child parent component ambient fibers middle last leftTag
          (\same => distinct (sym same))
          (foreignInsertPlanView nameEq keyEq child parent component ambient fibers leftTag middle
            (checkedActionProjects nameEq keyEq (OInsert child parent component) (MkSystemState ambient fibers) middle leftTag leftChecked))
          (o20ObserveActualBegin nameEq keyEq actor middle last (MkBeginStep rightChecked)) wellFormed
    PaperIterStep {actor} sameAction sameTag => case sameAction of
      Refl => o19AdvanceBeforeCheckedInsertion nameEq keyEq actor child parent component (MkSystemState ambient fibers) middle last
        leftTag rightTag leftChecked rightChecked (Left sameTag) distinct independent wellFormed
    PaperFinishStep {actor} sameAction sameTag => case sameAction of
      Refl => o19AdvanceBeforeCheckedInsertion nameEq keyEq actor child parent component (MkSystemState ambient fibers) middle last
        leftTag rightTag leftChecked rightChecked (Right sameTag) distinct independent wellFormed

||| Actual aligned O/A pair adapter. Only label evidence and SAME-pair
||| well-formedness/independence are consumed; the early edge is constructed.
export
0 o19InsertionActivationAligned :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  (transitionAction left = OInsert child parent component) ->
  Not (transitionActor right = child) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} first = True) ->
  TraceIndependent name key world error value keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  PaperActivationStep right ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions left (MoreTransitions right NoTransitions)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first (transitionAction right) (transitionTag right)
o19InsertionActivationAligned {first} {middle} {last} nameEq keyEq child parent component _ _ inserted distinct wellFormed independent activation
  (AlignedStep leftAction leftTag leftChecked _ (AlignedStep rightAction rightTag rightChecked _ AlignedEnd)) = case inserted of
    Refl => o19InsertionActivationChecked nameEq keyEq child parent component first middle last rightAction leftTag rightTag
      leftChecked rightChecked
      (\same => distinct (trans (o19TransitionActorOwner (Fired nameEq keyEq rightAction rightTag rightChecked)) (sym same)))
      independent wellFormed activation

||| One MIXED right-activation row step. The same explicit previous row
||| supplies its actual next pair, bundle, uniqueness and derivation. Combine
||| its origins with the original sanctioned source ONLY for metadata; build
||| the next local crossing/replay/count through the real row producers.
export
0 o19MixedActivationRowStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (source : Transitions initial sourceFinal) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original source ->
  (earlier : Transitions initial before) -> (left : Transition before middle) ->
  (sourceRight : Transition rightBefore rightAfter) -> (crossings : Nat) ->
  (previous : O19ActivationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (transitionActor sourceRight = actorRight swap) ->
  (observed : Either (PaperActivationStep left, transitionActor left = actorLeft swap)
    (child : name ** (component : Component key value world error **
      ((transitionAction left = OInsert child (ChildOf (actorLeft swap)) component), Not (actorRight swap = child))))) ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19MixedActivationRowStep nameEq keyEq protocol swap original blocks premises safety unique source prior earlier left sourceRight crossings previous rightOwner (Left (activation, leftOwner)) =
    o19ActivationRowStep nameEq keyEq protocol source earlier left sourceRight crossings previous activation
      (\same => actorDistinct swap (trans (sym leftOwner) (trans (sym same) rightOwner)))
      (o19EarlyLabels nameEq keyEq (transitionAction (rowRight previous)) (transitionAction sourceRight)
        (transitionTag (rowRight previous)) (transitionTag sourceRight) (sym (rowAction previous)) (sym (rowTag previous))
        (o19ReplayedActivationAligned nameEq keyEq protocol swap original blocks premises safety unique (MkO19ReachedCursor (cursorFinal (rowCursor previous)) (cursorTrace (rowCursor previous)) (cursorBundle (rowCursor previous)) (cursorUnique (rowCursor previous)) (o19AppendFinite prior (cursorDerivation (rowCursor previous))))
          earlier (rowRest previous) left (rowRight previous) (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions) (MoreTransitions (rowRight previous) (rowRest previous)))) (rowDecomposition previous))
          leftOwner (trans (rowActor previous) rightOwner) activation (rowActivation previous) (fst (o19SourcePairFacts nameEq keyEq protocol (cursorTrace (rowCursor previous)) earlier left (rowRight previous) (rowRest previous) (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions) (MoreTransitions (rowRight previous) (rowRest previous)))) (rowDecomposition previous)) (cursorBundle (rowCursor previous))))))
o19MixedActivationRowStep nameEq keyEq protocol swap original blocks premises safety unique source prior earlier left sourceRight crossings previous rightOwner (Right (child ** (component ** (inserted, childSafe)))) =
    o19InsertionRowStep nameEq keyEq protocol child (ChildOf (actorLeft swap)) component source earlier left sourceRight crossings previous inserted
      (\same => childSafe (trans (sym rightOwner) same))
      (\licensor, sameParent, sameActor => case sameParent of Refl => actorDistinct swap (trans (sym sameActor) rightOwner))
      (o19EarlyLabels nameEq keyEq (transitionAction (rowRight previous)) (transitionAction sourceRight)
        (transitionTag (rowRight previous)) (transitionTag sourceRight) (sym (rowAction previous)) (sym (rowTag previous))
        (o19InsertionActivationAligned nameEq keyEq child (ChildOf (actorLeft swap)) component left (rowRight previous) inserted
          (\same => childSafe (trans (sym (trans (rowActor previous) rightOwner)) same))
          (fst (snd (o19SourcePairFacts nameEq keyEq protocol (cursorTrace (rowCursor previous)) earlier left (rowRight previous) (rowRest previous) (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions) (MoreTransitions (rowRight previous) (rowRest previous)))) (rowDecomposition previous)) (cursorBundle (rowCursor previous))))) (snd (snd (o19SourcePairFacts nameEq keyEq protocol (cursorTrace (rowCursor previous)) earlier left (rowRight previous) (rowRest previous) (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions) (MoreTransitions (rowRight previous) (rowRest previous)))) (rowDecomposition previous)) (cursorBundle (rowCursor previous))))) (rowActivation previous) (fst (o19SourcePairFacts nameEq keyEq protocol (cursorTrace (rowCursor previous)) earlier left (rowRight previous) (rowRest previous) (trans (sym (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions) (MoreTransitions (rowRight previous) (rowRest previous)))) (rowDecomposition previous)) (cursorBundle (rowCursor previous))))))

||| Arbitrary MIXED right-activation row, not restricted to Begin. All A/A
||| and O/A cut guards, actual diamonds, sealed suffix replays, current full
||| bundles/uniqueness and exact row node count are built simultaneously.
||| Source classes carry ONLY actual action/owner labels and child separation.
export
0 o19BubbleMixedActivationRow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (source : Transitions initial sourceFinal) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original source ->
  (earlier : Transitions initial before) -> (spine : Transitions before rightBefore) ->
  (right : Transition rightBefore rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (appendTransitions spine (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  PaperActivationStep right -> (transitionActor right = actorRight swap) ->
  (0 classes : {first, last : SystemState name key value world error} ->
    (step : Transition first last) -> OccursIn step spine ->
    Either (PaperActivationStep step, transitionActor step = actorLeft swap)
      (child : name ** (component : Component key value world error **
        ((transitionAction step = OInsert child (ChildOf (actorLeft swap)) component), Not (actorRight swap = child))))) ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier right (transitionCount spine)
o19BubbleMixedActivationRow nameEq keyEq protocol swap original blocks premises safety unique source prior earlier
  NoTransitions right later decomposition currentPremises currentUnique activation rightOwner classes =
    o19ActivationRowZero nameEq keyEq protocol source earlier right later decomposition currentPremises currentUnique activation
o19BubbleMixedActivationRow nameEq keyEq protocol swap original blocks premises safety unique source prior earlier
  (MoreTransitions left rest) right later decomposition currentPremises currentUnique activation rightOwner classes =
    o19MixedActivationRowStep nameEq keyEq protocol swap original blocks premises safety unique source prior earlier left right
      (transitionCount rest)
      (o19BubbleMixedActivationRow nameEq keyEq protocol swap original blocks premises safety unique source prior
        (appendTransitions earlier (MoreTransitions left NoTransitions)) rest right later
        (trans (appendTransitionsAssociative earlier (MoreTransitions left NoTransitions)
          (appendTransitions rest (MoreTransitions right later))) decomposition)
        currentPremises currentUnique activation rightOwner (\step, occurs => classes step (OccursLater occurs)))
      rightOwner (classes left OccursHere)
