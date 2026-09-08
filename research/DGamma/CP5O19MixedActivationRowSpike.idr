module DGamma.CP5O19MixedActivationRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19BodyMetadataSpike
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
