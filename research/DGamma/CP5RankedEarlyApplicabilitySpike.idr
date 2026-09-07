module DGamma.CP5RankedEarlyApplicabilitySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5RankedTraceSelectionSpike
import Data.Maybe
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An actual checked early application with the EXACT original action/tag.
||| Its destination is produced by execution, never supplied by a caller.
public export
record CheckedEarlyApplication
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (before : SystemState name key value world error)
  (action : Action name key value world error) (tag : RuleTag) where
  constructor MkCheckedEarlyApplication
  earlyApplicationFinal : SystemState name key value world error
  0 earlyApplicationChecked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, earlyApplicationFinal)

||| Finite exact-tag check, not the existing test-only Boolean comparison.
public export
0 observedRuleTagSame : (actual, expected : RuleTag) -> Maybe (actual = expected)
observedRuleTagSame OInsertTag OInsertTag = Just Refl
observedRuleTagSame ORetireTag ORetireTag = Just Refl
observedRuleTagSame ORemoveTag ORemoveTag = Just Refl
observedRuleTagSame LBeginTag LBeginTag = Just Refl
observedRuleTagSame LIterTag LIterTag = Just Refl
observedRuleTagSame LFinishTag LFinishTag = Just Refl
observedRuleTagSame LDivertTag LDivertTag = Just Refl
observedRuleTagSame LRaiseTag LRaiseTag = Just Refl
observedRuleTagSame LLeaveTag LLeaveTag = Just Refl
observedRuleTagSame LUnloadTag LUnloadTag = Just Refl
observedRuleTagSame _ _ = Nothing

||| Authenticate an explicitly observed checked result. A different tag is
||| rejected even when the action itself happens to fire before the left node.
public export
0 checkedEarlyApplicationObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (before : SystemState name key value world error) ->
  (action : Action name key value world error) -> (expected : RuleTag) ->
  (observed : Maybe (RuleTag, SystemState name key value world error)) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = observed ->
  Maybe (CheckedEarlyApplication name key world error value nameEq keyEq before action expected)
checkedEarlyApplicationObserved name key world error value nameEq keyEq before action expected Nothing exact = Nothing
checkedEarlyApplicationObserved name key world error value nameEq keyEq before action expected (Just (actual, afterState)) exact =
  case observedRuleTagSame actual expected of
    Nothing => Nothing
    Just same => Just (MkCheckedEarlyApplication afterState
      (trans exact (cong (\tag => Just (tag, afterState)) same)))

||| Execute the SAME selected right action at the SAME selected before-cut.
||| Nothing is only a failed positive check, never completeness/canonicality.
public export
0 checkSelectedEarlyRight :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (observe : Action name key value world error -> Maybe Nat) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (choice : LocatedRankDescent name key world error value observe trace) ->
  Maybe (CheckedEarlyApplication name key world error value nameEq keyEq
    (traceDescentBefore choice) (transitionAction (traceDescentRight choice)) (transitionTag (traceDescentRight choice)))
checkSelectedEarlyRight name key world error value nameEq keyEq observe trace choice =
  checkedEarlyApplicationObserved name key world error value nameEq keyEq (traceDescentBefore choice)
    (transitionAction (traceDescentRight choice)) (transitionTag (traceDescentRight choice))
    (checkedApplyAction @{nameEq} @{keyEq} (transitionAction (traceDescentRight choice)) (traceDescentBefore choice)) Refl

||| Integrate E with the EXACT existing worklist observer and orientation
||| inspector, then execute the chosen right node at its authentic early cut.
||| Only positive results are certified. A failed first candidate is not a
||| search over later applicable pairs and is not an O17 progress theorem.
export
0 selectCanonicalObservedEarlyPair :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (fixedOrder : List name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  Maybe (choice : LocatedRankDescent name key world error value
    (canonicalWorkActionRank name key world error value nameEq fixedOrder) trace **
    (AdjacentSwapOrientationEvidence (traceDescentLeft choice) (traceDescentRight choice),
     CheckedEarlyApplication name key world error value nameEq keyEq (traceDescentBefore choice)
       (transitionAction (traceDescentRight choice)) (transitionTag (traceDescentRight choice))))
selectCanonicalObservedEarlyPair name key world error value nameEq keyEq fixedOrder trace =
  case findActualRankDescent name key world error value
    (canonicalWorkActionRank name key world error value nameEq fixedOrder) trace of
    Nothing => Nothing
    Just choice => case canonicalWorkInspectOrientation name key world error value (traceDescentLeft choice) (traceDescentRight choice) of
      Nothing => Nothing
      Just orientation => case checkSelectedEarlyRight name key world error value nameEq keyEq
        (canonicalWorkActionRank name key world error value nameEq fixedOrder) trace choice of
        Nothing => Nothing
        Just early => Just (choice ** (orientation, early))
