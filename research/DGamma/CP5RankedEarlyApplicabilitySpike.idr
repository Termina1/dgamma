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
