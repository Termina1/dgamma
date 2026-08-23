module DGamma.R14O4IndependentDictionaryNegative

import DGamma.Calculus
import DGamma.Metatheory
import Decidable.Equality

%default total

||| Bare mixed transitions built by independent executable dictionaries cannot
||| satisfy revision 14's exact source-pair alignment premise.
0 independentMixedPairCannotAlign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (alternateNameEq : DecEq name) -> (alternateKeyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (leftAction, rightAction : Action name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction
    @{alternateNameEq} @{alternateKeyEq} leftAction first =
      Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction
    @{alternateNameEq} @{alternateKeyEq} rightAction middle =
      Just (rightTag, finalState)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = middle}
        alternateNameEq alternateKeyEq leftAction leftTag leftChecked)
      (MoreTransitions
        (Fired {before = middle} {afterState = finalState}
          alternateNameEq alternateKeyEq rightAction rightTag rightChecked)
        NoTransitions))
independentMixedPairCannotAlign nameEq keyEq alternateNameEq alternateKeyEq
  leftAction rightAction leftTag rightTag leftChecked rightChecked =
    AlignedStep leftAction leftTag leftChecked
      (MoreTransitions
        (Fired alternateNameEq alternateKeyEq
          rightAction rightTag rightChecked)
        NoTransitions)
      (AlignedStep rightAction rightTag rightChecked NoTransitions AlignedEnd)
