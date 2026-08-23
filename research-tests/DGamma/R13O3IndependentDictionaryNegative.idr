module DGamma.R13O3IndependentDictionaryNegative

import DGamma.Calculus
import DGamma.Metatheory
import Decidable.Equality

%default total

||| The revision-13 premise is intentionally unavailable when a caller merely
||| supplies another executable dictionary pair. Lawful decision polarity does
||| not make these interface records definitionally equal.
0 independentDictionariesCannotAlign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (alternateNameEq : DecEq name) -> (alternateKeyEq : DecEq key) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{alternateNameEq} @{alternateKeyEq}
    action before = Just (tag, afterState)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions
      (Fired {before} {afterState}
        alternateNameEq alternateKeyEq action tag checked)
      NoTransitions)
independentDictionariesCannotAlign nameEq keyEq alternateNameEq alternateKeyEq
  action tag checked =
    AlignedStep action tag checked NoTransitions AlignedEnd
