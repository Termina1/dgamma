module DGamma.R15O5IndependentDictionaryNegative

import DGamma.Calculus
import DGamma.Metatheory
import Decidable.Equality

%default total

||| An independently stored early orchestration cannot inhabit revision 15's
||| singleton alignment index under different outer executable dictionaries.
0 independentEarlyOrchestrationCannotAlign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (alternateNameEq : DecEq name) -> (alternateKeyEq : DecEq key) ->
  {first, earlyFinal : SystemState name key value world error} ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{alternateNameEq} @{alternateKeyEq}
    action first = Just (tag, earlyFinal)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = earlyFinal}
        alternateNameEq alternateKeyEq action tag checked) NoTransitions)
independentEarlyOrchestrationCannotAlign nameEq keyEq alternateNameEq
  alternateKeyEq action tag checked =
    AlignedStep action tag checked NoTransitions AlignedEnd
