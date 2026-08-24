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
