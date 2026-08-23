module DGamma.R14O4AlignedProducerPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Every genuine mixed adjacent source is selected from an exact replay bundle.
||| This producer is orientation-independent: it supplies A/O and O/A alike.
0 alignedMixedPairFromReplayBundle :
  (premises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq
    (MoreTransitions left (MoreTransitions right suffix))) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
alignedMixedPairFromReplayBundle premises with (replayAligned premises)
  alignedMixedPairFromReplayBundle premises |
      (AlignedStep leftAction leftTag leftChecked _
        (AlignedStep rightAction rightTag rightChecked _ _)) =
    AlignedStep leftAction leftTag leftChecked
      (MoreTransitions
        (Fired nameEq keyEq rightAction rightTag rightChecked) NoTransitions)
      (AlignedStep rightAction rightTag rightChecked NoTransitions AlignedEnd)

||| A genuine O/A producer reconstructs the early activation by the outer
||| checked evaluator. The source pair and reconstructed singleton therefore
||| supply exactly the three erased premise occurrences authorized in revision 14.
0 genuineO4AlignmentsPositive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, earlyRightFinal : SystemState name key value world error} ->
  (premises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq
    (MoreTransitions left (MoreTransitions right suffix))) ->
  (earlyAction : Action name key value world error) ->
  (earlyTag : RuleTag) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq} earlyAction first =
    Just (earlyTag, earlyRightFinal)) ->
  ( AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions left (MoreTransitions right NoTransitions))
  , AlignedTransitions name key world error value nameEq keyEq
      (MoreTransitions
        (Fired {before = first} {afterState = earlyRightFinal}
          nameEq keyEq earlyAction earlyTag earlyChecked) NoTransitions)
  )
genuineO4AlignmentsPositive nameEq keyEq premises earlyAction earlyTag
  earlyChecked =
    ( alignedMixedPairFromReplayBundle premises
    , AlignedStep earlyAction earlyTag earlyChecked NoTransitions AlignedEnd
    )
