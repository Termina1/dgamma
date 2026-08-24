module DGamma.R13O3AlignedProducerPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| A genuine adjacent-swap source does not manufacture dictionary equalities.
||| Its replay bundle already refines the retained pair to the outer dictionaries.
0 alignedPairFromReplayBundle :
  (premises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq
    (MoreTransitions left (MoreTransitions right suffix))) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
alignedPairFromReplayBundle premises with (replayAligned premises)
  alignedPairFromReplayBundle premises |
      (AlignedStep leftAction leftTag leftChecked _
        (AlignedStep rightAction rightTag rightChecked _ _)) =
    AlignedStep leftAction leftTag leftChecked
      (MoreTransitions
        (Fired nameEq keyEq rightAction rightTag rightChecked) NoTransitions)
      (AlignedStep rightAction rightTag rightChecked NoTransitions AlignedEnd)

||| The operational producer reconstructs `earlyRight` with the same outer
||| dictionaries. Together with the split bundle this constructs exactly the two
||| erased premises accepted by the revision-13 O3 declaration.
0 genuineO3AlignmentsPositive :
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
genuineO3AlignmentsPositive nameEq keyEq premises earlyAction earlyTag
  earlyChecked =
    ( alignedPairFromReplayBundle premises
    , AlignedStep earlyAction earlyTag earlyChecked NoTransitions AlignedEnd
    )

||| Revision 17: the genuine A/A local producer exports exactly the
||| actor-name-indexed control relation consumed by suffix replay.
0 genuineAAControlProducer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyRightFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (earlyRight : Transition first earlyRightFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight NoTransitions)) ->
  (actionEq : transitionAction earlyRight = transitionAction right) ->
  (tagEq : transitionTag earlyRight = transitionTag right) ->
  (leftPaper : PaperActivationStep left) ->
  (rightPaper : PaperActivationStep right) ->
  (distinct : Not (transitionActor left = transitionActor right)) ->
  (wellFormed : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (independent : TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  ControlEquivalent name key world error value nameEq originalFinal
    (swappedFinal (activationActivationDiamondSpike nameEq keyEq left right
      earlyRight sourceAligned earlyRightAligned actionEq tagEq leftPaper
      rightPaper distinct wellFormed independent))
genuineAAControlProducer nameEq keyEq left right earlyRight sourceAligned
  earlyRightAligned actionEq tagEq leftPaper rightPaper distinct wellFormed
  independent = swappedControlEquivalent
    (activationActivationDiamondSpike nameEq keyEq left right earlyRight
      sourceAligned earlyRightAligned actionEq tagEq leftPaper rightPaper distinct
      wellFormed independent)
