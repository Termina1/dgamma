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

||| Revision 17: the genuine A/O producer exports the lookup-indexed endpoint
||| control relation, coercing its stronger ordered internal proof.
0 genuineAOControlProducer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (leftPaper : PaperActivationStep left) ->
  (rightPaper : PaperOrchestrationStep right) ->
  (distinct : Not (transitionActor left = transitionActor right)) ->
  (parentSafe : (child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction right = OInsert child (ChildOf parent) component ->
    Not (transitionActor left = parent)) ->
  (wellFormed : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (independent : TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  ControlEquivalent name key world error value nameEq originalFinal
    (swappedFinal (activationOrchestrationDiamondSpike nameEq keyEq left right
      sourceAligned leftPaper rightPaper distinct parentSafe wellFormed
      independent))
genuineAOControlProducer nameEq keyEq left right sourceAligned leftPaper
  rightPaper distinct parentSafe wellFormed independent =
    swappedControlEquivalent
      (activationOrchestrationDiamondSpike nameEq keyEq left right sourceAligned
        leftPaper rightPaper distinct parentSafe wellFormed independent)

||| Revision 17: the genuine O/A producer exports the same consumer-facing
||| lookup relation from its independently checked early activation.
0 genuineOAControlProducer :
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
  (leftPaper : PaperOrchestrationStep left) ->
  (rightPaper : PaperActivationStep right) ->
  (distinct : Not (transitionActor left = transitionActor right)) ->
  (childSafe : (child : name) -> (parent : Parent name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child parent component ->
    Not (transitionActor right = child)) ->
  (parentSafe : (child, parent : name) ->
    (component : Component key value world error) ->
    transitionAction left = OInsert child (ChildOf parent) component ->
    Not (transitionActor right = parent)) ->
  (wellFormed : registryWellFormed @{nameEq} @{keyEq} first = True) ->
  (independent : TraceIndependent name key world error value keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  ControlEquivalent name key world error value nameEq originalFinal
    (swappedFinal (orchestrationActivationDiamondSpike nameEq keyEq left right
      earlyRight sourceAligned earlyRightAligned actionEq tagEq leftPaper
      rightPaper distinct childSafe parentSafe wellFormed independent))
genuineOAControlProducer nameEq keyEq left right earlyRight sourceAligned
  earlyRightAligned actionEq tagEq leftPaper rightPaper distinct childSafe
  parentSafe wellFormed independent = swappedControlEquivalent
    (orchestrationActivationDiamondSpike nameEq keyEq left right earlyRight
      sourceAligned earlyRightAligned actionEq tagEq leftPaper rightPaper distinct
      childSafe parentSafe wellFormed independent)
