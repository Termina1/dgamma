module DGamma.R21MovedOutputAlignmentScopingPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R19SuffixFreeFullAdjacentCertificatePositive
import Decidable.Equality

%default total

||| Compatibility name for the now-frozen aligned local diamond.  Revision 21
||| no longer wraps or accepts detached alignment capital: the live producer
||| record owns the exact erased `movedPairAligned` field.
public export
CandidateAlignedLocalRelationalDiamond :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) -> Type
CandidateAlignedLocalRelationalDiamond name key world error value nameEq keyEq
  left right = LocalRelationalDiamond name key world error value nameEq keyEq
    left right

public export
0 baseDiamond :
  CandidateAlignedLocalRelationalDiamond name key world error value nameEq keyEq
    left right ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
baseDiamond diamond = diamond

||| Both moved steps were just checked with the outer dictionaries.  This is
||| precisely the constructor-local capital held by the A/O implementation.
public export
0 activationOrchestrationConstructorMovedAlignment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, movedMiddle, movedFinal : SystemState name key value world error} ->
  (rightAction : Action name key value world error) -> (rightTag : RuleTag) ->
  (0 rightChecked : checkedApplyAction @{nameEq} @{keyEq} rightAction first =
    Just (rightTag, movedMiddle)) ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (0 leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction movedMiddle =
    Just (leftTag, movedFinal)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = movedMiddle}
        nameEq keyEq rightAction rightTag rightChecked)
      (MoreTransitions
        (Fired {before = movedMiddle} {afterState = movedFinal}
          nameEq keyEq leftAction leftTag leftChecked)
        NoTransitions))
activationOrchestrationConstructorMovedAlignment nameEq keyEq rightAction
  rightTag rightChecked leftAction leftTag leftChecked =
    AlignedStep rightAction rightTag rightChecked
      (MoreTransitions
        (Fired {before = movedMiddle} {afterState = movedFinal}
          nameEq keyEq leftAction leftTag leftChecked)
        NoTransitions)
      (AlignedStep leftAction leftTag leftChecked NoTransitions AlignedEnd)

||| The A/A implementation already receives the exact early-right singleton
||| alignment and constructs moved-left with the outer dictionaries.
public export
0 activationActivationConstructorMovedAlignment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, movedMiddle, movedFinal : SystemState name key value world error} ->
  (earlyRight : Transition first movedMiddle) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq
    keyEq (MoreTransitions earlyRight NoTransitions)) ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (0 leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction movedMiddle =
    Just (leftTag, movedFinal)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight
      (MoreTransitions
        (Fired {before = movedMiddle} {afterState = movedFinal}
          nameEq keyEq leftAction leftTag leftChecked)
        NoTransitions))
activationActivationConstructorMovedAlignment nameEq keyEq earlyRight
  earlyRightAligned leftAction leftTag leftChecked =
    case earlyRightAligned of
      AlignedStep rightAction rightTag rightChecked NoTransitions AlignedEnd =>
        AlignedStep rightAction rightTag rightChecked
          (MoreTransitions
            (Fired {before = movedMiddle} {afterState = movedFinal}
              nameEq keyEq leftAction leftTag leftChecked)
            NoTransitions)
          (AlignedStep leftAction leftTag leftChecked NoTransitions AlignedEnd)

||| O/A has the same constructor-local alignment shape as A/A: checked early
||| activation plus a newly checked outer-dictionary orchestration step.
public export
0 orchestrationActivationConstructorMovedAlignment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, movedMiddle, movedFinal : SystemState name key value world error} ->
  (earlyRight : Transition first movedMiddle) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq
    keyEq (MoreTransitions earlyRight NoTransitions)) ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (0 leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction movedMiddle =
    Just (leftTag, movedFinal)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight
      (MoreTransitions
        (Fired {before = movedMiddle} {afterState = movedFinal}
          nameEq keyEq leftAction leftTag leftChecked)
        NoTransitions))
orchestrationActivationConstructorMovedAlignment =
  activationActivationConstructorMovedAlignment

||| O/O likewise receives the exact safety-owned early-right singleton
||| alignment and constructs moved-left using the outer dictionaries.
public export
0 orchestrationOrchestrationConstructorMovedAlignment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, movedMiddle, movedFinal : SystemState name key value world error} ->
  (earlyRight : Transition first movedMiddle) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq
    keyEq (MoreTransitions earlyRight NoTransitions)) ->
  (leftAction : Action name key value world error) -> (leftTag : RuleTag) ->
  (0 leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction movedMiddle =
    Just (leftTag, movedFinal)) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight
      (MoreTransitions
        (Fired {before = movedMiddle} {afterState = movedFinal}
          nameEq keyEq leftAction leftTag leftChecked)
        NoTransitions))
orchestrationOrchestrationConstructorMovedAlignment =
  activationActivationConstructorMovedAlignment

||| The live full suffix-free fixture is also migratable: its source bundle
||| authenticates the exact two-node trace, and its moved nodes are literally
||| those same source transitions.
public export
0 fullSuffixFreeFixtureMovedAlignment :
  (source : ReplayInvariantBundle name key world error value protocol nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
fullSuffixFreeFixtureMovedAlignment = replayAligned

||| Wrappers and consumers of the four live producers need no independent
||| dictionary proof after migration: the sealed candidate projection is exact.
public export
0 candidateMovedAlignmentProjection :
  (candidate : CandidateAlignedLocalRelationalDiamond name key world error value
    nameEq keyEq left right) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (movedRight (baseDiamond candidate))
      (MoreTransitions (movedLeft (baseDiamond candidate)) NoTransitions))
candidateMovedAlignmentProjection candidate = movedPairAligned candidate
