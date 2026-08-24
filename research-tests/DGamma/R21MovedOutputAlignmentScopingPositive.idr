module DGamma.R21MovedOutputAlignmentScopingPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R19SuffixFreeFullAdjacentCertificatePositive
import Decidable.Equality

%default total

||| Test-local candidate for the exact producer-carried delta.  The live record
||| is unchanged; this wrapper makes the proposed erased field consumer-visible
||| while keeping it indexed by the exact moved transitions of the sealed base.
public export
record CandidateAlignedLocalRelationalDiamond
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, middle, originalFinal : SystemState name key value world error}
  (left : Transition first middle)
  (right : Transition middle originalFinal) where
  constructor MkCandidateAlignedLocalRelationalDiamond
  baseDiamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right
  0 movedPairAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (movedRight baseDiamond)
      (MoreTransitions (movedLeft baseDiamond) NoTransitions))

||| Candidate constructor.  Its second argument cannot be detached from the
||| moved projections: the negative probe supplies an arbitrary dictionary-
||| storing base and is rejected exactly at this index.
public export
0 sealAlignedLocalRelationalDiamond :
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))) ->
  CandidateAlignedLocalRelationalDiamond name key world error value nameEq keyEq
    left right
sealAlignedLocalRelationalDiamond diamond aligned =
  MkCandidateAlignedLocalRelationalDiamond diamond aligned

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
candidateMovedAlignmentProjection = movedPairAligned
