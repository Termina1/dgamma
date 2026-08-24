module DGamma.R24CorrectedWholeAlignmentNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Expected failure reached by the corrected R23 fixture after both checked
||| suffix heads replay.  The first field of the whole target
||| `ReplayInvariantBundle` is `replayAligned`.  The unmodified
||| `LocalRelationalDiamond` has already forgotten the producer's exact outer
||| dictionaries, so a consumer cannot recover the moved-pair alignment by
||| destructing its transitions.  R23 instantiates this boundary with its
||| concrete O19-internal activation diamond.
0 correctedFixtureCannotRecoverMovedPairAlignment :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))
correctedFixtureCannotRecoverMovedPairAlignment nameEq keyEq left right diamond =
  case movedRight diamond of
    Fired storedRightNameEq storedRightKeyEq rightAction rightTag rightChecked =>
      case movedLeft diamond of
        Fired storedLeftNameEq storedLeftKeyEq leftAction leftTag leftChecked =>
          AlignedStep rightAction rightTag rightChecked
            (MoreTransitions (movedLeft diamond) NoTransitions)
            (AlignedStep leftAction leftTag leftChecked NoTransitions AlignedEnd)
