module DGamma.R20WholeBundleMovedAlignmentNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| A `LocalRelationalDiamond` authenticates action/tag observations and its
||| endpoint quotient, but its moved transitions may store arbitrary executable
||| DecEq dictionaries.  The whole `ReplayInvariantBundle` needs literal outer
||| dictionary alignment, which cannot be reconstructed from that interface.
0 localDiamondCannotSupplyMovedAlignment :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))
localDiamondCannotSupplyMovedAlignment nameEq keyEq left right diamond =
  case movedRight diamond of
    Fired storedRightNameEq storedRightKeyEq rightAction rightTag rightChecked =>
      case movedLeft diamond of
        Fired storedLeftNameEq storedLeftKeyEq leftAction leftTag leftChecked =>
          AlignedStep rightAction rightTag rightChecked
            (MoreTransitions (movedLeft diamond) NoTransitions)
            (AlignedStep leftAction leftTag leftChecked NoTransitions AlignedEnd)
