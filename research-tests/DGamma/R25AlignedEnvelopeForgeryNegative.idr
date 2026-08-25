module DGamma.R25AlignedEnvelopeForgeryNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R21MovedOutputAlignmentScopingPositive
import DGamma.R23CorrectedInternalFixturePositive
import Decidable.Equality

%default total

||| Revision 25 now consumes the frozen producer-owned alignment.  A caller
||| still cannot manufacture that field for independently stored executable
||| dictionaries: the exact outer-dictionary index rejects the forgery.
0 forgeAlignedEnvelopeFromIndependentDictionaries :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (movedRight : Transition first movedMiddle) ->
  (movedLeft : Transition movedMiddle movedFinal) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
forgeAlignedEnvelopeFromIndependentDictionaries nameEq keyEq movedRight movedLeft =
  case movedRight of
    Fired storedRightNameEq storedRightKeyEq rightAction rightTag rightChecked =>
      case movedLeft of
        Fired storedLeftNameEq storedLeftKeyEq leftAction leftTag leftChecked =>
          activationActivationConstructorMovedAlignment nameEq keyEq
            (Fired storedRightNameEq storedRightKeyEq rightAction rightTag
              rightChecked)
            (AlignedStep rightAction rightTag rightChecked NoTransitions
              AlignedEnd)
            leftAction leftTag leftChecked
