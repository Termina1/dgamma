module DGamma.R21CandidateIndependentDictionaryNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R21MovedOutputAlignmentScopingPositive
import Decidable.Equality

%default total

||| Detached checked transitions may store independent executable dictionaries.
||| They cannot populate the frozen `movedPairAligned` field under a caller's
||| outer dictionaries; the exact field index rejects this attempted forgery.
0 forgeCandidateFromIndependentDictionaries :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (movedRight : Transition first movedMiddle) ->
  (movedLeft : Transition movedMiddle movedFinal) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
forgeCandidateFromIndependentDictionaries nameEq keyEq movedRight movedLeft =
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
