module DGamma.R21CandidateIndependentDictionaryNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R21MovedOutputAlignmentScopingPositive
import Decidable.Equality

%default total

||| An arbitrary legacy diamond may store independent executable dictionaries.
||| The candidate cannot be sealed by reusing its checked equations under the
||| caller's outer dictionaries; the exact alignment index rejects the forgery.
0 forgeCandidateFromIndependentDictionaries :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  CandidateAlignedLocalRelationalDiamond name key world error value nameEq keyEq
    left right
forgeCandidateFromIndependentDictionaries nameEq keyEq left right diamond =
  case movedRight diamond of
    Fired storedRightNameEq storedRightKeyEq rightAction rightTag rightChecked =>
      case movedLeft diamond of
        Fired storedLeftNameEq storedLeftKeyEq leftAction leftTag leftChecked =>
          sealAlignedLocalRelationalDiamond diamond
            (AlignedStep rightAction rightTag rightChecked
              (MoreTransitions (movedLeft diamond) NoTransitions)
              (AlignedStep leftAction leftTag leftChecked NoTransitions
                AlignedEnd))
