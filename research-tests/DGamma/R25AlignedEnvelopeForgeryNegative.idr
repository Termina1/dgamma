module DGamma.R25AlignedEnvelopeForgeryNegative

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R21MovedOutputAlignmentScopingPositive
import DGamma.R23CorrectedInternalFixturePositive
import Decidable.Equality

%default total

||| Revision 25's envelope is safe only because its moved transition is the
||| exact transition returned by the concrete A/A producer.  A caller cannot
||| reproduce that population step for an arbitrary legacy diamond whose moved
||| transitions store independently chosen executable dictionaries.
0 forgeAlignedEnvelopeFromIndependentDictionaries :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  CandidateAlignedLocalRelationalDiamond name key world error value nameEq keyEq
    left right
forgeAlignedEnvelopeFromIndependentDictionaries nameEq keyEq left right diamond =
  case movedRight diamond of
    Fired storedRightNameEq storedRightKeyEq rightAction rightTag rightChecked =>
      case movedLeft diamond of
        Fired storedLeftNameEq storedLeftKeyEq leftAction leftTag leftChecked =>
          sealAlignedLocalRelationalDiamond diamond
            (activationActivationConstructorMovedAlignment nameEq keyEq
              (movedRight diamond)
              (AlignedStep rightAction rightTag rightChecked NoTransitions
                AlignedEnd)
              leftAction leftTag leftChecked)
