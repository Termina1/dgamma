module DGamma.R45BareDiamondSafetyProjectionNegative

import DGamma.Calculus
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive

%default total

||| Permanent revision-21 counterexample pin.  The old bare operational record
||| is inhabited in the paired positive module, but the live safety-gated
||| constructor requires this A/O parent exclusion.  Instantiating it at the
||| concrete LBegin-parent/OInsert-child pair asks for `Not (0 = 0)` and must be
||| rejected before a LocalRelationalDiamond can be built.
0 bareDiamondCannotProjectRegistrationSafety :
  CandidateRegistrationSwapSafety
    DGamma.R45BareDiamondDisciplineCounterexamplePositive.r45Begin
    DGamma.R45BareDiamondDisciplineCounterexamplePositive.r45ChildInsert
bareDiamondCannotProjectRegistrationSafety =
  CandidateActivationOrchestration (PaperBeginStep Refl Refl)
    (PaperInsertStep Refl)
    (\child, parent, component, actionSame, actorSame =>
      case actionSame of
        Refl => case actorSame of Refl impossible)
