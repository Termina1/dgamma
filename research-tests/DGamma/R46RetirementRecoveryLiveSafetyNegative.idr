module DGamma.R46RetirementRecoveryLiveSafetyNegative

import DGamma.Calculus
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R46RetirementRecoverySwapSafetyDesignPositive

%default total
%unbound_implicits off

||| Expected failure: the operational ORetire/LLeave countershape is checked and
||| independent, but LLeave is not one of Lemma 71's activation classifiers.
||| Therefore it cannot enter the landed revision-21 safety family.
0 retirementRecoveryCannotEnterLiveSafety :
  CandidateRegistrationSwapSafety r46RetireChild r46LeaveParent
retirementRecoveryCannotEnterLiveSafety =
  CandidateOrchestrationActivation
    (PaperRetireStep Refl)
    (PaperFinishStep Refl Refl)
    (\child, parent, component, insertion => case insertion of Refl impossible)
    (\child, parent, component, insertion => case insertion of Refl impossible)
