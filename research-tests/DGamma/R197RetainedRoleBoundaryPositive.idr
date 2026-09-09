module DGamma.R197RetainedRoleBoundaryPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures

%default total
%unbound_implicits off

||| The one-origin R178 words both contain ONLY closing-free paper roles,
||| but their final child roles differ (Begin/Finish versus Retire). This is
||| unilateral role classification, NOT independent canonical capital or
||| an accepted synchronization/convergence counterexample.
export
0 r197OneOriginRoleWords :
  (O20CanonicalTraceRoles r178LeftTrace, O20CanonicalTraceRoles r178RightTrace)
r197OneOriginRoleWords =
  (O20RolesStep (Right (PaperInsertStep Refl))
    (O20RolesStep (Left (PaperBeginStep Refl Refl))
      (O20RolesStep (Right (PaperInsertStep Refl))
        (O20RolesStep (Left (PaperFinishStep Refl Refl))
          (O20RolesStep (Left (PaperBeginStep Refl Refl))
            (O20RolesStep (Left (PaperFinishStep Refl Refl)) O20RolesEnd))))),
   O20RolesStep (Right (PaperInsertStep Refl))
    (O20RolesStep (Left (PaperBeginStep Refl Refl))
      (O20RolesStep (Right (PaperInsertStep Refl))
        (O20RolesStep (Left (PaperFinishStep Refl Refl))
          (O20RolesStep (Right (PaperRetireStep Refl)) O20RolesEnd)))))
