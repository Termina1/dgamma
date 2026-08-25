module DGamma.R29RetainedFinishTargetBundlePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.R21MovedOutputAlignmentScopingPositive
import DGamma.R23CorrectedInternalFixturePositive
import DGamma.R28RetainedFinishIndependencePositive

%default total
%unbound_implicits off

public export
0 r29Reached : ReachedFromEmpty Nat R23Key Unit Unit R23Value r23NameEq r23KeyEq
  (replayedAfter (baseFinishReplay r27SecondFinishEnvelope))
r29Reached = MkReachedFromEmpty _ r27WholeTargetTrace r27WholeAligned
  r27InitialEmpty r27InitialWellFormed

public export
0 r29Provenance : RegistrationProvenance r23Protocol r23NameEq
  r27WholeTargetTrace
r29Provenance = registrationDisciplineProvenance r23Protocol r23NameEq
  r27WholeTargetTrace r27WholeDiscipline
