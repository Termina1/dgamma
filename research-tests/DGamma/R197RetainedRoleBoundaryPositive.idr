module DGamma.R197RetainedRoleBoundaryPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import DGamma.CP5O20RootStageAttachmentSpike
import DGamma.CP5O20GenerationOnlyHistorySpike
import DGamma.R193VestigialHistoryTransportPositive
import DGamma.R195ClosingHistoryRetentionPositive
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

||| The same actual role-word mismatch is excluded by the ACCEPTED E9
||| generated-orchestration premise for every generation bijection. Thus
||| unary closing-free roles do not supply synchronization, but this pair
||| is not a counterexample to the protected accepted convergence statement.
export
0 r197RoleMismatchFailsAcceptedE9 :
  (O20CanonicalTraceRoles r178LeftTrace,
   O20CanonicalTraceRoles r178RightTrace,
   (mapping : RegistrationGenerationBijection Nat) ->
    (GeneratedOrchestrationMatched Nat R45Key Unit String R45Value r45NameEq
      r178LeftTrace r178RightTrace mapping -> Void))
r197RoleMismatchFailsAcceptedE9 =
  (fst r197OneOriginRoleWords, snd r197OneOriginRoleWords,
   r178QuietPairRejectsGeneratedMatching)

||| One actual R193 origin supplies BOTH its matched root/stamp and the R195
||| child closing disposition. Root matching does not discard that child
||| alternative or produce an opposite retained canonical child by fiat.
export
0 r197RootAndClosingBoundary :
  (O20RootBirthMatch Nat R45Key Unit String R45Value identityRegistrationGenerationBijection
    0 r45Parent 0 0 r193HistoricalClosedTrace,
   O20GenerationOnlyDisposition Nat R45Key Unit String R45Value identityRegistrationGenerationBijection
    r193HistoricalClosedTrace r193HistoricalClosedTrace (MkRegistrationGeneration 1 2))
r197RootAndClosingBoundary =
  (o20RootBirthMatchLocated identityRegistrationGenerationBijection
    r193HistoricalClosedTrace r193HistoricalClosedTrace
    (externalRootGenerationsCoupled r193HistoricalSameInputs) 0 r45Parent
    (MkLocatedActionOccurrence r45Initial r45AfterParent NoTransitions r45ParentInsert
      (MoreTransitions r45Begin (MoreTransitions r45ChildInsert r193HistoricalContinuation)) Refl Refl),
   r195ClosingHistoryRetained)
