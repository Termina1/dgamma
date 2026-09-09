module DGamma.R202NativeInsertScansPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationScan
import DGamma.CP5O20NativeInsertEnvironmentSpike
import DGamma.CP5O20ActivationPositionStepSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R191CanonicalChildRetirementGap
import DGamma.R193VestigialHistoryTransportPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Both actual child source cuts now have PRODUCED native prefix scans,
||| including CP3's append order. The lists are EXPECTED OUTPUTS in the
||| fixture, not arbitrary environments passed to the stage producer.
export
0 r202NativeChildBirthScans :
  (GenerationTraceScan r45NameEq Z [] (prefixToBlockOpening (r191ChildGapBlocks 0 Here)) 4
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2)],
   GenerationTraceScan r45NameEq Z [] (beforeRegistration r193HistoricalBirth) 2
    [(0, MkRegistrationGeneration 0 0)])
r202NativeChildBirthScans =
  (o20NativePrefixScan r45NameEq (prefixToBlockOpening (r191ChildGapBlocks 0 Here)),
   o20NativePrefixScan r45NameEq (beforeRegistration r193HistoricalBirth))

||| Regression for the NATIVE per-activation index algebra at the historical
||| root/begin prefix: deleted births consume zero positions and surviving
||| births consume one. These are two classifier branches, NOT a claim that
||| the same historical birth has both accepted classifications or a theorem
||| transporting arbitrary canonical prefixes.
export
0 r202ClassifiedActivationPositions :
  (eventChildPosition (registrationEventAt @{r45NameEq} 3
      (advanceDeletedRegistrationIndex @{r45NameEq} 2 1 0 r45Child
        (advanceRegistrationIndex @{r45NameEq} 1 (the (Action Nat R45Key R45Value Unit String) (LBegin 0)) (advanceRegistrationIndex @{r45NameEq} 0 (OInsert 0 Root r45Parent) emptyRegistrationIndex))) 2 0 r45Child) = 0,
   eventChildPosition (registrationEventAt @{r45NameEq} 3
      (advanceSurvivingRegistrationIndex @{r45NameEq} 2 1 0 r45Child
        (advanceRegistrationIndex @{r45NameEq} 1 (the (Action Nat R45Key R45Value Unit String) (LBegin 0)) (advanceRegistrationIndex @{r45NameEq} 0 (OInsert 0 Root r45Parent) emptyRegistrationIndex))) 2 0 r45Child) = 1)
r202ClassifiedActivationPositions =
  (o20DeletedBirthPreservesObservedPosition r45NameEq 2 3 1 0 2 0 r45Child r45Child
    (advanceRegistrationIndex @{r45NameEq} 1 (the (Action Nat R45Key R45Value Unit String) (LBegin 0)) (advanceRegistrationIndex @{r45NameEq} 0 (OInsert 0 Root r45Parent) emptyRegistrationIndex)) (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl,
   o20SurvivingBirthAdvancesObservedPosition r45NameEq 2 3 1 0 2 r45Child r45Child
    (advanceRegistrationIndex @{r45NameEq} 1 (the (Action Nat R45Key R45Value Unit String) (LBegin 0)) (advanceRegistrationIndex @{r45NameEq} 0 (OInsert 0 Root r45Parent) emptyRegistrationIndex)) (MkRegistrationActivation (MkRegistrationGeneration 0 0) 1) Refl)
