module DGamma.R199DeletionDisappearanceBoundaryPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DeletionDisappearanceSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import DGamma.R193VestigialHistoryTransportPositive
import DGamma.R195EndpointRebaseBoundaryPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Actual WHOLE-word scanner instances for both the eight-edge present
||| vestigial history and the six-edge removed history. The public asynchronous
||| accepted correspondences themselves produce the final live environments;
||| no fresh guessed scanner or canonical-capital assumption is supplied.
export
0 r199ActualAcceptedGenerationScans :
  ((finalOrdinal : Nat ** GenerationTraceScan {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
    r45NameEq Z [] r193HistoricalClosedTrace finalOrdinal (leftFinalGenerations r193HistoricalTree)),
   (finalOrdinal : Nat ** GenerationTraceScan {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
    r45NameEq Z [] r192RemovedBirthTrace finalOrdinal (leftFinalGenerations r192RemovedBirthTree)))
r199ActualAcceptedGenerationScans =
  (o20DeletionSideGenerationScan Nat R45Key Unit String R45Value r45NameEq identityRegistrationGenerationBijection
    Z emptyRegistrationIndex Z emptyRegistrationIndex r193HistoricalClosedTrace r193HistoricalClosedTrace
    (leftFinalIndex r193HistoricalTree) (rightFinalIndex r193HistoricalTree) (generationTraceCorrespondence r193HistoricalTree),
   o20DeletionSideGenerationScan Nat R45Key Unit String R45Value r45NameEq identityRegistrationGenerationBijection
    Z emptyRegistrationIndex Z emptyRegistrationIndex r192RemovedBirthTrace r192RemovedBirthTrace
    (leftFinalIndex r192RemovedBirthTree) (rightFinalIndex r192RemovedBirthTree) (generationTraceCorrespondence r192RemovedBirthTree))

||| CONDITIONAL canonical boundary for the genuine R193/R195 name1->2
||| obstruction. The FULL original vestigial packet and opposite original
||| absence are fixture-produced. Accepted canonical/permutation capital and
||| membership in its own first deletion node remain explicit inputs. This
||| does NOT claim that the fixture now owns independent canonical capital.
export
0 r199SelectedVestigialCurrentBoundary :
  (leftCapital, rightCapital : IndependentCanonicalSchedule Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r193HistoricalClosedTrace) ->
  (matching : MappedCanonicalSupportOrders Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq
    r193HistoricalClosedTrace r193HistoricalClosedTrace (expectedBridgeBijection r193HistoricalSameInputs)
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  (operational : CertifiedOperationalCanonicalPermutation Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq r193HistoricalClosedTrace r193HistoricalClosedTrace
    r193HistoricalSameInputs leftCapital rightCapital matching) ->
  (execution : PermutedCanonicalExecution Nat R45Key Unit String R45Value r45Protocol r45NameEq r45KeyEq
    r193HistoricalClosedTrace r193HistoricalClosedTrace r193HistoricalSameInputs leftCapital rightCapital operational) ->
  Elem (vestigialGeneration r193HistoricalVestigial)
    (o20DeletionHeadGenerations (reductionDeletionDerivation (capitalReduction leftCapital))) ->
  MaybeFiberRelatedBy (expectedBridgeBijection r193HistoricalSameInputs)
    (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq}
      1 (registry (operationalTargetFinal operational)))
    (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq}
      (renameForward (expectedBridgeBijection r193HistoricalSameInputs) 1) (registry (canonicalFinal (canonicalSchedule rightCapital))))
r199SelectedVestigialCurrentBoundary leftCapital rightCapital matching operational execution member =
  o20SelectedVestigialAbsentReplayedControls {sameInputs = r193HistoricalSameInputs}
    {leftCapital} {rightCapital} {operational} execution 1 r193HistoricalVestigial member
    (snd r193VestigialCurrentPresence)
