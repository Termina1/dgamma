module DGamma.R202NativeInsertScansPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationScan
import DGamma.CP5O20NativeInsertEnvironmentSpike
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
