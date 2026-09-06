module DGamma.R173CanonicalBlockWorklistFixtures

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Data.Maybe

%default total
%unbound_implicits off

||| Real block-scan regressions, not whole-O17 telescope fixtures.
||| First finish the parent directly after its genuine child registration.
r173ContiguousFinal : SystemState Nat R45Key R45Value Unit String
r173ContiguousFinal = maybe r45SourcePairFinal snd
  (checkedApplyAction @{r45NameEq} @{r45KeyEq} (LAdvance 0) r45SourcePairFinal)
