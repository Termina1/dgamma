module DGamma.L2R4FixtureSeparation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3FixtureCoverage
import DGamma.L2R4OrdinalObservation
import DGamma.L2R4NoStraddling
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Universal over all bundle decompositions of SAME smallTrace, not only R's
||| selected catalog interval. Its explicit checked trace has LBegin2 at5.
export
0 smallNoBundleStraddles : NoBundleStraddlesCut %search %search smallTrace 5
smallNoBundleStraddles = beginCutNoStraddling 5 2 Refl
