module DGamma.R179RankedTraceSelectionPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5RankedTraceSelectionSpike
import DGamma.Section3Example
import DGamma.Unified
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Two real empty-program actors begin after their root insertion barriers.
||| The next observation must exclude the builder's empty default branch.
export
0 r179RankedSelectionTrace : CertifiedActionTrace Nat ToyKey ToyRuntime String ToyValue %search %search
  (MkSystemState (MkToyRuntime False False) emptyContext)
r179RankedSelectionTrace = fromMaybe
  (MkCertifiedActionTrace (MkSystemState (MkToyRuntime False False) emptyContext) NoTransitions TraceComponentsTotalEnd)
  (buildCertifiedActionTrace %search %search
    [OInsert 0 Root (MkComponent DGamma.CalculusChecks.toyEmptySpec DGamma.CalculusChecks.toyEmptySpec []),
     OInsert 1 Root (MkComponent DGamma.CalculusChecks.toyEmptySpec DGamma.CalculusChecks.toyEmptySpec []),
     LBegin 0, LBegin 1]
    (MkSystemState (MkToyRuntime False False) emptyContext))
