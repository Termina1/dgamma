module DGamma.R179RankedTraceSelectionPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5RankedTraceSelectionSpike
import DGamma.CP5ConfluenceWorkMeasureSpike
import DGamma.Section3Example
import DGamma.Unified
import Data.Maybe
import Data.Nat
import Data.List.Elem
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

||| The actual trace has four checked actions. Under fixed desired order [1,0],
||| the selector returns the two Begin steps at ordinals2/3, never either root
||| barrier, and retains empty suffix plus the exact descending ranks1/0.
export
0 r179RankedSelectionChecks :
  ((transitionCount (certifiedTrace r179RankedSelectionTrace) = 4),
   ((the (Maybe (Nat, Nat, Nat, Nat, Nat, Nat)) (case findActualRankDescent Nat ToyKey ToyRuntime String ToyValue
      (the (Action Nat ToyKey ToyValue ToyRuntime String -> Maybe Nat)
        (\action => case action of
          LBegin Z => Just 1
          LBegin (S Z) => Just 0
          _ => Nothing))
      (certifiedTrace r179RankedSelectionTrace) of
      Nothing => Nothing
      Just choice => Just (transitionCount (traceDescentPrefix choice),
        transitionActor (traceDescentLeft choice), transitionActor (traceDescentRight choice),
        traceDescentLeftRank choice, traceDescentRightRank choice, transitionCount (traceDescentSuffix choice)))) = Just (2, 0, 1, 1, 0, 0)))
r179RankedSelectionChecks = (Refl, Refl)
