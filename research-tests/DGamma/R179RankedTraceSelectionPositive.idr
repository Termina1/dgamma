module DGamma.R179RankedTraceSelectionPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5RankedTraceSelectionSpike
import DGamma.CP5ConfluenceWorkMeasureSpike
import DGamma.Section3Example
import DGamma.Unified
import Data.List
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

||| The EXACT private-worklist rank observer selects this real checked pair.
||| The real early right Begin1 succeeds before Begin0: actor0 stays uninstalled,
||| actor1 becomes installed. The early packet's type authenticates the exact
||| original action AND tag. This does not assert the opaque orientation
||| inspector's optional result or any general completeness property.
export
0 r179CanonicalObservedEarlyChecks :
  ((transitionCount (certifiedTrace r179RankedSelectionTrace) = 4),
   ((the (Maybe (Nat, Nat, Nat, Bool, Bool)) (case findActualRankDescent Nat ToyKey ToyRuntime String ToyValue
      (canonicalWorkActionRank Nat ToyKey ToyRuntime String ToyValue %search [1, 0])
      (certifiedTrace r179RankedSelectionTrace) of
      Nothing => Nothing
      Just choice => case checkSelectedEarlyRight Nat ToyKey ToyRuntime String ToyValue %search %search
        (canonicalWorkActionRank Nat ToyKey ToyRuntime String ToyValue %search [1, 0])
        (certifiedTrace r179RankedSelectionTrace) choice of
        Nothing => Nothing
        Just early => Just (transitionCount (traceDescentPrefix choice),
          transitionActor (traceDescentLeft choice), transitionActor (traceDescentRight choice),
          (case lookupFiber 0 (registry (earlyApplicationFinal early)) of
            Nothing => False
            Just fiber => installed (fiberLifecycle fiber)),
          (case lookupFiber 1 (registry (earlyApplicationFinal early)) of
            Nothing => False
            Just fiber => installed (fiberLifecycle fiber))))) = Just (2, 0, 1, False, True)))
r179CanonicalObservedEarlyChecks = (Refl, Refl)
