module DGamma.L2R2SmallPlacement

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual root birth at ordinal4 in the explicit seven-edge native trace.
||| Its before/after states and four-edge prefix are constructed together;
||| this is not the exhausted nested R174 transparent-collision occurrence.
public export
smallRootBirth : LocatedActionOccurrence (OInsert 3 Root (smallComponent True)) smallTrace
smallRootBirth = MkLocatedActionOccurrence (smallState 4) (smallState 5)
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
      (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
        (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))))
  (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
  (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions))
  Refl Refl

||| Actual-state annotation of the located birth's four-edge prefix, including
||| the still-occupied retired-child state3 and the freed state4 endpoint.
public export
smallAvailabilityTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit)
  (beforeActionOccurrence smallRootBirth)
smallAvailabilityTrail =
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)))
    (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))
    (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)
    (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    NoTransitions
    (AvailabilityEnd (smallState 4))))))

||| Every strictly earlier cut is incompatible for the ACTUAL located root
||| birth. In particular, retiring the present child at cut3 does not free its
||| declared key; only Remove1 produces compatible cut4. No finite sample is
||| substituted for this quantified Nat/LT statement.
export
0 smallEarlierUnavailable : (earlier : Nat) -> LT earlier (locatedActionOrdinal smallRootBirth) ->
  rootCutCompatible Nat Bool Unit String (\key => Unit) %search %search
    (smallComponent True) earlier smallAvailabilityTrail = False
smallEarlierUnavailable Z bounded = Refl
smallEarlierUnavailable (S Z) bounded = Refl
smallEarlierUnavailable (S (S Z)) bounded = Refl
smallEarlierUnavailable (S (S (S Z))) bounded = Refl
smallEarlierUnavailable (S (S (S (S later)))) bounded =
  void (succNotLTEzero (fromLteSucc (fromLteSucc (fromLteSucc (fromLteSucc bounded)))))

||| The actual located root birth inhabits R178's availability-aware EARLIEST
||| clause (replacement of CP3:3164/3173 strict root placement). Current
||| compatibility and ALL earlier-cut exclusions are proved. This certificate
||| is not yet the entire AvailabilityAwareCanonicalInputPlacement package.
public export
0 smallRootEarliest : EarliestAvailableRootBirth Nat Bool Unit String (\key => Unit)
  %search %search smallTrace 3 (smallComponent True) smallRootBirth
smallRootEarliest = MkEarliestAvailableRootBirth smallAvailabilityTrail Refl smallEarlierUnavailable

||| The FROZEN strict CanonicalInputPlacement (CP3:3156, field3173) is
||| uninhabited for this actual native trace, for EVERY support state/order.
||| Its root-before-every-lifecycle clause would require ordinal4 < ordinal0.
||| This is an actual negative certificate, not a sampled Boolean rejection.
export
0 smallStrictPlacementRejected :
  (supportState : SystemState Nat Bool (\key => Unit) Unit String) -> (order : List Nat) ->
  CanonicalInputPlacement Nat Bool Unit String (\key => Unit) %search %search supportState order smallTrace -> Void
smallStrictPlacementRejected supportState order placement =
  succNotLTEzero (rootGenerationBeforeLifecycle placement smallRootBirth
    (MkLocatedActionOccurrence (smallState 0) (smallState 1) NoTransitions
      (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
      (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions)))))) Refl Refl) Refl)
