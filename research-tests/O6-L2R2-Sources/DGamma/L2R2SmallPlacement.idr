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
smallAvailabilityTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit)
  (beforeActionOccurrence smallRootBirth)
smallAvailabilityTrail =
  (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)))
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution))
    NoTransitions
    (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (smallState 4))))))

||| Every strictly earlier cut is incompatible for the ACTUAL located root
||| birth. In particular, retiring the present child at cut3 does not free its
||| declared key; only Remove1 produces compatible cut4. No finite sample is
||| substituted for this quantified Nat/LT statement.
export
0 smallEarlierUnavailable : (earlier : Nat) -> LT earlier (locatedActionOrdinal smallRootBirth) ->
  DGamma.CP5AvailabilityAwarePlacement.rootCutCompatible Nat Bool Unit String (\key => Unit) %search %search
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
0 smallRootEarliest : DGamma.CP5AvailabilityAwarePlacement.EarliestAvailableRootBirth Nat Bool Unit String (\key => Unit)
  %search %search smallTrace 3 (smallComponent True) smallRootBirth
smallRootEarliest = DGamma.CP5AvailabilityAwarePlacement.MkEarliestAvailableRootBirth smallAvailabilityTrail Refl smallEarlierUnavailable

||| Explicit retired strict clause: each root birth precedes EVERY lifecycle
||| action, including actions of OTHER actors. This is a predicate TYPE, not
||| the availability-aware production CanonicalInputPlacement and not inhabited
||| universally. The fixture rejection below is the retained A12 countershape.
public export
0 StrictRootBeforeAnyLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> Type
StrictRootBeforeAnyLifecycle {name} {key} {world} {error} {value} trace =
  {root : name} -> {component : Component key value world error} ->
  (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
  {action : Action name key value world error} ->
  (lifecycle : LocatedActionOccurrence action trace) ->
  isLifecycleAction action = True ->
  LT (locatedActionOrdinal birth) (locatedActionOrdinal lifecycle)

||| The retired strict placement rejects this fixture; A8/A12 replace it.
||| Root3's ordinal4 cannot precede actor0's lifecycle at ordinal0. This does
||| NOT reject the new availability-aware CanonicalInputPlacement; its weaker
||| own-lifecycle clause is intentionally not the predicate consumed here.
export
0 smallStrictPlacementRejected : StrictRootBeforeAnyLifecycle smallTrace -> Void
smallStrictPlacementRejected strict =
  succNotLTEzero (strict smallRootBirth
    (MkLocatedActionOccurrence (smallState 0) (smallState 1) NoTransitions
      (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution))
      (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions)))))) Refl Refl) Refl)
