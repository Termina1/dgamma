module DGamma.L2R2RootPhase

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1RootExchange
import DGamma.L2R2RootSnapshot
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2SmallPlacement
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| CP3:577 supportSet depends only on ordered runtime bindings. Therefore a
||| snapshot-preserving root exchange preserves the ENTIRE executable support
||| set, without postulating equality of erased UniqueKeys witnesses.
export
0 supportSetAcrossSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : SystemState name key value world error) ->
  (0 same : runtimeSnapshot left = runtimeSnapshot right) ->
  supportSet @{nameEq} @{keyEq} left = supportSet @{nameEq} @{keyEq} right
supportSetAcrossSnapshot {name} {key} {world} {error} {value} nameEq keyEq left right same =
  cong (\snapshot => supportFuel {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (length (snapshotBindings snapshot)) (snapshotBindings snapshot) []) same

||| Snapshot/no-suffix counterpart of CP5L2R1RootExchange:77
||| beginRootExchangeDecreases: the genuine checked Begin/root pair loses
||| exactly ONE lifecycle-before-root inversion for every prior count. Endpoint
||| identity is not required. This LOCAL measure does not replay an arbitrary
||| suffix or prove the prefix's lifecycle count; the physical C20 instance
||| checks its full annotated trace separately.
export
0 beginSnapshotRootDecreases :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor, root : name) -> (component : Component key value world error) ->
  {first, middle, cut : SystemState name key value world error} ->
  (0 beforeBegin : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) first = Just (LBeginTag, middle)) ->
  (0 beforeRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) middle = Just (OInsertTag, cut)) ->
  (exchange : AvailabilityRootSnapshotExchange name key world error value nameEq keyEq root component
    (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin actor) LBeginTag beforeBegin)
    (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot)) ->
  (prior : Nat) ->
  rootBirthInversions prior
    (AvailabilityStep first (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin actor) LBeginTag beforeBegin) (MoreTransitions (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot) NoTransitions)
      (AvailabilityStep middle (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot) NoTransitions (AvailabilityEnd cut))) =
  S (rootBirthInversions prior
    (AvailabilityStep first (Fired {before = first} {afterState = snapshotRootMiddle exchange} nameEq keyEq (OInsert root Root component) OInsertTag (snapshotRootEarly exchange)) (MoreTransitions (Fired {before = snapshotRootMiddle exchange} {afterState = snapshotRootFinal exchange} nameEq keyEq (LBegin actor) LBeginTag (snapshotRootLater exchange)) NoTransitions)
      (AvailabilityStep (snapshotRootMiddle exchange) (Fired {before = snapshotRootMiddle exchange} {afterState = snapshotRootFinal exchange} nameEq keyEq (LBegin actor) LBeginTag (snapshotRootLater exchange)) NoTransitions (AvailabilityEnd (snapshotRootFinal exchange)))))
beginSnapshotRootDecreases nameEq keyEq actor root component beforeBegin beforeRoot exchange prior = Refl

||| Narrow research root-phase step, inspired by CanonicalSort:1583
||| CanonicalRootInsertionHoist but NOT a copy of its full O17 result:
||| arbitrary genuine context BEFORE the pair, no suffix, supplied authenticated
||| availability-aware snapshot square, checked output, support-set equality,
||| exact local measure decrement. ReplayInvariantBundle, canonical placement,
||| generic square production, arbitrary-suffix replay and full normalization
||| remain outside this record. Frozen statements are not weakened.
public export
record SnapshotRootPhaseStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor, root : name) (component : Component key value world error)
  {initial, first, middle, cut : SystemState name key value world error}
  (earlier : Transitions initial first)
  (beforeBegin : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) first = Just (LBeginTag, middle))
  (beforeRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) middle = Just (OInsertTag, cut)) where
  constructor MkSnapshotRootPhaseStep
  rootPhaseSquare : AvailabilityRootSnapshotExchange name key world error value nameEq keyEq root component
    (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin actor) LBeginTag beforeBegin)
    (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot)
  rootPhaseTrace : Transitions initial (snapshotRootFinal rootPhaseSquare)
  0 rootPhasePhysical : rootPhaseTrace = appendTransitions earlier
    (MoreTransitions (Fired {before = first} {afterState = snapshotRootMiddle rootPhaseSquare} nameEq keyEq (OInsert root Root component) OInsertTag (snapshotRootEarly rootPhaseSquare)) (MoreTransitions (Fired {before = snapshotRootMiddle rootPhaseSquare} {afterState = snapshotRootFinal rootPhaseSquare} nameEq keyEq (LBegin actor) LBeginTag (snapshotRootLater rootPhaseSquare)) NoTransitions))
  0 rootPhaseRuntime : runtimeSnapshot cut = runtimeSnapshot (snapshotRootFinal rootPhaseSquare)
  0 rootPhaseSupport : supportSet @{nameEq} @{keyEq} cut = supportSet @{nameEq} @{keyEq} (snapshotRootFinal rootPhaseSquare)
  0 rootPhaseMeasure : (prior : Nat) ->
    rootBirthInversions prior
      (AvailabilityStep first (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin actor) LBeginTag beforeBegin) (MoreTransitions (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot) NoTransitions)
        (AvailabilityStep middle (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot) NoTransitions (AvailabilityEnd cut))) =
    S (rootBirthInversions prior
      (AvailabilityStep first (Fired {before = first} {afterState = snapshotRootMiddle rootPhaseSquare} nameEq keyEq (OInsert root Root component) OInsertTag (snapshotRootEarly rootPhaseSquare)) (MoreTransitions (Fired {before = snapshotRootMiddle rootPhaseSquare} {afterState = snapshotRootFinal rootPhaseSquare} nameEq keyEq (LBegin actor) LBeginTag (snapshotRootLater rootPhaseSquare)) NoTransitions)
        (AvailabilityStep (snapshotRootMiddle rootPhaseSquare) (Fired {before = snapshotRootMiddle rootPhaseSquare} {afterState = snapshotRootFinal rootPhaseSquare} nameEq keyEq (LBegin actor) LBeginTag (snapshotRootLater rootPhaseSquare)) NoTransitions (AvailabilityEnd (snapshotRootFinal rootPhaseSquare)))))

||| Produce the scoped step from an authenticated admissible square, keeping
||| the arbitrary physical earlier context unchanged. This is NOT a square
||| dispatcher or a suffix-replay oracle: the square is an explicit premise,
||| the returned trace is assembled from its actual checked edges, and support
||| preservation follows from runtime binding equality rather than an input
||| support-preservation assumption. No full O17 normalization is claimed.
export
0 rootPhaseFromSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor, root : name) -> (component : Component key value world error) ->
  {initial, first, middle, cut : SystemState name key value world error} ->
  (earlier : Transitions initial first) ->
  (0 beforeBegin : checkedApplyAction @{nameEq} @{keyEq} (LBegin actor) first = Just (LBeginTag, middle)) ->
  (0 beforeRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) middle = Just (OInsertTag, cut)) ->
  (exchange : AvailabilityRootSnapshotExchange name key world error value nameEq keyEq root component
    (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin actor) LBeginTag beforeBegin)
    (Fired {before = middle} {afterState = cut} nameEq keyEq (OInsert root Root component) OInsertTag beforeRoot)) ->
  SnapshotRootPhaseStep name key world error value nameEq keyEq actor root component earlier beforeBegin beforeRoot
rootPhaseFromSnapshot {cut} nameEq keyEq actor root component earlier beforeBegin beforeRoot exchange =
  MkSnapshotRootPhaseStep exchange
    (appendTransitions earlier (MoreTransitions (Fired {before = first} {afterState = snapshotRootMiddle exchange} nameEq keyEq (OInsert root Root component) OInsertTag (snapshotRootEarly exchange)) (MoreTransitions (Fired {before = snapshotRootMiddle exchange} {afterState = snapshotRootFinal exchange} nameEq keyEq (LBegin actor) LBeginTag (snapshotRootLater exchange)) NoTransitions)))
    Refl (snapshotRootSame exchange)
    (supportSetAcrossSnapshot nameEq keyEq cut (snapshotRootFinal exchange) (snapshotRootSame exchange))
    (beginSnapshotRootDecreases nameEq keyEq actor root component beforeBegin beforeRoot exchange)

||| Producer-owned physical C' root-phase evidence: the ORIGINAL six-edge
||| run ends at state9; the swapped six-edge run has a potentially different
||| native endpoint, exposed by its authenticated square. Counts are computed
||| on full actual-state annotations from cut0, not an unlinked tag word or an
||| assumed prior count. This is a nontrivial admitted move, not normalization.
public export
record SmallRootPhaseEvidence where
  constructor MkSmallRootPhaseEvidence
  smallPhase : SnapshotRootPhaseStep Nat Bool Unit String (\key => Unit) %search %search
    2 3 (smallComponent True) (beforeActionOccurrence smallRootBirth)
    (smallEarlyBegin2 smallNativeExecution) (smallLateInsert3 smallNativeExecution)
  smallOriginalRun : Transitions (smallState 0) (smallState 9)
  smallOriginalTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) smallOriginalRun
  smallMovedTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) (rootPhaseTrace smallPhase)
  0 smallOriginalPhysical : smallOriginalRun = appendTransitions (beforeActionOccurrence smallRootBirth)
    (MoreTransitions
      (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution))
      (MoreTransitions
        (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions))
  0 smallOriginalInversions : rootBirthInversions 0 smallOriginalTrail = 3
  0 smallMovedInversions : rootBirthInversions 0 smallMovedTrail = 2
  0 smallPhysicalExactlyOne : rootBirthInversions 0 smallOriginalTrail = S (rootBirthInversions 0 smallMovedTrail)

||| Both routes are physically contextualized by Begin0/Finish0/Retire1/
||| Remove1. The admitted move crosses Begin2 ONLY AFTER Remove1 has freed
||| the root's key. Actual full-trace inversions change 3 -> 2 (exactly one),
||| checked successors and support preservation come from the real C14 square
||| and C18 step, and no literal state9=state6 identity is claimed.
public export
0 smallRootPhaseEvidence : SmallRootPhaseEvidence
smallRootPhaseEvidence = MkSmallRootPhaseEvidence
  (rootPhaseFromSnapshot %search %search 2 3 (smallComponent True)
    (beforeActionOccurrence smallRootBirth)
    (smallEarlyBegin2 smallNativeExecution) (smallLateInsert3 smallNativeExecution) smallRootSnapshotSquare)
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions)))))
      (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions))))
      (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions)))
      (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions))
      (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 8} %search %search (LBegin 2) LBeginTag (smallEarlyBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions)
      (AvailabilityStep (smallState 8) (Fired {before = smallState 8} {afterState = smallState 9} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallLateInsert3 smallNativeExecution)) NoTransitions
      (AvailabilityEnd (smallState 9))))))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions)))))
      (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions))))
      (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions)))
      (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions))
      (AvailabilityStep (smallState 4) (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions)
      (AvailabilityStep (smallState 5) (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) NoTransitions
      (AvailabilityEnd (smallState 6))))))))
  Refl Refl Refl Refl
