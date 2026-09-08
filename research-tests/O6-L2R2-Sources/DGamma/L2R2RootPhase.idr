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
