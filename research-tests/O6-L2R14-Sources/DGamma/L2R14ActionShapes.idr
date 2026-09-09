module DGamma.L2R14ActionShapes

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R12PacketContiguity
import DGamma.L2R14LocalOperations
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| A single authentic native edge to a raw per-action snapshot shape.
||| No equality between independent registry representation proofs is needed.
||| Record declaration alone is not a producer of these native shape premises.
public export
record NativeActionShape
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (source : SystemState name key value world error) (tag : RuleTag)
  (0 expected : RuntimeSnapshot name key world error value) where
  constructor MkNativeActionShape
  shapeTarget : SystemState name key value world error
  0 shapeChecked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (tag, shapeTarget)
  0 shapeSnapshot : runtimeSnapshot shapeTarget = expected

||| Native determinism transports a raw operation shape to the ACTUAL
||| packet target. No target/source registry proof-record equality is assumed.
export
0 nativeActionShapeSnapshot : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {action : Action name key value world error} ->
  {source : SystemState name key value world error} -> {tag : RuleTag} ->
  {expected : RuntimeSnapshot name key world error value} ->
  (actual : SystemState name key value world error) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} action source = Just (tag, actual)) ->
  (shape : NativeActionShape name key world error value nameEq keyEq action source tag expected) ->
  runtimeSnapshot actual = expected
nativeActionShapeSnapshot actual original shape =
  trans (cong runtimeSnapshot (cong snd (injective (trans (sym original) (shapeChecked shape)))))
    (shapeSnapshot shape)

||| EXPLICIT authorized per-action raw shapes, not a LOCAL/WHOLE endpoint
||| equation. Each core side has FIVE one-edge native shape observations;
||| early/late root observations are separate. Payloads remain runtime data.
||| Raw per-action state-shape premises are general hypotheses, discharged
||| only on the fixture. NativeActionShape does not manufacture these edges.
public export
record LocalSquareActionShapes
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String)
  (root : Nat) (component : Component Bool (\key => Unit) Unit String)
  (lateRootState : SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkLocalSquareActionShapes
  begunFiber : Fiber Nat Bool (\key => Unit) Unit String
  finishedFiber : Fiber Nat Bool (\key => Unit) Unit String
  oldActionShapes :
    (NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (OInsert 5 (ChildOf 2) (smallComponent False)) (oldStates 0) OInsertTag
      (MkRuntimeSnapshot (worldState (oldStates 0)) (Bind 5 (freshFiber (smallComponent False) (ChildOf 2)) :: bindings (registry (oldStates 0)))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LBegin 2) (oldStates 1) LBeginTag
      (MkRuntimeSnapshot (worldState (oldStates 1)) (replaceEntries @{fst fixtureDictionaries} 2 begunFiber (bindings (registry (oldStates 1))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LAdvance 2) (oldStates 2) LFinishTag
      (MkRuntimeSnapshot (worldState (oldStates 2)) (replaceEntries @{fst fixtureDictionaries} 2 finishedFiber (bindings (registry (oldStates 2))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (ORetire 5) (oldStates 3) ORetireTag
      (MkRuntimeSnapshot (worldState (oldStates 3)) (replaceEntries @{fst fixtureDictionaries} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (bindings (registry (oldStates 3))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (ORemove 5) (oldStates 4) ORemoveTag
      (MkRuntimeSnapshot (worldState (oldStates 4)) (deleteEntries @{fst fixtureDictionaries} 5 (bindings (registry (oldStates 4))))))
  newActionShapes :
    (NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (OInsert 5 (ChildOf 2) (smallComponent False)) (newStates 0) OInsertTag
      (MkRuntimeSnapshot (worldState (newStates 0)) (Bind 5 (freshFiber (smallComponent False) (ChildOf 2)) :: bindings (registry (newStates 0)))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LBegin 2) (newStates 1) LBeginTag
      (MkRuntimeSnapshot (worldState (newStates 1)) (replaceEntries @{fst fixtureDictionaries} 2 begunFiber (bindings (registry (newStates 1))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LAdvance 2) (newStates 2) LFinishTag
      (MkRuntimeSnapshot (worldState (newStates 2)) (replaceEntries @{fst fixtureDictionaries} 2 finishedFiber (bindings (registry (newStates 2))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (ORetire 5) (newStates 3) ORetireTag
      (MkRuntimeSnapshot (worldState (newStates 3)) (replaceEntries @{fst fixtureDictionaries} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (bindings (registry (newStates 3))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (ORemove 5) (newStates 4) ORemoveTag
      (MkRuntimeSnapshot (worldState (newStates 4)) (deleteEntries @{fst fixtureDictionaries} 5 (bindings (registry (newStates 4))))))
  earlyRootShape : NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (OInsert root Root component) (oldStates 0) OInsertTag
      (MkRuntimeSnapshot (worldState (oldStates 0)) (Bind root (freshFiber component Root) :: bindings (registry (oldStates 0))))
  lateRootShape : NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (OInsert root Root component) (oldStates 5) OInsertTag
      (MkRuntimeSnapshot (worldState (oldStates 5)) (Bind root (freshFiber component Root) :: bindings (registry (oldStates 5))))
