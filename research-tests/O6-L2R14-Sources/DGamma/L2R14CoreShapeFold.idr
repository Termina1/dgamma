module DGamma.L2R14CoreShapeFold

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

import DGamma.L2R14ActionShapes

%default total
%unbound_implicits off

||| Fold FIVE authentic per-action shapes by native packet determinism.
||| Fresh child insertion/retirement/deletion cancel by registry algebra;
||| the two actor replacement payloads and initial source remain arbitrary.
||| No LOCAL endpoint relation or alternate native Remove is an input.
export
0 coreNativeSnapshotFromShapes :
  (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  (packet : CoreNativePacket states) ->
  (begun, finished : Fiber Nat Bool (\key => Unit) Unit String) ->
  (insertShape : NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (OInsert 5 (ChildOf 2) (smallComponent False)) (states 0) OInsertTag
    (MkRuntimeSnapshot (worldState (states 0)) (Bind 5 (freshFiber (smallComponent False) (ChildOf 2)) :: bindings (registry (states 0))))) ->
  (beginShape : NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (LBegin 2) (states 1) LBeginTag
    (MkRuntimeSnapshot (worldState (states 1)) (replaceEntries @{fst fixtureDictionaries} 2 begun (bindings (registry (states 1)))))) ->
  (finishShape : NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (LAdvance 2) (states 2) LFinishTag
    (MkRuntimeSnapshot (worldState (states 2)) (replaceEntries @{fst fixtureDictionaries} 2 finished (bindings (registry (states 2)))))) ->
  (retireShape : NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (ORetire 5) (states 3) ORetireTag
    (MkRuntimeSnapshot (worldState (states 3)) (replaceEntries @{fst fixtureDictionaries} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (bindings (registry (states 3)))))) ->
  (removeShape : NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (ORemove 5) (states 4) ORemoveTag
    (MkRuntimeSnapshot (worldState (states 4)) (deleteEntries @{fst fixtureDictionaries} 5 (bindings (registry (states 4)))))) ->
  runtimeSnapshot (states 5) = MkRuntimeSnapshot (worldState (states 0))
    (replaceEntries @{fst fixtureDictionaries} 2 finished
      (replaceEntries @{fst fixtureDictionaries} 2 begun (bindings (registry (states 0)))))
coreNativeSnapshotFromShapes states packet begun finished insertShape beginShape finishShape retireShape removeShape =
  trans (trans (nativeActionShapeSnapshot (states 5) (removeEdge packet) removeShape) (cong (\view => MkRuntimeSnapshot (snapshotWorld view) (deleteEntries @{fst fixtureDictionaries} 5 (snapshotBindings view))) (trans (nativeActionShapeSnapshot (states 4) (retireEdge packet) retireShape) (cong (\view => MkRuntimeSnapshot (snapshotWorld view) (replaceEntries @{fst fixtureDictionaries} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (snapshotBindings view))) (trans (nativeActionShapeSnapshot (states 3) (finishEdge packet) finishShape) (cong (\view => MkRuntimeSnapshot (snapshotWorld view) (replaceEntries @{fst fixtureDictionaries} 2 finished (snapshotBindings view))) (trans (nativeActionShapeSnapshot (states 2) (beginEdge packet) beginShape) (cong (\view => MkRuntimeSnapshot (snapshotWorld view) (replaceEntries @{fst fixtureDictionaries} 2 begun (snapshotBindings view))) (nativeActionShapeSnapshot (states 1) (insertEdge packet) insertShape)))))))))
    (cong (MkRuntimeSnapshot (worldState (states 0)))
      (localChildInsertRetireDelete (freshFiber (smallComponent False) (ChildOf 2)) begun finished
        (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (bindings (registry (states 0)))))
