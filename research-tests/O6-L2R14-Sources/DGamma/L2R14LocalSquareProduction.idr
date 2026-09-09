module DGamma.L2R14LocalSquareProduction

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

import DGamma.L2R14CoreShapeFold
import DGamma.L2R5Extensional
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R13PacketEndpointTransport

%default total
%unbound_implicits off

||| PRODUCE PacketWholeEndpointTransport's LOCAL square from raw per-action
||| shapes, original/restored packet determinism and fresh-head replacement
||| commutation. Both five-edge cores are folded separately (five packets
||| each). No whole or LOCAL endpoint relation is supplied by the caller.
||| Raw per-action state-shape premises are general hypotheses, discharged
||| only on the fixture; suffix kinds remain the inherited Root/Retire scope.
export
0 packetWholeTransportFromActionShapes :
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  {initial, oldFinal, newFinal : SystemState Nat Bool (\key => Unit) Unit String} ->
  (passage : PacketPassage oldStates newStates initial oldFinal newFinal) ->
  (lateRootState : SystemState Nat Bool (\key => Unit) Unit String) ->
  (0 nativeLateRoot : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert (passageRoot passage) Root (passageComponent passage)) (oldStates 5) = Just (OInsertTag, lateRootState)) ->
  (oldRemainder : Transitions lateRootState oldFinal) ->
  (oldRemainderTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) oldRemainder) ->
  (0 nativeSuffixSplit : MoreTransitions
    (Fired {before = oldStates 5} {afterState = lateRootState} (fst fixtureDictionaries) (snd fixtureDictionaries)
      (OInsert (passageRoot passage) Root (passageComponent passage)) OInsertTag nativeLateRoot)
    oldRemainder = passageOldSuffix passage) ->
  (0 frames : NativeSuffixFrames (fst fixtureDictionaries) (snd fixtureDictionaries)
    oldRemainder (passageNewSuffix passage)) ->
  (shapes : LocalSquareActionShapes oldStates newStates (passageRoot passage) (passageComponent passage) lateRootState) ->
  PacketWholeEndpointTransport oldStates newStates passage
packetWholeTransportFromActionShapes oldStates newStates passage lateRootState nativeLateRoot
  oldRemainder oldRemainderTrail nativeSuffixSplit frames shapes =
  MkPacketWholeEndpointTransport lateRootState nativeLateRoot oldRemainder oldRemainderTrail nativeSuffixSplit
    (snapshotIntoExtensional (fst fixtureDictionaries) lateRootState (newStates 5)
      (trans (trans (nativeActionShapeSnapshot lateRootState nativeLateRoot (lateRootShape shapes)) (cong (\view => MkRuntimeSnapshot (snapshotWorld view) (Bind (passageRoot passage) (freshFiber (passageComponent passage) Root) :: snapshotBindings view)) (coreNativeSnapshotFromShapes oldStates (passageOldPacket passage) (begunFiber shapes) (finishedFiber shapes) (fst (oldActionShapes shapes)) (fst (snd (oldActionShapes shapes))) (fst (snd (snd (oldActionShapes shapes)))) (fst (snd (snd (snd (oldActionShapes shapes))))) (snd (snd (snd (snd (oldActionShapes shapes))))))))
        (trans (cong (MkRuntimeSnapshot (worldState (oldStates 0))) (sym (trans (cong (replaceEntries @{fst fixtureDictionaries} 2 (finishedFiber shapes)) (localReplaceFreshHead (fst fixtureDictionaries) 2 (passageRoot passage) (begunFiber shapes) (freshFiber (passageComponent passage) Root) (bindings (registry (oldStates 0))) (\same => passageForeign passage (sym same)) (decEq @{fst fixtureDictionaries} 2 (passageRoot passage)) Refl)) (localReplaceFreshHead (fst fixtureDictionaries) 2 (passageRoot passage) (finishedFiber shapes) (freshFiber (passageComponent passage) Root) (replaceEntries @{fst fixtureDictionaries} 2 (begunFiber shapes) (bindings (registry (oldStates 0)))) (\same => passageForeign passage (sym same)) (decEq @{fst fixtureDictionaries} 2 (passageRoot passage)) Refl))))
          (sym (trans (coreNativeSnapshotFromShapes newStates (passageNewPacket passage) (begunFiber shapes) (finishedFiber shapes) (fst (newActionShapes shapes)) (fst (snd (newActionShapes shapes))) (fst (snd (snd (newActionShapes shapes)))) (fst (snd (snd (snd (newActionShapes shapes))))) (snd (snd (snd (snd (newActionShapes shapes)))))) (cong (\view => MkRuntimeSnapshot (snapshotWorld view) (replaceEntries @{fst fixtureDictionaries} 2 (finishedFiber shapes) (replaceEntries @{fst fixtureDictionaries} 2 (begunFiber shapes) (snapshotBindings view)))) (nativeActionShapeSnapshot (newStates 0) (passageEarlyRoot passage) (earlyRootShape shapes))))))))
    frames
