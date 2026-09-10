module DGamma.L2R15LocalSquareProduction

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP4RuntimeBindings
import DGamma.L2R2SmallStates
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R12PacketContiguity
import DGamma.L2R14ActionShapes
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R13PacketEndpointTransport
import DGamma.L2R14LocalSquareProduction
import DGamma.L2R15LocalShapeAssembly
import DGamma.L2R15PacketControlShapes
import DGamma.L2R15NativeInsertShape
import DGamma.L2R15NativeControlShapes
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| General LOCAL square and packet endpoint transport with only FOUR
||| remaining raw lifecycle shape premises. All eight orchestration shapes
||| are generated from native registry definitions, then L2R14's actual
||| operation commutation/determinism proves the LOCAL square. No LOCAL or
||| WHOLE endpoint relation is supplied. This is still CONDITIONAL on common
||| Begin/Finish payloads and the inherited Root/Retire native suffix frames.
public export
0 packetWholeTransportFromLifecycleShapes :
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  {initial, oldFinal, newFinal : SystemState Nat Bool (\key => Unit) Unit String} ->
  (passage : PacketPassage oldStates newStates initial oldFinal newFinal) ->
  (lateRootState : SystemState Nat Bool (\key => Unit) Unit String) ->
  (0 nativeLateRoot : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert (passageRoot passage) Root (passageComponent passage)) (oldStates 5) = Just (OInsertTag, lateRootState)) ->
  (oldRemainder : Transitions lateRootState oldFinal) ->
  (oldRemainderTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) oldRemainder) ->
  (0 nativeSuffixSplit : MoreTransitions
    (Fired {before = oldStates 5} {afterState = lateRootState} (fst fixtureDictionaries) (snd fixtureDictionaries)
      (OInsert (passageRoot passage) Root (passageComponent passage)) OInsertTag nativeLateRoot)
    oldRemainder = passageOldSuffix passage) ->
  (0 frames : NativeSuffixFrames (fst fixtureDictionaries) (snd fixtureDictionaries)
    oldRemainder (passageNewSuffix passage)) ->
  (begun, finished : Fiber Nat Bool (\key => Unit) Unit String) ->
  (oldLife : (NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LBegin 2) (oldStates 1) LBeginTag
      (MkRuntimeSnapshot (worldState (oldStates 1)) (replaceEntries @{fst fixtureDictionaries} 2 begun (bindings (registry (oldStates 1))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LAdvance 2) (oldStates 2) LFinishTag
      (MkRuntimeSnapshot (worldState (oldStates 2)) (replaceEntries @{fst fixtureDictionaries} 2 finished (bindings (registry (oldStates 2))))))) ->
  (newLife : (NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LBegin 2) (newStates 1) LBeginTag
      (MkRuntimeSnapshot (worldState (newStates 1)) (replaceEntries @{fst fixtureDictionaries} 2 begun (bindings (registry (newStates 1))))),
     NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
      (LAdvance 2) (newStates 2) LFinishTag
      (MkRuntimeSnapshot (worldState (newStates 2)) (replaceEntries @{fst fixtureDictionaries} 2 finished (bindings (registry (newStates 2))))))) ->
  PacketWholeEndpointTransport oldStates newStates passage
packetWholeTransportFromLifecycleShapes oldStates newStates passage lateRootState nativeLateRoot
  oldRemainder oldRemainderTrail nativeSuffixSplit frames begun finished oldLife newLife =
  packetWholeTransportFromActionShapes oldStates newStates passage lateRootState nativeLateRoot
    oldRemainder oldRemainderTrail nativeSuffixSplit frames
    (localShapesFromLifecycle oldStates newStates passage lateRootState nativeLateRoot begun finished oldLife newLife)
