module DGamma.L2R15LocalShapeAssembly

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.L2R2SmallStates
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R12PacketContiguity
import DGamma.L2R14ActionShapes
import DGamma.L2R15PacketControlShapes
import DGamma.L2R15NativeInsertShape
import DGamma.L2R15NativeControlShapes
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| General shape assembly now requires only FOUR explicit lifecycle
||| shapes sharing begun/finished payloads. All EIGHT orchestration shapes
||| are PRODUCED from arbitrary native packets and actual early/late roots.
||| This is not an unconditional LocalSquareActionShapes producer: the shared
||| Begin/Finish payload transport is the exact remaining semantic premise.
public export
0 localShapesFromLifecycle :
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  {initial, oldFinal, newFinal : SystemState Nat Bool (\key => Unit) Unit String} ->
  (passage : PacketPassage oldStates newStates initial oldFinal newFinal) ->
  (lateRootState : SystemState Nat Bool (\key => Unit) Unit String) ->
  (0 lateChecked : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert (passageRoot passage) Root (passageComponent passage)) (oldStates 5) = Just (OInsertTag, lateRootState)) ->
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
  LocalSquareActionShapes oldStates newStates (passageRoot passage) (passageComponent passage) lateRootState
localShapesFromLifecycle oldStates newStates passage lateRootState lateChecked begun finished oldLife newLife =
  MkLocalSquareActionShapes begun finished
    (fst (nativeCoreControlShapes oldStates (passageOldPacket passage)), fst oldLife, snd oldLife,
     fst (snd (nativeCoreControlShapes oldStates (passageOldPacket passage))),
     snd (snd (nativeCoreControlShapes oldStates (passageOldPacket passage))))
    (fst (nativeCoreControlShapes newStates (passageNewPacket passage)), fst newLife, snd newLife,
     fst (snd (nativeCoreControlShapes newStates (passageNewPacket passage))),
     snd (snd (nativeCoreControlShapes newStates (passageNewPacket passage))))
    (nativeInsertShape (fst fixtureDictionaries) (snd fixtureDictionaries) (passageRoot passage) Root
      (passageComponent passage) (oldStates 0) (newStates 0) OInsertTag (passageEarlyRoot passage))
    (nativeInsertShape (fst fixtureDictionaries) (snd fixtureDictionaries) (passageRoot passage) Root
      (passageComponent passage) (oldStates 5) lateRootState OInsertTag lateChecked)
