module DGamma.L2R13PacketEndpointTransport

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5Extensional
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R12PacketContiguity
import DGamma.L2R13NativeSuffixFrames
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| Arbitrary-family WHOLE-endpoint transport hypotheses, per supervisor C
||| ruling. The passage owns both actual native per-edge core packets. This
||| record owns the native late-root/suffix decomposition and LOCAL square;
||| there is NO whole endpoint-equivalence field.
||| The five-edge core/root LOCAL square is an explicit justified hypothesis,
||| not derived from per-action swaps. Suffix frame kinds are Root/Retire.
public export
record PacketWholeEndpointTransport
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String)
  {initial, oldFinal, newFinal : SystemState Nat Bool (\key => Unit) Unit String}
  (passage : PacketPassage oldStates newStates initial oldFinal newFinal) where
  constructor MkPacketWholeEndpointTransport
  lateRootState : SystemState Nat Bool (\key => Unit) Unit String
  0 nativeLateRoot : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert (passageRoot passage) Root (passageComponent passage)) (oldStates 5) = Just (OInsertTag, lateRootState)
  oldRemainder : Transitions lateRootState oldFinal
  oldRemainderTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) oldRemainder
  0 nativeSuffixSplit : MoreTransitions
    (Fired {before = oldStates 5} {afterState = lateRootState} (fst fixtureDictionaries) (snd fixtureDictionaries)
      (OInsert (passageRoot passage) Root (passageComponent passage)) OInsertTag nativeLateRoot)
    oldRemainder = passageOldSuffix passage
  0 localCoreRootSquare : RegistryExtensional Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) lateRootState (newStates 5)
  0 suffixNativeFrames : NativeSuffixFrames (fst fixtureDictionaries) (snd fixtureDictionaries)
    oldRemainder (passageNewSuffix passage)

||| WHOLE endpoints derived from the LOCAL core/root square and native
||| per-edge suffix transport. Works over arbitrary packet state families and
||| any finite Root/Retire suffix; neither whole endpoint is assumed equal.
export
0 packetWholeEndpointsFromLocalSquare :
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  {initial, oldFinal, newFinal : SystemState Nat Bool (\key => Unit) Unit String} ->
  (passage : PacketPassage oldStates newStates initial oldFinal newFinal) ->
  PacketWholeEndpointTransport oldStates newStates passage ->
  RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) oldFinal newFinal
packetWholeEndpointsFromLocalSquare oldStates newStates passage hypotheses =
  nativeSuffixEndpoints (fst fixtureDictionaries) (snd fixtureDictionaries)
    (suffixNativeFrames hypotheses) (localCoreRootSquare hypotheses)
