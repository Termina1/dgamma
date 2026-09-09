module DGamma.L2R12PacketContiguity

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.L2R2SmallStates
import DGamma.L2R5Extensional
import DGamma.L2R6Iteration
import DGamma.L2R8NativeWords
import DGamma.L2R8CoreContract
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| GENUINELY arbitrary state-family theorem: two native packets produce
||| exactly equal extended-core action words and equal physical count5.
||| No whole-endpoint relation follows from these core packets alone.
export
0 packetCoreWords :
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  (oldPacket : CoreNativePacket oldStates) -> (newPacket : CoreNativePacket newStates) ->
  (nativeActionWord (assembledTrail (assembleCoreNative newStates newPacket)) =
    nativeActionWord (assembledTrail (assembleCoreNative oldStates oldPacket)),
   transitionCount (assembledTrace (assembleCoreNative oldStates oldPacket)) = 5,
   transitionCount (assembledTrace (assembleCoreNative newStates newPacket)) = 5)
packetCoreWords oldStates newStates oldPacket newPacket =
  (trans (assembledWord (assembleCoreNative newStates newPacket))
    (sym (assembledWord (assembleCoreNative oldStates oldPacket))),
   assembledCount (assembleCoreNative oldStates oldPacket),
   assembledCount (assembleCoreNative newStates newPacket))

||| Native passage INPUT over arbitrary original/restored state families.
||| Authentic prefix, root edge and suffix observations locate the packets.
||| Intentionally NO whole-endpoint equivalence field: that is the separately
||| named open native frame/square residue of the conditional consumer.
public export
record PacketPassage
  (oldStates, newStates : Nat -> SystemState Nat Bool (\key => Unit) Unit String)
  (initial, oldFinal, newFinal : SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkPacketPassage
  passageOldPacket : CoreNativePacket oldStates
  passageNewPacket : CoreNativePacket newStates
  passagePrefix : Transitions initial (oldStates 0)
  passagePrefixTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) passagePrefix
  passageRoot : Nat
  passageComponent : Component Bool (\key => Unit) Unit String
  0 passageEarlyRoot : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert passageRoot Root passageComponent) (oldStates 0) = Just (OInsertTag, newStates 0)
  passageOldSuffix : Transitions (oldStates 5) oldFinal
  passageOldSuffixTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) passageOldSuffix
  passageNewSuffix : Transitions (newStates 5) newFinal
  passageNewSuffixTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) passageNewSuffix
  passageSuffixWord : List (Action Nat Bool (\key => Unit) Unit String)
  0 passageOldAfterWord : nativeActionWord passageOldSuffixTrail =
    OInsert passageRoot Root passageComponent :: passageSuffixWord
  0 passageNewAfterWord : nativeActionWord passageNewSuffixTrail = passageSuffixWord
  0 passageSourceValid : registryWellFormed @{fst fixtureDictionaries} @{snd fixtureDictionaries} initial = True
  0 passageForeign : passageRoot = 2 -> Void
