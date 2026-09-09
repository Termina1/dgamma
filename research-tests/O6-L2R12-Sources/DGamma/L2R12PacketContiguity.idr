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

||| GeneralCoreContiguityRestored-shaped result of the packet route. Both
||| families and whole endpoints are arbitrary; the inherited core template
||| is actor2/child5. Exact core words, count and physical placement, not
||| equality of incompatible core endpoint states, are the conclusions.
public export
record PacketContiguityResult
  (initial, oldFinal, newFinal : SystemState Nat Bool (\key => Unit) Unit String)
  (root : Nat) (component : Component Bool (\key => Unit) Unit String)
  (suffix : List (Action Nat Bool (\key => Unit) Unit String)) where
  constructor MkPacketContiguityResult
  packetOriginalRun : Transitions initial oldFinal
  packetRestoredRun : Transitions initial newFinal
  packetOriginalTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) packetOriginalRun
  packetRestoredTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) packetRestoredRun
  packetOriginalCore : LocatedExtendedCore Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) 2 packetOriginalRun
  packetRestoredCore : LocatedExtendedCore Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) 2 packetRestoredRun
  0 packetOriginValid : registryWellFormed @{fst fixtureDictionaries} @{snd fixtureDictionaries} initial = True
  0 packetRootForeign : root = 2 -> Void
  0 packetOriginalSuffix : nativeActionWord (afterCoreTrail packetOriginalCore) = OInsert root Root component :: suffix
  0 packetRestoredWord : nativeActionWord packetRestoredTrail =
    nativeActionWord (beforeCoreTrail packetOriginalCore) ++
      OInsert root Root component :: (nativeActionWord (coreTrail packetOriginalCore) ++ suffix)
  0 packetCoreWord : nativeActionWord (coreTrail packetRestoredCore) = nativeActionWord (coreTrail packetOriginalCore)
  0 packetOldCount : transitionCount (nativeCore packetOriginalCore) = 5
  0 packetNewCount : transitionCount (nativeCore packetRestoredCore) = 5
  0 packetCorePosition : transitionCount (beforeCore packetRestoredCore) = S (transitionCount (beforeCore packetOriginalCore))
  0 packetWholeEndpoints : RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) oldFinal newFinal

||| Produce a physically located extended core FROM an arbitrary native
||| packet and actual surrounding traces. Grammar is derived by assembly.
export
0 locatePacketCore :
  (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  {initial, finalState : SystemState Nat Bool (\key => Unit) Unit String} ->
  (packet : CoreNativePacket states) ->
  (before : Transitions initial (states 0)) -> (after : Transitions (states 5) finalState) ->
  (beforeTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) before) ->
  (afterTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) after) ->
  LocatedExtendedCore Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) 2
    (appendTransitions before (appendTransitions (assembledTrace (assembleCoreNative states packet)) after))
locatePacketCore states packet before after beforeTrail afterTrail =
  MkLocatedExtendedCore (states 0) (states 5) before (assembledTrace (assembleCoreNative states packet)) after
    beforeTrail (assembledTrail (assembleCoreNative states packet)) afterTrail
    (assembledActorOnly (assembleCoreNative states packet)) Refl

||| The restored prefix gains exactly its single native root edge. This is
||| structural physical count, not an assumed ordinal annotation.
export
0 packetPrefixShift : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (before : Transitions first middle) -> (step : Transition middle finalState) ->
  transitionCount (appendTransitions before (MoreTransitions step NoTransitions)) = S (transitionCount before)
packetPrefixShift NoTransitions step = Refl
packetPrefixShift (MoreTransitions head rest) step = cong S (packetPrefixShift rest step)
