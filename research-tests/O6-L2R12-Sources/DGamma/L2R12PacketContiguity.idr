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
