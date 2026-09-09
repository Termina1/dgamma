module DGamma.L2R14LocalSquareFixture

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

import Prelude.Num
import DGamma.L2R8ContiguityStates
import DGamma.L2R9ContiguityPackets
import DGamma.L2R9RestoredPackets
import DGamma.L2R11CorePackets

import DGamma.L2R5Extensional
import DGamma.L2R12PacketFixture
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R13PacketEndpointTransport
import DGamma.L2R14LocalShapeFixture
import DGamma.L2R14LocalSquareProduction

%default total
%unbound_implicits off

||| The ACTUAL LOCAL6~16 square and complete packet transport are FROM the
||| GENERAL per-action-shape producer; whole7~17 is then DERIVED by native S
||| suffix replay. No old fixtureLocalCoreRootSquare, whole endpoint equality
||| or PacketWholeEndpointTransport hypothesis is consumed. No split Remove.
public export
0 fixtureLocalSquareFromActionShapes :
  (transport : PacketWholeEndpointTransport contiguityState
    (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage **
    (lateRootState transport = contiguityState 6,
     RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries)
       (contiguityState 6) (contiguityState 16),
     RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries)
       (contiguityState 7) (contiguityState 17)))
fixtureLocalSquareFromActionShapes =
  ((packetWholeTransportFromActionShapes contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (contiguityState 6) (fst contiguityOriginalLast) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions) (AvailabilityStep (contiguityState 6) (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions (AvailabilityEnd (contiguityState 7))) Refl (SuffixFramesRoot 4 (smallComponent False) (snd contiguityOriginalLast) (restoredEdge16 contiguityRestoredLast) Refl Refl SuffixFramesEnd) fixtureLocalActionShapes) ** (Refl, localCoreRootSquare (packetWholeTransportFromActionShapes contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (contiguityState 6) (fst contiguityOriginalLast) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions) (AvailabilityStep (contiguityState 6) (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions (AvailabilityEnd (contiguityState 7))) Refl (SuffixFramesRoot 4 (smallComponent False) (snd contiguityOriginalLast) (restoredEdge16 contiguityRestoredLast) Refl Refl SuffixFramesEnd) fixtureLocalActionShapes),
    packetWholeEndpointsFromLocalSquare contiguityState (\ordinal => contiguityState (11 + ordinal))
      fixturePacketPassage (packetWholeTransportFromActionShapes contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (contiguityState 6) (fst contiguityOriginalLast) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions) (AvailabilityStep (contiguityState 6) (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions (AvailabilityEnd (contiguityState 7))) Refl (SuffixFramesRoot 4 (smallComponent False) (snd contiguityOriginalLast) (restoredEdge16 contiguityRestoredLast) Refl Refl SuffixFramesEnd) fixtureLocalActionShapes)))
