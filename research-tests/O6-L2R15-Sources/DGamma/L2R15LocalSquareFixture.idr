module DGamma.L2R15LocalSquareFixture

import Builtin
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
import DGamma.L2R15LocalShapeAssembly
import DGamma.L2R15LocalSquareProduction

%default total
%unbound_implicits off

||| Reproduce ALL twelve fixture shape TYPES, exact LOCAL6~16 and DERIVED
||| whole7~17. Eight orchestration shapes now come FROM general native
||| producers; only FOUR lifecycle shapes/payloads are reused from L2R14.
||| No old orchestration shape, LOCAL square, whole equality or endpoint
||| transport record is a construction input. This is not proof-record identity.
public export
0 fixtureLocalSquareFromNativeControls :
  (LocalSquareActionShapes contiguityState (\ordinal => contiguityState (11 + ordinal))
    3 (smallComponent True) (contiguityState 6),
   (transport : PacketWholeEndpointTransport contiguityState
      (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage **
     (lateRootState transport = contiguityState 6,
      RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries)
        (contiguityState 6) (contiguityState 16),
      RegistryExtensional Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries)
        (contiguityState 7) (contiguityState 17))))
fixtureLocalSquareFromNativeControls =
  ((localShapesFromLifecycle contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (contiguityState 6) (fst contiguityOriginalLast) (begunFiber fixtureLocalActionShapes) (finishedFiber fixtureLocalActionShapes)
    (fst (snd (oldActionShapes fixtureLocalActionShapes)), fst (snd (snd (oldActionShapes fixtureLocalActionShapes))))
    (fst (snd (newActionShapes fixtureLocalActionShapes)), fst (snd (snd (newActionShapes fixtureLocalActionShapes))))),
   ((packetWholeTransportFromLifecycleShapes contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (contiguityState 6) (fst contiguityOriginalLast) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions) (AvailabilityStep (contiguityState 6) (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions (AvailabilityEnd (contiguityState 7))) Refl (SuffixFramesRoot 4 (smallComponent False) (snd contiguityOriginalLast) (restoredEdge16 contiguityRestoredLast) Refl Refl SuffixFramesEnd) (begunFiber fixtureLocalActionShapes) (finishedFiber fixtureLocalActionShapes)
    (fst (snd (oldActionShapes fixtureLocalActionShapes)), fst (snd (snd (oldActionShapes fixtureLocalActionShapes))))
    (fst (snd (newActionShapes fixtureLocalActionShapes)), fst (snd (snd (newActionShapes fixtureLocalActionShapes))))) ** (Refl, localCoreRootSquare (packetWholeTransportFromLifecycleShapes contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (contiguityState 6) (fst contiguityOriginalLast) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions) (AvailabilityStep (contiguityState 6) (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions (AvailabilityEnd (contiguityState 7))) Refl (SuffixFramesRoot 4 (smallComponent False) (snd contiguityOriginalLast) (restoredEdge16 contiguityRestoredLast) Refl Refl SuffixFramesEnd) (begunFiber fixtureLocalActionShapes) (finishedFiber fixtureLocalActionShapes)
    (fst (snd (oldActionShapes fixtureLocalActionShapes)), fst (snd (snd (oldActionShapes fixtureLocalActionShapes))))
    (fst (snd (newActionShapes fixtureLocalActionShapes)), fst (snd (snd (newActionShapes fixtureLocalActionShapes))))),
     packetWholeEndpointsFromLocalSquare contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (packetWholeTransportFromLifecycleShapes contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (contiguityState 6) (fst contiguityOriginalLast) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions) (AvailabilityStep (contiguityState 6) (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions (AvailabilityEnd (contiguityState 7))) Refl (SuffixFramesRoot 4 (smallComponent False) (snd contiguityOriginalLast) (restoredEdge16 contiguityRestoredLast) Refl Refl SuffixFramesEnd) (begunFiber fixtureLocalActionShapes) (finishedFiber fixtureLocalActionShapes)
    (fst (snd (oldActionShapes fixtureLocalActionShapes)), fst (snd (snd (oldActionShapes fixtureLocalActionShapes))))
    (fst (snd (newActionShapes fixtureLocalActionShapes)), fst (snd (snd (newActionShapes fixtureLocalActionShapes))))))))
