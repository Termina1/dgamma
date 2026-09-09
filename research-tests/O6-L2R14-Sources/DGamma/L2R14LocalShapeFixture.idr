module DGamma.L2R14LocalShapeFixture

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

%default total
%unbound_implicits off

||| Discharge ALL per-action shape hypotheses on the actual fixture native
||| packets. Each Refl concerns ONLY one immediate raw registry operation;
||| no whole6~16 or7~17 snapshot is used, and no split Remove is constructed.
public export
0 fixtureLocalActionShapes : LocalSquareActionShapes contiguityState
  (\ordinal => contiguityState (11 + ordinal)) 3 (smallComponent True) (contiguityState 6)
fixtureLocalActionShapes = MkLocalSquareActionShapes
  (setFiberLifecycle (freshFiber (smallComponent False) Root) (Reloading [] id EmptyView))
  (setFiberLifecycle (freshFiber (smallComponent False) Root) (Active id EmptyView))
  (MkNativeActionShape (contiguityState 1) (insertEdge originalCorePacket) Refl,
   MkNativeActionShape (contiguityState 2) (beginEdge originalCorePacket) Refl,
   MkNativeActionShape (contiguityState 3) (finishEdge originalCorePacket) Refl,
   MkNativeActionShape (contiguityState 4) (retireEdge originalCorePacket) Refl,
   MkNativeActionShape (contiguityState 5) (removeEdge originalCorePacket) Refl)
  (MkNativeActionShape (contiguityState 12) (insertEdge restoredCorePacket) Refl,
   MkNativeActionShape (contiguityState 13) (beginEdge restoredCorePacket) Refl,
   MkNativeActionShape (contiguityState 14) (finishEdge restoredCorePacket) Refl,
   MkNativeActionShape (contiguityState 15) (retireEdge restoredCorePacket) Refl,
   MkNativeActionShape (contiguityState 16) (removeEdge restoredCorePacket) Refl)
  (MkNativeActionShape (contiguityState 11) (restoredEdge10 contiguityRestoredFirst) Refl)
  (MkNativeActionShape (contiguityState 6) (fst contiguityOriginalLast) Refl)
