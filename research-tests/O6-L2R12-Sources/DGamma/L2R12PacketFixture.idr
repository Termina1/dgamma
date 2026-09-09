module DGamma.L2R12PacketFixture

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R5Extensional
import DGamma.L2R6Iteration
import DGamma.L2R8ContiguityStates
import DGamma.L2R8NativeWords
import DGamma.L2R8CoreContract
import DGamma.L2R9ContiguityPackets
import DGamma.L2R9RestoredPackets
import DGamma.L2R9ContiguityEndpoints
import DGamma.L2R9CoreRestoration
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R11CorePackets
import DGamma.L2R12PacketContiguity
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| Actual old/new passage packets instantiate the ARBITRARY-family input.
||| Existing native edge packets supply every checked equation. No split
||| path and no whole endpoint relation is smuggled into this input record.
public export
fixturePacketPassage : PacketPassage contiguityState (\ordinal => contiguityState (11 + ordinal))
  (smallState 0) (contiguityState 7) (contiguityState 17)
fixturePacketPassage = MkPacketPassage originalCorePacket restoredCorePacket
  (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))))
  (AvailabilityStep (smallState 0) (Fired {before = smallState 0} {afterState = smallState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))) (AvailabilityStep (smallState 1) (Fired {before = smallState 1} {afterState = smallState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) (AvailabilityStep (smallState 2) (Fired {before = smallState 2} {afterState = smallState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions) (AvailabilityStep (smallState 3) (Fired {before = smallState 3} {afterState = smallState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions (AvailabilityEnd (smallState 4))))))
  3 (smallComponent True) (restoredEdge10 contiguityRestoredFirst)
  (MoreTransitions (Fired {before = contiguityState 5} {afterState = contiguityState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 3 Root (smallComponent True)) OInsertTag (fst contiguityOriginalLast)) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions))
  (AvailabilityStep (contiguityState 5) (Fired {before = contiguityState 5} {afterState = contiguityState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 3 Root (smallComponent True)) OInsertTag (fst contiguityOriginalLast)) (MoreTransitions (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions) (AvailabilityStep (contiguityState 6) (Fired {before = contiguityState 6} {afterState = contiguityState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (snd contiguityOriginalLast)) NoTransitions (AvailabilityEnd (contiguityState 7))))
  (MoreTransitions (Fired {before = contiguityState 16} {afterState = contiguityState 17} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (restoredEdge16 contiguityRestoredLast)) NoTransitions)
  (AvailabilityStep (contiguityState 16) (Fired {before = contiguityState 16} {afterState = contiguityState 17} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (smallComponent False)) OInsertTag (restoredEdge16 contiguityRestoredLast)) NoTransitions (AvailabilityEnd (contiguityState 17)))
  [OInsert 4 Root (smallComponent False)] Refl Refl
  (smallSourceValid smallNativeExecution)
  (\same => SIsNotZ {x = 0} (cong pred (cong pred same)))
