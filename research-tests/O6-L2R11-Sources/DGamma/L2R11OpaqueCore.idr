module DGamma.L2R11OpaqueCore

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R6Iteration
import DGamma.L2R10OrdinalData
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| OPAQUE state-family boundary: the assembler will never normalize a
||| concrete Remove. Native equations and actual source metadata are inputs
||| from independently checked public fixture packets, not grammar oracles.
||| No split8->9 equation is requested, retried, or manufactured here.
public export
record CoreNativePacket (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkCoreNativePacket
  0 insertEdge : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert 5 (ChildOf 2) (smallComponent False)) (states 0) = Just (OInsertTag, states 1)
  0 beginEdge : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (LBegin 2) (states 1) = Just (LBeginTag, states 2)
  0 finishEdge : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (LAdvance 2) (states 2) = Just (LFinishTag, states 3)
  0 retireEdge : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORetire 5) (states 3) = Just (ORetireTag, states 4)
  0 removeEdge : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORemove 5) (states 4) = Just (ORemoveTag, states 5)
  0 retireSource : lookupFiber {name = Nat} {key = Bool} {value = \key => Unit} {world = Unit} {error = String}
    @{fst fixtureDictionaries} 5 (registry (states 3)) = Just (freshFiber (smallComponent False) (ChildOf 2))
  0 removeSource : lookupFiber {name = Nat} {key = Bool} {value = \key => Unit} {world = Unit} {error = String}
    @{fst fixtureDictionaries} 5 (registry (states 4)) = Just (retireFiber (freshFiber (smallComponent False) (ChildOf 2)))

||| Simultaneously constructed native core, source-aware trail and grammar.
||| The output has exact action-word/count specifications, not endpoint-state
||| equality between original and restored cores.
public export
record CoreNativeRun (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) where
  constructor MkCoreNativeRun
  assembledTrace : Transitions (states 0) (states 5)
  assembledTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) assembledTrace
  0 assembledActorOnly : ActorLifecycleOnlyExtended (fst fixtureDictionaries) 2 assembledTrace
  0 assembledWord : nativeActionWord assembledTrail =
    [OInsert 5 (ChildOf 2) (smallComponent False), LBegin 2, LAdvance 2, ORetire 5, ORemove 5]
  0 assembledCount : transitionCount assembledTrace = 5

||| TOTAL executable assembly over OPAQUE states. Every Fired equation comes
||| from the native packet; grammar/source/action-word/count are constructed
||| simultaneously. No concrete ORemove reduction occurs in this definition.
public export
assembleCoreNative : (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  CoreNativePacket states -> CoreNativeRun states
assembleCoreNative states packet = MkCoreNativeRun
  (MoreTransitions (Fired {before = states 0} {afterState = states 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 (ChildOf 2) (smallComponent False)) OInsertTag (insertEdge packet)) (MoreTransitions (Fired {before = states 1} {afterState = states 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (beginEdge packet)) (MoreTransitions (Fired {before = states 2} {afterState = states 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishEdge packet)) (MoreTransitions (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions)))))
  (AvailabilityStep (states 0) (Fired {before = states 0} {afterState = states 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 (ChildOf 2) (smallComponent False)) OInsertTag (insertEdge packet)) (MoreTransitions (Fired {before = states 1} {afterState = states 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (beginEdge packet)) (MoreTransitions (Fired {before = states 2} {afterState = states 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishEdge packet)) (MoreTransitions (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions)))) (AvailabilityStep (states 1) (Fired {before = states 1} {afterState = states 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (beginEdge packet)) (MoreTransitions (Fired {before = states 2} {afterState = states 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishEdge packet)) (MoreTransitions (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions))) (AvailabilityStep (states 2) (Fired {before = states 2} {afterState = states 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishEdge packet)) (MoreTransitions (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions)) (AvailabilityStep (states 3) (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions) (AvailabilityStep (states 4) (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions (AvailabilityEnd (states 5)))))))
  (ExtendedYieldedRegistrationStep (Fired {before = states 0} {afterState = states 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 (ChildOf 2) (smallComponent False)) OInsertTag (insertEdge packet)) (MoreTransitions (Fired {before = states 1} {afterState = states 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (beginEdge packet)) (MoreTransitions (Fired {before = states 2} {afterState = states 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishEdge packet)) (MoreTransitions (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions)))) Refl (ExtendedLifecycleStep (Fired {before = states 1} {afterState = states 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 2) LBeginTag (beginEdge packet)) (MoreTransitions (Fired {before = states 2} {afterState = states 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishEdge packet)) (MoreTransitions (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions))) Refl Refl (ExtendedLifecycleStep (Fired {before = states 2} {afterState = states 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 2) LFinishTag (finishEdge packet)) (MoreTransitions (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions)) Refl Refl (ExtendedChildRetireStep (Fired {before = states 3} {afterState = states 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 5) ORetireTag (retireEdge packet)) (MoreTransitions (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions) 5 (freshFiber (smallComponent False) (ChildOf 2)) (retireSource packet) Refl Refl (ExtendedChildRemoveStep (Fired {before = states 4} {afterState = states 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 5) ORemoveTag (removeEdge packet)) NoTransitions 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (removeSource packet) Refl Refl ExtendedLifecycleEnd)))))
  Refl Refl
