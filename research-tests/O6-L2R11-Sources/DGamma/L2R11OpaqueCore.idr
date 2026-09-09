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
