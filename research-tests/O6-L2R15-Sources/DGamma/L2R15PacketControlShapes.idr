module DGamma.L2R15PacketControlShapes

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.L2R2SmallStates
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R14ActionShapes
import DGamma.L2R15NativeInsertShape
import DGamma.L2R15NativeControlShapes
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| For ANY state-family packet, produce all THREE native child control
||| shapes from the registry definitions. Only three native edges per call;
||| no fixture shape, whole snapshot equality or extra freshness is supplied.
export
0 nativeCoreControlShapes :
  (states : Nat -> SystemState Nat Bool (\key => Unit) Unit String) ->
  (packet : CoreNativePacket states) ->
  (NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (OInsert 5 (ChildOf 2) (smallComponent False)) (states 0) OInsertTag
    (MkRuntimeSnapshot (worldState (states 0)) (Bind 5 (freshFiber (smallComponent False) (ChildOf 2)) :: bindings (registry (states 0)))),
   NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (ORetire 5) (states 3) ORetireTag
    (MkRuntimeSnapshot (worldState (states 3)) (replaceEntries @{fst fixtureDictionaries} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) (bindings (registry (states 3))))),
   NativeActionShape Nat Bool Unit String (\key => Unit) (fst fixtureDictionaries) (snd fixtureDictionaries)
    (ORemove 5) (states 4) ORemoveTag
    (MkRuntimeSnapshot (worldState (states 4)) (deleteEntries @{fst fixtureDictionaries} 5 (bindings (registry (states 4))))))
nativeCoreControlShapes states packet =
  (nativeInsertShape (fst fixtureDictionaries) (snd fixtureDictionaries) 5 (ChildOf 2) (smallComponent False)
     (states 0) (states 1) OInsertTag (insertEdge packet),
   nativeRetireShape (fst fixtureDictionaries) (snd fixtureDictionaries) 5 (freshFiber (smallComponent False) (ChildOf 2))
     (states 3) (states 4) ORetireTag (retireSource packet) (retireEdge packet),
   nativeRemoveShape (fst fixtureDictionaries) (snd fixtureDictionaries) 5 (states 4) (states 5) ORemoveTag (removeEdge packet))
