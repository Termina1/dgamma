module DGamma.L2R16AnchorTrace

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Both words consist ONLY of the freshly certified native edges. The
||| Boolean selects the authentic Retire/Root order, not a guessed endpoint.
public export
anchorTrace : (crossed : Bool) ->
  Transitions (anchorState 0) (anchorState (if crossed then 12 else 9))
anchorTrace False =
  MoreTransitions (Fired {before = anchorState 0} {afterState = anchorState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (aBegin anchorNative)) (MoreTransitions (Fired {before = anchorState 1} {afterState = anchorState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (aFinish anchorNative)) (MoreTransitions (Fired {before = anchorState 2} {afterState = anchorState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (aRetire1 anchorNative)) (MoreTransitions (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (MoreTransitions (Fired {before = anchorState 6} {afterState = anchorState 7} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 3) ORetireTag (aRetire3 anchorNative)) (MoreTransitions (Fired {before = anchorState 7} {afterState = anchorState 8} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (anchorComponent True)) OInsertTag (aRoot4 anchorNative)) (MoreTransitions (Fired {before = anchorState 8} {afterState = anchorState 9} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aRoot5 anchorNative)) (NoTransitions)))))))))
anchorTrace True =
  MoreTransitions (Fired {before = anchorState 0} {afterState = anchorState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (aBegin anchorNative)) (MoreTransitions (Fired {before = anchorState 1} {afterState = anchorState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (aFinish anchorNative)) (MoreTransitions (Fired {before = anchorState 2} {afterState = anchorState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (aRetire1 anchorNative)) (MoreTransitions (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (MoreTransitions (Fired {before = anchorState 6} {afterState = anchorState 10} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 4 Root (anchorComponent True)) OInsertTag (aEarlyRoot4 anchorNative)) (MoreTransitions (Fired {before = anchorState 10} {afterState = anchorState 11} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 3) ORetireTag (aLateRetire3 anchorNative)) (MoreTransitions (Fired {before = anchorState 11} {afterState = anchorState 12} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aLateRoot5 anchorNative)) (NoTransitions)))))))))
