module DGamma.L2R16AnchorNative

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
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Native-check SPECIFICATION TYPE. Its constructor alone does not certify
||| any edge; anchorNative will separately inhabit all twelve obligations.
public export
record AnchorNativeExecution where
  constructor MkAnchorNativeExecution
  0 anchorInitialValid : registryWellFormed @{fst fixtureDictionaries} @{snd fixtureDictionaries} (anchorState 0) = True
  0 aBegin : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (LBegin 0) (anchorState 0) = Just (LBeginTag, anchorState 1)
  0 aFinish : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (LAdvance 0) (anchorState 1) = Just (LFinishTag, anchorState 2)
  0 aRetire1 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORetire 1) (anchorState 2) = Just (ORetireTag, anchorState 3)
  0 aRemove1 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORemove 1) (anchorState 3) = Just (ORemoveTag, anchorState 4)
  0 aRetire2 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORetire 2) (anchorState 4) = Just (ORetireTag, anchorState 5)
  0 aRemove2 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORemove 2) (anchorState 5) = Just (ORemoveTag, anchorState 6)
  0 aRetire3 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORetire 3) (anchorState 6) = Just (ORetireTag, anchorState 7)
  0 aRoot4 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert 4 Root (anchorComponent True)) (anchorState 7) = Just (OInsertTag, anchorState 8)
  0 aRoot5 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert 5 Root (anchorComponent False)) (anchorState 8) = Just (OInsertTag, anchorState 9)
  0 aEarlyRoot4 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert 4 Root (anchorComponent True)) (anchorState 6) = Just (OInsertTag, anchorState 10)
  0 aLateRetire3 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (ORetire 3) (anchorState 10) = Just (ORetireTag, anchorState 11)
  0 aLateRoot5 : checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries}
    (OInsert 5 Root (anchorComponent False)) (anchorState 11) = Just (OInsertTag, anchorState 12)

||| All twelve ACTUAL checked edges and the initial registry invariant.
||| This proof inhabits the preceding record; no execution is postulated.
public export
0 anchorNative : AnchorNativeExecution
anchorNative = MkAnchorNativeExecution
  Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl Refl
