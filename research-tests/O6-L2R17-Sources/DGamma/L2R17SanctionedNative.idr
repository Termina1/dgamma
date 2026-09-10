module DGamma.L2R17SanctionedNative

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.L2R17SanctionedStates
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5UniqueRawNameInsertions
import DGamma.L2R2SmallStates
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import Data.DPair
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off


||| Four five-edge equation packets, plus initial validity. Producer-owned
||| equalities are checked once here, not re-inferred in each block field.
public export
0 sanctionedNative :
  (registryWellFormed @{fst fixtureDictionaries} @{snd fixtureDictionaries} (sanctionedState 0) = True,
   (checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LBegin 0) (sanctionedState 0) = Just (LBeginTag, sanctionedState 1),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LAdvance 0) (sanctionedState 1) = Just (LFinishTag, sanctionedState 2),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORetire 1) (sanctionedState 2) = Just (ORetireTag, sanctionedState 3),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORemove 1) (sanctionedState 3) = Just (ORemoveTag, sanctionedState 4),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (OInsert 4 Root (anchorComponent True)) (sanctionedState 4) = Just (OInsertTag, sanctionedState 5)),
   (checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LBegin 2) (sanctionedState 5) = Just (LBeginTag, sanctionedState 6),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LAdvance 2) (sanctionedState 6) = Just (LFinishTag, sanctionedState 7),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORetire 3) (sanctionedState 7) = Just (ORetireTag, sanctionedState 8),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORemove 3) (sanctionedState 8) = Just (ORemoveTag, sanctionedState 9),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (OInsert 5 Root (anchorComponent False)) (sanctionedState 9) = Just (OInsertTag, sanctionedState 10)),
   (checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LBegin 2) (sanctionedState 0) = Just (LBeginTag, sanctionedState 11),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LAdvance 2) (sanctionedState 11) = Just (LFinishTag, sanctionedState 12),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORetire 3) (sanctionedState 12) = Just (ORetireTag, sanctionedState 13),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORemove 3) (sanctionedState 13) = Just (ORemoveTag, sanctionedState 14),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (OInsert 5 Root (anchorComponent False)) (sanctionedState 14) = Just (OInsertTag, sanctionedState 15)),
   (checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LBegin 0) (sanctionedState 15) = Just (LBeginTag, sanctionedState 16),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (LAdvance 0) (sanctionedState 16) = Just (LFinishTag, sanctionedState 17),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORetire 1) (sanctionedState 17) = Just (ORetireTag, sanctionedState 18),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (ORemove 1) (sanctionedState 18) = Just (ORemoveTag, sanctionedState 19),
   checkedApplyAction @{fst fixtureDictionaries} @{snd fixtureDictionaries} (OInsert 4 Root (anchorComponent True)) (sanctionedState 19) = Just (OInsertTag, sanctionedState 20)))
sanctionedNative = (Refl, (Refl, Refl, Refl, Refl, Refl), (Refl, Refl, Refl, Refl, Refl), (Refl, Refl, Refl, Refl, Refl), (Refl, Refl, Refl, Refl, Refl))
