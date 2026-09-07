module DGamma.CP5RankedEarlyApplicabilitySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5RankedTraceSelectionSpike
import Data.Maybe
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An actual checked early application with the EXACT original action/tag.
||| Its destination is produced by execution, never supplied by a caller.
public export
record CheckedEarlyApplication
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (before : SystemState name key value world error)
  (action : Action name key value world error) (tag : RuleTag) where
  constructor MkCheckedEarlyApplication
  earlyApplicationFinal : SystemState name key value world error
  0 earlyApplicationChecked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, earlyApplicationFinal)
