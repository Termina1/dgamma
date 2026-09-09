module DGamma.L2R12AlignedCut

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R10MoveCutObservation
import DGamma.L2R11LocatedCut
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact source/action locator WITH the authentic checked equation at the
||| explicitly named dictionaries. This avoids identifying unrelated DecEq
||| values from an unaligned Transition. Alignment is an explicit premise.
public export
record AlignedSourceAction
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (source : SystemState name key value world error)
  (action : Action name key value world error) (ordinal : Nat) where
  constructor MkAlignedSourceAction
  edgeTarget : SystemState name key value world error
  edgeTag : RuleTag
  0 edgeChecked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (edgeTag, edgeTarget)
  edgeOccurrence : LocatedActionOccurrence action trace
  0 edgeOrdinal : locatedActionOrdinal edgeOccurrence = ordinal
  0 edgeBefore : actionBeforeState edgeOccurrence = source
  0 edgeAfter : actionAfterState edgeOccurrence = edgeTarget
