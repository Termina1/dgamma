module DGamma.L2R11PhaseDecode

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R10PhaseScan
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Decode the ACTUAL event-owner classifier into its native child parent.
||| Only the parent is eliminated; Just injectivity preserves owner identity.
export
0 phaseParentDecoded : {name : Type} -> (parent : Parent name) -> (actor : name) ->
  (0 equation : phaseParentOwner parent = Just actor) -> parent = ChildOf actor
phaseParentDecoded Root actor equation = absurd equation
phaseParentDecoded (ChildOf owner) actor equation = cong ChildOf (injective equation)
