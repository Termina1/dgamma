module DGamma.CP5O19CommutedDomainSpike

import DGamma.Core
import DGamma.Coeffects
import DGamma.Unified
import Data.Maybe

%default total
%unbound_implicits off

||| Partial commutation preserves DEFINEDNESS, not just successful values.
||| This algebraic fact is not a checked control/tag applicability theorem.
export
0 o19RelatedDefined :
  {state : Type} -> {rel : state -> state -> Type} ->
  {left, right : Maybe state} ->
  PartialRelated state rel left right -> (isJust left = isJust right)
o19RelatedDefined PartialUndefined = Refl
o19RelatedDefined (PartialDefined related) = Refl
