module DGamma.L2R4AnchorDecrease

import DGamma.L2R4AnchorMeasure
import Data.List
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Adjacent foreign lifecycle/root exchange decreases the fixed-anchor
||| measure by EXACTLY one, with ANY historical context and ANY suffix.
||| One observed name decision; no suffix-root cost changes because roots do
||| not reset history. Native legality/valid anchor assignment is separate.
export
0 anchorSwapObserved :
  {name : Type} -> (nameEq : DecEq name) -> (actor, root : name) ->
  (anchor : Maybe Nat) -> (history, back : List (AnchorEvent name)) ->
  (0 distinct : Not (actor = root)) ->
  (decision : Dec (actor = root)) -> (0 exact : decEq @{nameEq} actor root = decision) ->
  anchorInversions nameEq history (AnchorLife actor :: AnchorBirth root anchor :: back) =
    S (anchorInversions nameEq history (AnchorBirth root anchor :: AnchorLife actor :: back))
anchorSwapObserved nameEq actor root anchor history back distinct (Yes same) exact = void (distinct same)
anchorSwapObserved nameEq actor root anchor history back distinct (No different) exact = rewrite exact in Refl
