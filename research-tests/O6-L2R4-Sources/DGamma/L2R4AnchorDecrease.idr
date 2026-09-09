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

||| Every possible prefix event preserves a suffix's exact-one difference.
||| Births add the same historical charge on both sides; release/lifecycle/
||| other events pass the SAME transformed history to both continuations.
export
0 anchorStepPreservesOne :
  {name : Type} -> (nameEq : DecEq name) -> (event : AnchorEvent name) ->
  (left, right : List (AnchorEvent name) -> Nat) ->
  (0 same : (history : List (AnchorEvent name)) -> left history = S (right history)) ->
  (history : List (AnchorEvent name)) ->
  anchorMeasureStep nameEq event left history = S (anchorMeasureStep nameEq event right history)
anchorStepPreservesOne nameEq (AnchorBirth root anchor) left right same history =
  trans (cong (anchorHistoryCount nameEq root anchor history +) (same history))
    (sym (plusSuccRightSucc (anchorHistoryCount nameEq root anchor history) (right history)))
anchorStepPreservesOne nameEq (AnchorLife actor) left right same history = same (AnchorLife actor :: history)
anchorStepPreservesOne nameEq (AnchorRelease marker) left right same history = same (AnchorRelease marker :: history)
anchorStepPreservesOne nameEq AnchorOther left right same history = same (AnchorOther :: history)

||| General exact-one decrease for a fixed-anchor foreign lifecycle/root
||| adjacent swap under ARBITRARY prefix AND suffix (and prior history).
||| Prefix induction uses C9; C8 observes name distinctness once at the pair.
||| Applies to native admitted swaps once their unchanged anchor/event
||| annotations are authenticated; does not produce the operational square.
export
0 anchorSwapDecreases :
  {name : Type} -> (nameEq : DecEq name) -> (actor, root : name) ->
  (anchor : Maybe Nat) -> (front, back : List (AnchorEvent name)) ->
  (0 distinct : Not (actor = root)) -> (history : List (AnchorEvent name)) ->
  anchorInversions nameEq history (front ++ (AnchorLife actor :: AnchorBirth root anchor :: back)) =
    S (anchorInversions nameEq history (front ++ (AnchorBirth root anchor :: AnchorLife actor :: back)))
anchorSwapDecreases nameEq actor root anchor [] back distinct history =
  anchorSwapObserved nameEq actor root anchor history back distinct (decEq @{nameEq} actor root) Refl
anchorSwapDecreases nameEq actor root anchor (event :: rest) back distinct history =
  anchorStepPreservesOne nameEq event
    (\past => anchorInversions nameEq past (rest ++ (AnchorLife actor :: AnchorBirth root anchor :: back)))
    (\past => anchorInversions nameEq past (rest ++ (AnchorBirth root anchor :: AnchorLife actor :: back)))
    (anchorSwapDecreases nameEq actor root anchor rest back distinct) history
