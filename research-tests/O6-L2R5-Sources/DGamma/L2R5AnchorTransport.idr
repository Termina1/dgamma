module DGamma.L2R5AnchorTransport

import DGamma.L2R4AnchorMeasure
import Data.List
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Ordered root/anchor annotations, retaining repeated names as separate
||| occurrence positions. This projection does not assign release identities.
public export
anchorBirths : {name : Type} -> List (AnchorEvent name) -> List (name, Maybe Nat)
anchorBirths [] = []
anchorBirths (AnchorLife actor :: rest) = anchorBirths rest
anchorBirths (AnchorRelease marker :: rest) = anchorBirths rest
anchorBirths (AnchorBirth root anchor :: rest) = (root, anchor) :: anchorBirths rest
anchorBirths (AnchorOther :: rest) = anchorBirths rest

||| A fixed-annotation lifecycle/birth swap preserves the ENTIRE ordered
||| annotation list, including every other root and repeated-name occurrence.
||| Native ordinal-to-anchor reassignment is a separate transport obligation.
export
0 anchorBirthsSwap : {name : Type} -> (actor, root : name) ->
  (anchor : Maybe Nat) -> (front, back : List (AnchorEvent name)) ->
  anchorBirths (front ++ (AnchorLife actor :: AnchorBirth root anchor :: back)) =
  anchorBirths (front ++ (AnchorBirth root anchor :: AnchorLife actor :: back))
anchorBirthsSwap actor root anchor [] back = Refl
anchorBirthsSwap actor root anchor (AnchorLife other :: rest) back =
  anchorBirthsSwap actor root anchor rest back
anchorBirthsSwap actor root anchor (AnchorRelease marker :: rest) back =
  anchorBirthsSwap actor root anchor rest back
anchorBirthsSwap actor root anchor (AnchorBirth other assigned :: rest) back =
  cong ((other, assigned) ::) (anchorBirthsSwap actor root anchor rest back)
anchorBirthsSwap actor root anchor (AnchorOther :: rest) back =
  anchorBirthsSwap actor root anchor rest back
