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
