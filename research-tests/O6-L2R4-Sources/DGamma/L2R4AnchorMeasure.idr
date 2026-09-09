module DGamma.L2R4AnchorMeasure

import Data.List
import Data.Nat
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Runtime events for the ratified release-anchor measure, not compatible-
||| cut counting. Release IDs are fixed original removal-ending cuts; a forced
||| birth carries its bundle's release ID, a non-forced birth carries Nothing.
||| Semantic authentication of these annotations is separate from this algebra.
public export
data AnchorEvent : Type -> Type where
  AnchorLife : {name : Type} -> name -> AnchorEvent name
  AnchorRelease : {name : Type} -> Nat -> AnchorEvent name
  AnchorBirth : {name : Type} -> name -> Maybe Nat -> AnchorEvent name
  AnchorOther : {name : Type} -> AnchorEvent name
