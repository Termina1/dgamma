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

||| One event's action on a root's historical foreign-lifecycle count.
||| A matching release discards earlier history; other roots do not reset it.
||| This fixed-anchor distinction avoids the compatible-cut 1,1,0 plateau.
public export
anchorHistoryStep : {name : Type} -> (nameEq : DecEq name) ->
  (root : name) -> (anchor : Maybe Nat) -> AnchorEvent name -> Nat -> Nat
anchorHistoryStep nameEq root anchor (AnchorLife actor) prior =
  if isYes (decEq @{nameEq} actor root) then prior else S prior
anchorHistoryStep nameEq root anchor (AnchorRelease marker) prior =
  if anchor == Just marker then 0 else prior
anchorHistoryStep nameEq root anchor (AnchorBirth actor otherAnchor) prior = prior
anchorHistoryStep nameEq root anchor AnchorOther prior = prior

||| Count foreign lifecycle events since a root's fixed release in reverse-
||| chronological history. Nothing counts from trace start. A forced anchor
||| must actually occur in authenticated history; assignment is not inferred.
public export
anchorHistoryCount : {name : Type} -> DecEq name -> name -> Maybe Nat -> List (AnchorEvent name) -> Nat
anchorHistoryCount nameEq root anchor history = foldr (anchorHistoryStep nameEq root anchor) 0 history

||| One chronological event's contribution to total inversions. Births charge
||| their own fixed-anchor cost but do NOT alter historical counting context,
||| so hoisting one root cannot expose a new inversion for a later bundle root.
public export
anchorMeasureStep : {name : Type} -> (nameEq : DecEq name) -> AnchorEvent name ->
  (List (AnchorEvent name) -> Nat) -> List (AnchorEvent name) -> Nat
anchorMeasureStep nameEq (AnchorBirth root anchor) later history =
  anchorHistoryCount nameEq root anchor history + later history
anchorMeasureStep nameEq (AnchorLife actor) later history = later (AnchorLife actor :: history)
anchorMeasureStep nameEq (AnchorRelease marker) later history = later (AnchorRelease marker :: history)
anchorMeasureStep nameEq AnchorOther later history = later (AnchorOther :: history)
