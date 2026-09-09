module DGamma.L2R14CatalogQuery

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6Iteration
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Shift a genuine catalog action query through exactly one physical head.
||| Both ordinal arithmetic and the native action query are retained.
export
0 catalogQueryThroughHead : {name, key, world, error : Type} -> {value : key -> Type} ->
  (head : Action name key value world error) -> (word : List (Action name key value world error)) ->
  (entry : RootCatalogEntry name key world error value) -> (offset : Nat) ->
  (query : (position : Nat ** (catalogOrdinal entry = S offset + position,
    head' (drop position word) = Just (OInsert (catalogRoot entry) Root (catalogComponent entry))))) ->
  (position : Nat ** (catalogOrdinal entry = offset + position,
    head' (drop position (head :: word)) = Just (OInsert (catalogRoot entry) Root (catalogComponent entry))))
catalogQueryThroughHead head word entry offset (position ** (ordinal, action)) =
  (S position ** (trans ordinal (plusSuccRightSucc offset position), action))

||| The catalog's actual root cons either supplies the head query or lifts
||| the structurally obtained tail query. Only membership is eliminated.
export
0 catalogQueryInsert : {name, key, world, error : Type} -> {value : key -> Type} ->
  (root : name) -> (component : Component key value world error) -> (offset : Nat) ->
  (word : List (Action name key value world error)) ->
  (catalog : List (RootCatalogEntry name key world error value)) ->
  (0 tail : (item : RootCatalogEntry name key world error value) -> Elem item catalog ->
    (position : Nat ** (catalogOrdinal item = S offset + position,
      head' (drop position word) = Just (OInsert (catalogRoot item) Root (catalogComponent item))))) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (MkRootCatalogEntry offset root component :: catalog)) ->
  (position : Nat ** (catalogOrdinal entry = offset + position,
    head' (drop position (OInsert root Root component :: word)) =
      Just (OInsert (catalogRoot entry) Root (catalogComponent entry))))
catalogQueryInsert root component offset word catalog tail _ Here =
  (0 ** (sym (plusZeroRightNeutral offset), Refl))
catalogQueryInsert root component offset word catalog tail entry (There later) =
  catalogQueryThroughHead (OInsert root Root component) word entry offset (tail entry later)

||| Exhaustive authentic head-action classification for catalog word queries.
||| No action, source or root-birth query is supplied for the whole trail.
export
0 catalogQueryAtAction : {name, key, world, error : Type} -> {value : key -> Type} ->
  (head : Action name key value world error) -> (offset : Nat) ->
  (word : List (Action name key value world error)) ->
  (catalog : List (RootCatalogEntry name key world error value)) ->
  (0 tail : (item : RootCatalogEntry name key world error value) -> Elem item catalog ->
    (position : Nat ** (catalogOrdinal item = S offset + position,
      head' (drop position word) = Just (OInsert (catalogRoot item) Root (catalogComponent item))))) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (rootCatalogStep offset head catalog)) ->
  (position : Nat ** (catalogOrdinal entry = offset + position,
    head' (drop position (head :: word)) = Just (OInsert (catalogRoot entry) Root (catalogComponent entry))))
catalogQueryAtAction (OInsert root Root component) offset word catalog tail entry member =
  catalogQueryInsert root component offset word catalog tail entry member
catalogQueryAtAction (OInsert child (ChildOf parent) component) offset word catalog tail entry member =
  catalogQueryThroughHead (OInsert child (ChildOf parent) component) word entry offset (tail entry member)
catalogQueryAtAction (ORetire actor) offset word catalog tail entry member =
  catalogQueryThroughHead (ORetire actor) word entry offset (tail entry member)
catalogQueryAtAction (ORemove actor) offset word catalog tail entry member =
  catalogQueryThroughHead (ORemove actor) word entry offset (tail entry member)
catalogQueryAtAction (LBegin actor) offset word catalog tail entry member =
  catalogQueryThroughHead (LBegin actor) word entry offset (tail entry member)
catalogQueryAtAction (LAdvance actor) offset word catalog tail entry member =
  catalogQueryThroughHead (LAdvance actor) word entry offset (tail entry member)
catalogQueryAtAction (LDivert actor) offset word catalog tail entry member =
  catalogQueryThroughHead (LDivert actor) word entry offset (tail entry member)
catalogQueryAtAction (LUnload actor) offset word catalog tail entry member =
  catalogQueryThroughHead (LUnload actor) word entry offset (tail entry member)
catalogQueryAtAction (LLeave actor) offset word catalog tail entry member =
  catalogQueryThroughHead (LLeave actor) word entry offset (tail entry member)

||| GENERAL catalog membership to native action-word query, by induction
||| on the authentic availability trail. Source/dictionary alignment follows
||| separately; neither a birth action nor a word equation is assumed.
export
0 scanCatalogActionQuery : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (offset : Nat) -> (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog offset trail)) ->
  (position : Nat ** (catalogOrdinal entry = offset + position,
    head' (drop position (nativeActionWord trail)) = Just (OInsert (catalogRoot entry) Root (catalogComponent entry))))
scanCatalogActionQuery offset (AvailabilityEnd state) entry member = absurd member
scanCatalogActionQuery offset (AvailabilityStep source (Fired ne ke action tag checked) rest later) entry member =
  catalogQueryAtAction action offset (nativeActionWord later) (scanRootCatalog (S offset) later)
    (\item, present => scanCatalogActionQuery (S offset) later item present) entry member
