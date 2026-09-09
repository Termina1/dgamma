module DGamma.L2R5RootCatalog

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R4OrdinalObservation
import Data.List.Elem
import Data.Maybe
import Data.Nat

%default total
%unbound_implicits off

||| Runtime root-insertion catalog item: original physical ordinal, actor and
||| actual component. No forced-root classification or bundle is asserted.
public export
record RootCatalogEntry
  (name, key, world, error : Type) (value : key -> Type) where
  constructor MkRootCatalogEntry
  catalogOrdinal : Nat
  catalogRoot : name
  catalogComponent : Component key value world error

||| Exhaustive runtime Action classifier: only OInsert Root adds an entry.
||| Child Insert, root Retire/Remove and every lifecycle action are not births.
public export
rootCatalogStep : {name, key, world, error : Type} -> {value : key -> Type} ->
  Nat -> Action name key value world error ->
  List (RootCatalogEntry name key world error value) -> List (RootCatalogEntry name key world error value)
rootCatalogStep ordinal (OInsert root Root component) later = MkRootCatalogEntry ordinal root component :: later
rootCatalogStep ordinal (OInsert actor (ChildOf parent) component) later = later
rootCatalogStep ordinal (ORetire actor) later = later
rootCatalogStep ordinal (ORemove actor) later = later
rootCatalogStep ordinal (LBegin actor) later = later
rootCatalogStep ordinal (LAdvance actor) later = later
rootCatalogStep ordinal (LDivert actor) later = later
rootCatalogStep ordinal (LUnload actor) later = later
rootCatalogStep ordinal (LLeave actor) later = later

||| Total executable catalog scan FROM the actual checked native trail. All
||| input ordinals advance, including non-birth actions; no catalog is supplied.
public export
scanRootCatalog : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  (offset : Nat) -> AvailabilityTrace name key world error value trace ->
  List (RootCatalogEntry name key world error value)
scanRootCatalog offset (AvailabilityEnd state) = []
scanRootCatalog offset (AvailabilityStep first (Fired nameEq keyEq action tag checked) rest later) =
  rootCatalogStep offset action (scanRootCatalog (S offset) later)

||| A catalog member with producer-owned action and ordinal equations. This
||| authenticates a raw birth catalog only, NOT an AttachedBundleOccurrence.
public export
record RootCatalogContains
  (name, key, world, error : Type) (value : key -> Type)
  (0 entries : List (RootCatalogEntry name key world error value))
  (ordinal : Nat) (action : Action name key value world error) where
  constructor MkRootCatalogContains
  catalogItem : RootCatalogEntry name key world error value
  0 itemPresent : Elem catalogItem entries
  0 itemOrdinal : catalogOrdinal catalogItem = ordinal
  0 itemAction : OInsert (catalogRoot catalogItem) Root (catalogComponent catalogItem) = action

||| A head action observed as a root insertion is genuinely inserted by the
||| runtime classifier. Exhaustive Action elimination, no pre-supplied member.
export
0 rootCatalogHeadComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (offset : Nat) -> (action : Action name key value world error) ->
  (later : List (RootCatalogEntry name key world error value)) ->
  (root : name) -> (component : Component key value world error) ->
  (0 exact : action = OInsert root Root component) ->
  RootCatalogContains name key world error value (rootCatalogStep offset action later) offset (OInsert root Root component)
rootCatalogHeadComplete {name} {key} {world} {error} {value} offset (OInsert own Root ownComponent) later root component exact =
  replace {p = RootCatalogContains name key world error value
    (rootCatalogStep offset (OInsert own Root ownComponent) later) offset} exact
    (MkRootCatalogContains (MkRootCatalogEntry offset own ownComponent) Here Refl Refl)
rootCatalogHeadComplete offset (OInsert _ (ChildOf parent) _) later root component Refl impossible
rootCatalogHeadComplete offset (ORetire actor) later root component Refl impossible
rootCatalogHeadComplete offset (ORemove actor) later root component Refl impossible
rootCatalogHeadComplete offset (LBegin actor) later root component Refl impossible
rootCatalogHeadComplete offset (LAdvance actor) later root component Refl impossible
rootCatalogHeadComplete offset (LDivert actor) later root component Refl impossible
rootCatalogHeadComplete offset (LUnload actor) later root component Refl impossible
rootCatalogHeadComplete offset (LLeave actor) later root component Refl impossible
