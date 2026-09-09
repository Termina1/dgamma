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
