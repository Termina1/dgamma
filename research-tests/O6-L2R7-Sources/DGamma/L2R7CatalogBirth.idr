module DGamma.L2R7CatalogBirth

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A decoded actual native root birth for a catalog item. Offset is explicit:
||| the catalog ordinal is the scan offset plus the exact local occurrence.
||| This is not yet bundle placement or general gap coverage.
public export
record CatalogBirthAt
  (name, key, world, error : Type) (value : key -> Type)
  (entry : RootCatalogEntry name key world error value) (offset : Nat)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkCatalogBirthAt
  catalogBirthOccurrence : LocatedActionOccurrence (OInsert (catalogRoot entry) Root (catalogComponent entry)) trace
  0 catalogBirthOrdinal : catalogOrdinal entry = offset + locatedActionOrdinal catalogBirthOccurrence
