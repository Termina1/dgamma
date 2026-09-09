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
