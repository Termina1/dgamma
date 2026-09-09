module DGamma.L2R5CatalogFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R4OrdinalObservation
import DGamma.L2R5RootCatalog
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Full original seven-/eight-edge native trails, their GENERATED runtime
||| catalogs and every-root-lookup completeness. Both catalogs are nonempty.
||| These fixtures are already at attached positions; neither catalog asserts
||| attached bundle assignment or derives the physical zero-gap theorem.
public export
record RuntimeCatalogFixtures where
  constructor MkRuntimeCatalogFixtures
  smallCatalogTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) smallTrace
  barrierCatalogTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit) barrierTrace
  0 smallCatalogComputed : scanRootCatalog 0 smallCatalogTrail =
    [MkRootCatalogEntry 4 3 (smallComponent True)]
  0 barrierCatalogComputed : scanRootCatalog 0 barrierCatalogTrail =
    [MkRootCatalogEntry 4 3 (smallComponent True), MkRootCatalogEntry 5 4 (smallComponent False)]
  0 smallCatalogComplete : (ordinal, root : Nat) -> (component : Component Bool (\key => Unit) Unit String) ->
    nativeActionAt smallTrace ordinal = Just (OInsert root Root component) ->
    RootCatalogContains Nat Bool Unit String (\key => Unit) (scanRootCatalog 0 smallCatalogTrail) ordinal (OInsert root Root component)
  0 barrierCatalogComplete : (ordinal, root : Nat) -> (component : Component Bool (\key => Unit) Unit String) ->
    nativeActionAt barrierTrace ordinal = Just (OInsert root Root component) ->
    RootCatalogContains Nat Bool Unit String (\key => Unit) (scanRootCatalog 0 barrierCatalogTrail) ordinal (OInsert root Root component)
