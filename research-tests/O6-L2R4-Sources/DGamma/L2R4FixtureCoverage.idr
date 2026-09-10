module DGamma.L2R4FixtureCoverage

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3AttachedGap
import DGamma.L2R3FixtureCoverage
import DGamma.L2R4OrdinalObservation
import DGamma.L2R4CatalogCoverage
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Nonempty pre-attachment native root windows: C12 [4,5), barrier [4,6).
||| Exact step equations identify both windows in the SAME existing native
||| fixture origins. NF quantifies over EVERY occurrence, not named births only.
public export
record FixtureRootRegions where
  constructor MkFixtureRootRegions
  smallRegion : Transitions (smallState 4) (smallState 5)
  barrierRegion : Transitions (barrierState 4) (barrierState 6)
  0 smallRegionExact : smallRegion = MoreTransitions
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search
      (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions
  0 barrierRegionExact : barrierRegion = MoreTransitions
    (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search
      (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search
      (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions)
  0 smallRegionCount : transitionCount smallRegion = 1
  0 barrierRegionCount : transitionCount barrierRegion = 2
  0 smallRegionNF : DGamma.L2R3AttachedGap.AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search smallTrace smallRegion 4
  0 barrierRegionNF : DGamma.L2R3AttachedGap.AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search barrierTrace barrierRegion 4

||| NONVACUOUS general occurrence coverage on both native pre-attachment
||| windows. Catalog completeness is built by cons induction from the A22
||| actual members, then catalogNormalForm handles every dependent occurrence.
||| The widths are 1 and 2, not the honestly empty post-attachment gaps.
public export
0 fixtureRootRegions : FixtureRootRegions
fixtureRootRegions = MkFixtureRootRegions
  (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search
    (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions)
  (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search
    (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
    (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search
      (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions))
  Refl Refl Refl Refl
  (catalogNormalForm _ 4
    (catalogConsObserved
      (Fired {before = smallState 4} {afterState = smallState 5} %search %search
        (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions 4
      (c12CatalogR fixtureCoverage) (\n, action, exact => void (nothingIsNotJust exact))))
  (catalogNormalForm _ 4
    (catalogConsObserved
      (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search
        (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution))
      (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search
        (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions) 4
      (barrierCatalogR fixtureCoverage)
      (catalogConsObserved
        (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search
          (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) NoTransitions 5
        (barrierCatalogS fixtureCoverage) (\n, action, exact => void (nothingIsNotJust exact)))))
