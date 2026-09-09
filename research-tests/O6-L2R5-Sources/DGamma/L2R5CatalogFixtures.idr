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

||| Simultaneously construct both full native annotations, observe the actual
||| generated one-/two-entry catalogs, and apply the general lookup theorem.
||| No supplied catalog, fixture-specific coverage callback or nested builder.
public export
0 runtimeCatalogFixtures : RuntimeCatalogFixtures
runtimeCatalogFixtures = MkRuntimeCatalogFixtures
  (AvailabilityStep (smallState 0)
    (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1)
    (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2)
    (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3)
    (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4)
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (smallState 5)
    (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _
    (AvailabilityStep (smallState 6)
    (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) _
    (AvailabilityEnd (smallState 7)))))))))
  (AvailabilityStep (barrierState 0)
    (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (barrierState 1)
    (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (barrierState 2)
    (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (barrierState 3)
    (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (barrierState 4)
    (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (barrierState 5)
    (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _
    (AvailabilityStep (barrierState 6)
    (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) _
    (AvailabilityStep (barrierState 7)
    (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) _
    (AvailabilityEnd (barrierState 8))))))))))
  Refl Refl
  (scanRootLookupComplete 0 (AvailabilityStep (smallState 0)
    (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1)
    (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (smallState 2)
    (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (smallState 3)
    (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (smallState 4)
    (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (smallState 5)
    (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) _
    (AvailabilityStep (smallState 6)
    (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) _
    (AvailabilityEnd (smallState 7))))))))))
  (scanRootLookupComplete 0 (AvailabilityStep (barrierState 0)
    (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (barrierState 1)
    (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
    (AvailabilityStep (barrierState 2)
    (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
    (AvailabilityStep (barrierState 3)
    (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
    (AvailabilityStep (barrierState 4)
    (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) _
    (AvailabilityStep (barrierState 5)
    (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) _
    (AvailabilityStep (barrierState 6)
    (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) _
    (AvailabilityStep (barrierState 7)
    (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) _
    (AvailabilityEnd (barrierState 8)))))))))))
