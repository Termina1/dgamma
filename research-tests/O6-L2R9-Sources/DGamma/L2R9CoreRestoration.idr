module DGamma.L2R9CoreRestoration

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R5Extensional
import DGamma.L2R6Iteration
import DGamma.L2R8ContiguityStates
import DGamma.L2R8CoreContract
import DGamma.L2R9ContiguityPackets
import DGamma.L2R9RestoredPackets
import DGamma.L2R9ContiguityEndpoints
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Concrete premise/conclusion instance of GeneralCoreContiguityRestored,
||| not a proof of its universally quantified type. Both complete native
||| paths start at smallState0. The intermediate split path is NOT asserted.
public export
record CoreRestorationFixture where
  constructor MkCoreRestorationFixture
  originalRun : Transitions (smallState 0) (contiguityState 7)
  restoredRun : Transitions (smallState 0) (contiguityState 17)
  originalTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) originalRun
  restoredTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit) restoredRun
  originalCore : LocatedExtendedCore Nat Bool Unit String (\key => Unit) %search 2 originalRun
  restoredCore : LocatedExtendedCore Nat Bool Unit String (\key => Unit) %search 2 restoredRun
  0 originValid : registryWellFormed @{%search} @{%search} (smallState 0) = True
  0 rootForeign : (the Nat 3) = 2 -> Void
  0 originalSuffix : nativeActionWord (afterCoreTrail originalCore) =
    [OInsert 3 Root (smallComponent True), OInsert 4 Root (smallComponent False)]
  0 restoredWholeWord : nativeActionWord restoredTrail = nativeActionWord (beforeCoreTrail originalCore) ++
    OInsert 3 Root (smallComponent True) :: (nativeActionWord (coreTrail originalCore) ++
      [OInsert 4 Root (smallComponent False)])
  0 sameCoreActionWord : nativeActionWord (coreTrail restoredCore) = nativeActionWord (coreTrail originalCore)
  0 restoredCorePosition : transitionCount (beforeCore restoredCore) = S (transitionCount (beforeCore originalCore))
  0 wholeRunEndpoints : RegistryExtensional Nat Bool Unit String (\key => Unit) %search
    (contiguityState 7) (contiguityState 17)
