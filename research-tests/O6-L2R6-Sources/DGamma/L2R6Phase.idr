module DGamma.L2R6Phase

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R3Attached
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6PlacementFixtures
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| PHASE premise for one forced catalog root (key or barrier). Its assigned
||| anchor is an ACTUAL own-child Remove at the END of a located actor core,
||| after that actor's located lifecycle. A key-seed at/before this root owns
||| the shared provision witness. Pre-lifecycle removal of an initially
||| retired child is excluded explicitly, not normalized across front inputs.
||| TYPE ONLY; the general producer produceForcedRootPhases remains OPEN.
public export
record ForcedRootPhase
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  {trace : Transitions initial finalState}
  (trail : AvailabilityTrace name key world error value trace)
  (entry : RootCatalogEntry name key world error value) where
  constructor MkForcedRootPhase
  phaseSeed : RootCatalogEntry name key world error value
  0 phaseSeedMember : Elem phaseSeed (scanRootCatalog 0 trail)
  0 phaseSeedEarlier : LTE (catalogOrdinal phaseSeed) (catalogOrdinal entry)
  0 phaseSeedKeyForced : keyForcedOrdinal nameEq keyEq trail (catalogOrdinal phaseSeed) = True
  phaseActor : name
  phaseCoreStart : SystemState name key value world error
  phaseCoreEnd : SystemState name key value world error
  phasePrefix : Transitions initial phaseCoreStart
  phaseCore : Transitions phaseCoreStart phaseCoreEnd
  phaseSuffix : Transitions phaseCoreEnd finalState
  0 phaseExtended : ActorLifecycleOnlyExtended nameEq phaseActor phaseCore
  0 phaseGlobalSplit : appendTransitions phasePrefix (appendTransitions phaseCore phaseSuffix) = trace
  phaseRelease : AttachedRelease name key world error value nameEq phaseActor phaseCore (catalogComponent phaseSeed)
  phaseLifeAction : Action name key value world error
  phaseLife : LocatedActionOccurrence phaseLifeAction phaseCore
  phaseLifecycleObserved : Bool
  0 phaseLifecycleEquation : isLifecycleAction phaseLifeAction = phaseLifecycleObserved
  0 phaseLifecycleAccepted : phaseLifecycleObserved = True
  0 phaseLifeOwner : actionOwner phaseLifeAction = phaseActor
  0 phaseLifeBeforeRelease : LT (locatedActionOrdinal phaseLife) (locatedActionOrdinal (releaseOccurrence phaseRelease))
  0 phaseReleaseEndsCore : transitionCount phaseCore = S (locatedActionOrdinal (releaseOccurrence phaseRelease))
  0 phaseAnchorEquation : anchorOf nameEq keyEq trail (catalogOrdinal entry) =
    Just (transitionCount phasePrefix + S (locatedActionOrdinal (releaseOccurrence phaseRelease)))
  0 phaseCoreBeforeBirth : LTE (transitionCount phasePrefix + transitionCount phaseCore) (catalogOrdinal entry)
