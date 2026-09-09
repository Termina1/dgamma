module DGamma.L2R14PhaseOrigins

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R5RootCatalog
import DGamma.L2R8ReleaseScan
import DGamma.L2R9OrdinalScan
import DGamma.L2R9OrdinalLink
import DGamma.L2R10ReleaseAgreement
import DGamma.L2R12PhaseAccepted
import DGamma.L2R14PhaseSeed
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

import DGamma.L2R6Anchors
import DGamma.L2R6ForcedScan
import DGamma.L2R7ObservedAny
import DGamma.L2R7CatalogBirth
import DGamma.L2R10PhaseScan
import DGamma.L2R13PhaseEntry
import DGamma.L2R14PhaseRelease

%default total
%unbound_implicits off

||| General forced-origin producer FROM produceForcedPhaseEntry. It produces
||| both the phase-event actor/check and actual global own-child release at
||| the SAME physical ordinal. Actor identity between these observations and
||| localization of that release inside an owned lifecycle core remain OPEN.
||| This is deliberately NOT named produceForcedRootPhases.
export
0 produceForcedPhaseOrigins : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (scanRootCatalog 0 trail)) ->
  (0 accepted : phaseScanOk nameEq keyEq trail = True) ->
  (0 classified : any (\seed => catalogOrdinal seed <= catalogOrdinal entry &&
    keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) = True) ->
  (anchor : Nat ** (anchorOf nameEq keyEq trail (catalogOrdinal entry) = Just anchor,
    (seed : RootCatalogEntry name key world error value **
      (Elem seed (scanRootCatalog 0 trail),
       phaseAnchorSeedCheck nameEq keyEq trail entry anchor seed = True,
       (actor : name ** (flag : Bool **
         (head' (drop (pred anchor) (phaseEvents nameEq trail)) = Just (Just actor, flag),
          phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail) = True))),
       (packet : (actor : name ** AttachedRelease name key world error value nameEq actor trace (catalogComponent seed)) **
         locatedActionOrdinal (releaseOccurrence (snd packet)) = pred anchor))),
    CatalogBirthAt name key world error value entry 0 trace))
produceForcedPhaseOrigins nameEq keyEq trail entry member accepted classified =
  ((fst (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified)) ** (fst (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified)),
    ((hitItem (fst (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified))))) ** (hitMember (fst (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified)))), (hitAccepted (fst (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified))))),
      phaseSeedActor nameEq keyEq trail entry (hitItem (fst (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified))))) (fst (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified)) (hitAccepted (fst (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified))))),
      phaseSeedRelease nameEq keyEq trail entry (hitItem (fst (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified))))) (fst (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified)) (hitAccepted (fst (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified))))))),
    snd (snd (snd (produceForcedPhaseEntry nameEq keyEq trail entry member accepted classified)))))
