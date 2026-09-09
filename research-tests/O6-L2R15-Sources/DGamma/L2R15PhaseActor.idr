module DGamma.L2R15PhaseActor

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
import DGamma.L2R10PhaseScan
import DGamma.L2R14PhaseSeed
import DGamma.L2R14PhaseRelease
import DGamma.L2R14PhaseOrigins
import DGamma.L2R15PhaseOccurrence
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Event-at-occurrence makes the observed release actor IDENTICAL to the
||| actual native ORemove parent. Equal ordinals alone are not substituted
||| for this source-aware theorem; the native owner classifier is consumed.
export
0 phaseReleaseActorIdentity : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (actor, observedActor : name) -> (component : Component key value world error) ->
  (release : AttachedRelease name key world error value nameEq actor trace component) ->
  (ordinal : Nat) -> (flag : Bool) ->
  (0 atOrdinal : locatedActionOrdinal (releaseOccurrence release) = ordinal) ->
  (0 event : head' (drop ordinal (phaseEvents nameEq trail)) = Just (Just observedActor, flag)) ->
  observedActor = actor
phaseReleaseActorIdentity nameEq trail actor observedActor component release ordinal flag atOrdinal event =
  injective (cong fst (injective (trans (sym event)
    (trans (sym (cong (\position => head' (drop position (phaseEvents nameEq trail))) atOrdinal))
      (trans (phaseEventAtOccurrence nameEq trail (ORemove (releasedChild release)) (releaseOccurrence release))
        (cong (\owner => Just (owner, False)) (phaseReleaseNativeOwner nameEq actor component release)))))))
