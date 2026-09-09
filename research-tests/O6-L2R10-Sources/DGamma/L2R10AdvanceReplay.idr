module DGamma.L2R10AdvanceReplay

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4RetireReplay
import DGamma.L2R5RetirementFrame
import DGamma.L2R9ResolverRetirement
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Target invariance consumes only the explicit retired Bool observation.
||| No reconstructed/projected conditional family is passed to a consumer.
export
0 retirementTargetAtFlag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (seen : Bool) -> (0 equation : retired actorFiber = seen) ->
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber
    (replaceBinding @{nameEq} child (retireFiber childFiber) source) =
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source
retirementTargetAtFlag nameEq keyEq child parent actor childFiber actorFiber source frame False equation =
  rewrite equation in sym (fst (retirementFrameResolverSame nameEq keyEq child parent actor childFiber actorFiber source frame))
retirementTargetAtFlag nameEq keyEq child parent actor childFiber actorFiber source frame True equation =
  rewrite equation in Refl

||| Actual frame producer for native target equality, no equality oracle.
export
0 retirementTargetSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber
    (replaceBinding @{nameEq} child (retireFiber childFiber) source) =
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source
retirementTargetSame nameEq keyEq child parent actor childFiber actorFiber source frame =
  retirementTargetAtFlag nameEq keyEq child parent actor childFiber actorFiber source frame (retired actorFiber) Refl

||| Precise ALL-TAG native LAdvance observation equation. TYPE only until
||| the observed elimination helpers supply its producer. The RHS retires
||| the original child at the actual original evaluator result, not a chosen
||| late state, and retains the exact ordered binding snapshot.
public export
RetirementAdvanceEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, actor : name) ->
  (childFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) -> Type
RetirementAdvanceEquation {name} {key} {world} {error} {value}
  nameEq keyEq child actor childFiber ambient source =
  observeActionResult {name} {key} {world} {error} {value}
    (applyAction @{nameEq} @{keyEq} (LAdvance actor)
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber childFiber) source))) =
  Prelude.map {f = Maybe}
    (\out => (fst out, runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState (snd out))
        (replaceBinding @{nameEq} child (retireFiber childFiber) (registry (snd out))))))
    (applyAction @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient source))
