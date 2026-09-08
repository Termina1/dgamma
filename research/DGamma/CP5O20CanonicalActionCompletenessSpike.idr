module DGamma.CP5O20CanonicalActionCompletenessSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O19OriginalBlockClassSpike
import DGamma.CP5O19PaperBranchCompletenessSpike
import DGamma.CP5O19ReachedDecompositionSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Every actual lifecycle occurrence covered by the full block decomposition
||| is a paper Begin/Iter/Finish. Final Active plus installed bodies and no
||| outside lifecycle exclude Raise/Divert/Leave/Unload, via the existing
||| native absorption proof. Alignment is projected from this exact bundle.
export
0 o20DecomposedLifecyclePaper :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> (order : List name) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq order trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action trace) ->
  (isLifecycleAction action = True) -> PaperActivationStep (locatedTransition occurrence)
o20DecomposedLifecyclePaper {name} {key} {world} {error} {value} nameEq keyEq protocol trace order blocks premises action occurrence lifecycle =
  o19OriginalPaperBranch nameEq keyEq (actionOwner action) (actionOwner action) trace
    (decomposedBlock blocks (actionOwner action)
      (o19LocatedLifecycleCovered trace (decomposedLifecycleCoverage blocks) action occurrence lifecycle))
    occurrence (BlockOwnLifecycle lifecycle Refl)
    (snd (alignedAppendSplit (beforeActionOccurrence occurrence)
      (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence))
      (replace {p = AlignedTransitions name key world error value nameEq keyEq}
        (sym (actionOccurrenceDecomposition occurrence)) (replayAligned premises)))) lifecycle

||| Accepted independent canonical capital supplies the complete decomposition
||| and the exact replay bundle used by A17. No no-failure-at-every-cut or
||| success-role premise is added; the native final-active argument derives it.
export
0 o20CanonicalLifecyclePaper :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  (action : Action name key value world error) ->
  (occurrence : LocatedActionOccurrence action (canonicalTrace (canonicalSchedule capital))) ->
  (isLifecycleAction action = True) -> PaperActivationStep (locatedTransition occurrence)
o20CanonicalLifecyclePaper nameEq keyEq protocol trace capital action occurrence lifecycle =
  o20DecomposedLifecyclePaper nameEq keyEq protocol (canonicalTrace (canonicalSchedule capital))
    (supportOrder (canonicalSchedule capital)) (canonicalActorBlockDecomposition capital)
    (canonicalReplayPremises capital) action occurrence lifecycle
