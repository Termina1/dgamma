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
import DGamma.CP5CurrentGenerationBirthSpike
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
    occurrence (ExpandedLegacy (BlockOwnLifecycle lifecycle Refl))
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

||| A false lifecycle observation selects exactly Insert/Retire/Remove from
||| the actual action. Remove remains a genuine orchestration role.
export
0 o20OrchestrationFromAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) -> (action : Action name key value world error) ->
  (transitionAction step = action) -> (isLifecycleAction action = False) ->
  PaperOrchestrationStep step
o20OrchestrationFromAction step (OInsert actor parent component) exact nonLifecycle = PaperInsertStep exact
o20OrchestrationFromAction step (ORetire actor) exact nonLifecycle = PaperRetireStep exact
o20OrchestrationFromAction step (ORemove actor) exact nonLifecycle = PaperRemoveStep exact
o20OrchestrationFromAction step (LBegin actor) exact nonLifecycle = absurd nonLifecycle
o20OrchestrationFromAction step (LAdvance actor) exact nonLifecycle = absurd nonLifecycle
o20OrchestrationFromAction step (LDivert actor) exact nonLifecycle = absurd nonLifecycle
o20OrchestrationFromAction step (LLeave actor) exact nonLifecycle = absurd nonLifecycle
o20OrchestrationFromAction step (LUnload actor) exact nonLifecycle = absurd nonLifecycle

||| Single observed Bool classification at any actual decomposed occurrence.
||| The two branches retain exact native tags and locations, not guessed roles.
export
0 o20DecomposedActionObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> (order : List name) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq order trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (action : Action name key value world error) -> (occurrence : LocatedActionOccurrence action trace) ->
  (observed : Bool) -> (isLifecycleAction action = observed) ->
  Either (PaperActivationStep (locatedTransition occurrence)) (PaperOrchestrationStep (locatedTransition occurrence))
o20DecomposedActionObserved nameEq keyEq protocol trace order blocks premises action occurrence True exact =
  Left (o20DecomposedLifecyclePaper nameEq keyEq protocol trace order blocks premises action occurrence exact)
o20DecomposedActionObserved nameEq keyEq protocol trace order blocks premises action occurrence False exact =
  Right (o20OrchestrationFromAction (locatedTransition occurrence) action (locatedAction occurrence) exact)

||| Erased unilateral role word indexed by the WHOLE actual native trace.
||| It deliberately does not claim paired edge alignment or a shared name cut.
public export
data O20CanonicalTraceRoles :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  Transitions before afterState -> Type where
  O20RolesEnd : O20CanonicalTraceRoles NoTransitions
  O20RolesStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {before, middle, afterState : SystemState name key value world error} ->
    {step : Transition before middle} -> {rest : Transitions middle afterState} ->
    (0 role : Either (PaperActivationStep step) (PaperOrchestrationStep step)) ->
    (0 roles : O20CanonicalTraceRoles rest) ->
    O20CanonicalTraceRoles (MoreTransitions step rest)

||| A constructor-owned occurrence embedding keeps the exact native step.
||| This avoids observing a computed dependent location merely by Refl.
export
0 o20RolesInTail :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, middle, afterState : SystemState name key value world error} ->
  (step : Transition before middle) -> (rest : Transitions middle afterState) ->
  ((action : Action name key value world error) ->
   (location : LocatedActionOccurrence action (MoreTransitions step rest)) ->
   Either (PaperActivationStep (locatedTransition location)) (PaperOrchestrationStep (locatedTransition location))) ->
  (action : Action name key value world error) -> (location : LocatedActionOccurrence action rest) ->
  Either (PaperActivationStep (locatedTransition location)) (PaperOrchestrationStep (locatedTransition location))
o20RolesInTail step rest classified action
  (MkLocatedActionOccurrence before afterState prior located later exact decomposition) =
    classified action (MkLocatedActionOccurrence before afterState (MoreTransitions step prior)
      located later exact (cong (MoreTransitions step) decomposition))

||| Structural induction over every edge of the actual trace, not a selected
||| pair. The classifier is consumed at the head and transported into its tail.
export
0 o20RolesFromLocations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (trace : Transitions before afterState) ->
  ((action : Action name key value world error) ->
   (location : LocatedActionOccurrence action trace) ->
   Either (PaperActivationStep (locatedTransition location)) (PaperOrchestrationStep (locatedTransition location))) ->
  O20CanonicalTraceRoles trace
o20RolesFromLocations NoTransitions classified = O20RolesEnd
o20RolesFromLocations {before} (MoreTransitions {middle} step rest) classified =
  O20RolesStep
    (classified (transitionAction step) (MkLocatedActionOccurrence before middle NoTransitions step rest Refl Refl))
    (o20RolesFromLocations rest (o20RolesInTail step rest classified))

||| Whole accepted canonical trace has only Begin/Iter/Finish and native
||| Insert/Retire/Remove. This removes the failure/diversion completeness debt
||| for each unilateral canonical word, but does NOT pair the two words.
export
0 o20WholeCanonicalRoles :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq trace) ->
  O20CanonicalTraceRoles (canonicalTrace (canonicalSchedule capital))
o20WholeCanonicalRoles nameEq keyEq protocol trace capital =
  o20RolesFromLocations (canonicalTrace (canonicalSchedule capital))
    (\action, location => o20DecomposedActionObserved nameEq keyEq protocol
      (canonicalTrace (canonicalSchedule capital)) (supportOrder (canonicalSchedule capital))
      (canonicalActorBlockDecomposition capital) (canonicalReplayPremises capital)
      action location (isLifecycleAction action) Refl)
