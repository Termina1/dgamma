module DGamma.CP3Support

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Ordering
import Decidable.Equality
import Data.Nat

%default total

||| The empty-trace case of the quantitative Progress result. This isolates the
||| remaining theorem debt to no-deadlock and the nonempty numerical bound.
public export
0 progressEndFromNoDeadlock :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (state : SystemState name key value world error) ->
  (noDeadlock : quiet @{nameEq} @{keyEq} state = False ->
    LifecycleMove nameEq keyEq state) ->
  ProgressResult name key world error value nameEq keyEq bound
    (NoTransitions {state})
progressEndFromNoDeadlock nameEq keyEq bound state noDeadlock =
  MkProgressResult noDeadlock perFiber
    (maximalQuietFromNoDeadlock nameEq keyEq state noDeadlock)
  where
    0 perFiber : (actor : name) -> (turns : Nat) ->
      TargetTurnCount name key world error value nameEq keyEq actor
        (NoTransitions {state}) turns ->
      LTE (stepsActingOn @{nameEq} actor (NoTransitions {state}))
        ((bound + 4) * (turns + 1))
    perFiber actor Z NoTargetTurns = LTEZero

||| Executable base case: a successful lifecycle search supplies no-deadlock,
||| hence the full endpoint Progress result for the empty suffix.
public export
0 progressEndFromSearch :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (state : SystemState name key value world error) ->
  (move : LifecycleMove nameEq keyEq state) ->
  firstApplicableLifecycle @{nameEq} @{keyEq} state = Just move ->
  ProgressResult name key world error value nameEq keyEq bound
    (NoTransitions {state})
progressEndFromSearch nameEq keyEq bound state move found =
  progressEndFromNoDeadlock nameEq keyEq bound state
    (\quietFalse => searchedLifecycleMove nameEq keyEq state move found)

||| Lemma 70's base case: the least support fixed point and the Active set are
||| both empty when the registry is empty.
public export
0 supportMatchesActiveEmpty :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  bindings (registry state) = [] ->
  SupportMatchesActive nameEq keyEq state
supportMatchesActiveEmpty nameEq keyEq state empty selected =
  rewrite supportSetEmptyRegistry nameEq keyEq state empty in
  rewrite listMemberEmpty nameEq selected in
  rewrite lookupFiberEmptyRegistry nameEq selected state empty in Refl

public export
0 effectStateRelatedSymmetric :
  EffectStateRelated keyEq left right -> EffectStateRelated keyEq right left
effectStateRelatedSymmetric (MkEffectStateRelated ambient tables) =
  MkEffectStateRelated (sym ambient) (\selected, k => sym (tables selected k))

public export
0 effectStateRelatedTransitive :
  EffectStateRelated keyEq first middle ->
  EffectStateRelated keyEq middle finalState ->
  EffectStateRelated keyEq first finalState
effectStateRelatedTransitive (MkEffectStateRelated ambientLeft tablesLeft)
  (MkEffectStateRelated ambientRight tablesRight) =
    MkEffectStateRelated (trans ambientLeft ambientRight)
      (\selected, k => trans (tablesLeft selected k) (tablesRight selected k))

public export
0 controlEquivalentSymmetric :
  ControlEquivalent name key world error value nameEq left right ->
  ControlEquivalent name key world error value nameEq right left
controlEquivalentSymmetric (MkControlEquivalent pointwise) =
  MkControlEquivalent (\selected => sym (pointwise selected))

public export
0 controlEquivalentTransitive :
  ControlEquivalent name key world error value nameEq first middle ->
  ControlEquivalent name key world error value nameEq middle finalState ->
  ControlEquivalent name key world error value nameEq first finalState
controlEquivalentTransitive (MkControlEquivalent leftPointwise)
  (MkControlEquivalent rightPointwise) =
    MkControlEquivalent
      (\selected => trans (leftPointwise selected) (rightPointwise selected))

public export
0 systemEquivalentSymmetric :
  SystemEquivalent name key world error value nameEq keyEq left right ->
  SystemEquivalent name key world error value nameEq keyEq right left
systemEquivalentSymmetric (MkSystemEquivalent effects controls) =
  MkSystemEquivalent (effectStateRelatedSymmetric effects)
    (controlEquivalentSymmetric controls)

public export
0 systemEquivalentTransitive :
  SystemEquivalent name key world error value nameEq keyEq first middle ->
  SystemEquivalent name key world error value nameEq keyEq middle finalState ->
  SystemEquivalent name key world error value nameEq keyEq first finalState
systemEquivalentTransitive (MkSystemEquivalent leftEffects leftControls)
  (MkSystemEquivalent rightEffects rightControls) =
    MkSystemEquivalent
      (effectStateRelatedTransitive leftEffects rightEffects)
      (controlEquivalentTransitive leftControls rightControls)

||| Same-orchestration is symmetric even though its constructors are oriented
||| as left/right lifecycle deletion steps.
public export
0 sameOrchestrationSymmetric :
  SameOrchestration left right -> SameOrchestration right left
sameOrchestrationSymmetric SameOrchestrationEnd = SameOrchestrationEnd
sameOrchestrationSymmetric
  (SkipLeftLifecycle transition rest lifecycle tail) =
    SkipRightLifecycle transition rest lifecycle
      (sameOrchestrationSymmetric tail)
sameOrchestrationSymmetric
  (SkipRightLifecycle transition rest lifecycle tail) =
    SkipLeftLifecycle transition rest lifecycle
      (sameOrchestrationSymmetric tail)
sameOrchestrationSymmetric
  (MatchOrchestration action leftTransition leftRest rightTransition rightRest
    orchestration leftAction rightAction tail) =
      MatchOrchestration action rightTransition rightRest leftTransition leftRest
        orchestration rightAction leftAction (sameOrchestrationSymmetric tail)

||| Lemma 72 base case: deleting no episodes preserves the original checked
||| trace and endpoint.
public export
0 deletionKeepsAll :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions initial finalState) ->
  DeletionResult name key world error value nameEq keyEq trace
deletionKeepsAll nameEq keyEq trace =
  MkDeletionResult finalState trace
    (systemEquivalentReflexive nameEq keyEq finalState)

||| Sequential deletion witnesses compose; this is the induction-composition
||| operation required by Lemma 72 once one-step deletion is available.
public export
0 deletionResultsCompose :
  (first : DeletionResult name key world error value nameEq keyEq original) ->
  DeletionResult name key world error value nameEq keyEq (surviving first) ->
  DeletionResult name key world error value nameEq keyEq original
deletionResultsCompose first second =
  MkDeletionResult (survivingFinal second) (surviving second)
    (systemEquivalentTransitive (endpointPreserved first)
      (endpointPreserved second))

||| Foreign replay on an empty trace is exactly effect-state equivalence.
public export
0 foreignReplayEmpty :
  EffectStateRelated keyEq initial finalState ->
  ForeignReplay name key world error value keyEq selected
    (NoTransitions {state}) initial finalState
foreignReplayEmpty = ReplayDone

||| The recovery-combined Theorem 64 is now a direct assembly once Corollary 62
||| is supplied. Thus all remaining proof debt is precisely terminal recovery,
||| not resolution structure or dependent packaging.
public export
0 resolutionCoherenceFromTerminalRecovery :
  terminalRecoveryTheorem name key value world error ->
  resolutionCoherenceTheorem name key value world error
resolutionCoherenceFromTerminalRecovery terminal nameEq keyEq selected pre afterState
  episode independent =
  case resolutionStructureTheoremProof nameEq keyEq selected pre
       (lastInstalledState episode)
       (MkEpisodePrefix (closedStartState episode) (closedOpening episode)
         (closedInside episode) (closedInsideInstalled episode)) of
    (providers ** (openingProviders, structure)) =>
      (providers ** (openingProviders, structure,
        terminal nameEq keyEq selected pre afterState episode independent))
