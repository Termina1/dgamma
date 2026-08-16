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
  MkControlEquivalent
    (\selected => fiberControlMaybeSymmetric (pointwise selected))

public export
0 controlEquivalentTransitive :
  ControlEquivalent name key world error value nameEq first middle ->
  ControlEquivalent name key world error value nameEq middle finalState ->
  ControlEquivalent name key world error value nameEq first finalState
controlEquivalentTransitive (MkControlEquivalent leftPointwise)
  (MkControlEquivalent rightPointwise) =
    MkControlEquivalent
      (\selected => fiberControlMaybeTransitive (leftPointwise selected)
        (rightPointwise selected))

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

0 boolTrueFalse : observed = True -> observed = False -> result
boolTrueFalse Refl Refl impossible

||| Shared-orchestration witnesses compose. The two mismatch cases are
||| impossible because the shared middle transition cannot be both lifecycle
||| and orchestration.
public export
0 sameOrchestrationTransitive :
  SameOrchestration left middle -> SameOrchestration middle right ->
  SameOrchestration left right
sameOrchestrationTransitive SameOrchestrationEnd SameOrchestrationEnd =
  SameOrchestrationEnd
sameOrchestrationTransitive
  (SkipLeftLifecycle transition rest lifecycle tail) rightWitness =
    SkipLeftLifecycle transition rest lifecycle
      (sameOrchestrationTransitive tail rightWitness)
sameOrchestrationTransitive leftWitness
  (SkipRightLifecycle transition rest lifecycle tail) =
    SkipRightLifecycle transition rest lifecycle
      (sameOrchestrationTransitive leftWitness tail)
sameOrchestrationTransitive
  (SkipRightLifecycle middleTransition middleRest lifecycle firstTail)
  (SkipLeftLifecycle middleTransition middleRest lifecycleAgain secondTail) =
    sameOrchestrationTransitive firstTail secondTail
sameOrchestrationTransitive
  (SkipRightLifecycle middleTransition middleRest lifecycle firstTail)
  (MatchOrchestration action middleTransition middleRest rightTransition rightRest
    orchestration middleAction rightAction secondTail) =
      boolTrueFalse
        (trans (sym (cong isLifecycleAction middleAction)) lifecycle)
        orchestration
sameOrchestrationTransitive
  (MatchOrchestration action leftTransition leftRest middleTransition middleRest
    orchestration leftAction middleAction firstTail)
  (SkipLeftLifecycle middleTransition middleRest lifecycle secondTail) =
      boolTrueFalse
        (trans (sym (cong isLifecycleAction middleAction)) lifecycle)
        orchestration
sameOrchestrationTransitive
  (MatchOrchestration leftActionValue leftTransition leftRest middleTransition
    middleRest leftOrchestration leftAction middleLeftAction firstTail)
  (MatchOrchestration rightActionValue middleTransition middleRest rightTransition
    rightRest rightOrchestration middleRightAction rightAction secondTail) =
      case trans (sym middleLeftAction) middleRightAction of
        Refl => MatchOrchestration leftActionValue leftTransition leftRest
          rightTransition rightRest leftOrchestration leftAction rightAction
          (sameOrchestrationTransitive firstTail secondTail)

||| If the canonical sorting/deletion construction returns the same canonical
||| endpoint for two schedules, observational uniqueness follows by symmetry
||| and transitivity. This discharges Theorem 73's final diagram chase.
public export
0 canonicalEndpointsEquivalent :
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  (leftSchedule : CanonicalSchedule name key world error value nameEq keyEq
    leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value nameEq keyEq
    rightTrace) ->
  canonicalFinal leftSchedule = canonicalFinal rightSchedule ->
  SystemEquivalent name key world error value nameEq keyEq leftFinal rightFinal
canonicalEndpointsEquivalent leftSchedule rightSchedule sameFinal =
  systemEquivalentTransitive (canonicalEndpoint leftSchedule)
    (replace {p = \state => SystemEquivalent name key world error value nameEq
      keyEq state rightFinal} (sym sameFinal)
      (systemEquivalentSymmetric (canonicalEndpoint rightSchedule)))

||| Canonical-schedule construction plus endpoint coincidence is precisely the
||| still-missing constructive core of full Confluence; all packaging after it
||| is proved here.
public export
0 confluenceFromCanonicalSchedules :
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  (leftSchedule : CanonicalSchedule name key world error value nameEq keyEq
    leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value nameEq keyEq
    rightTrace) ->
  canonicalFinal leftSchedule = canonicalFinal rightSchedule ->
  (CanonicalSchedule name key world error value nameEq keyEq leftTrace,
   CanonicalSchedule name key world error value nameEq keyEq rightTrace,
   SystemEquivalent name key world error value nameEq keyEq leftFinal rightFinal)
confluenceFromCanonicalSchedules leftSchedule rightSchedule sameFinal =
  (leftSchedule, rightSchedule,
    canonicalEndpointsEquivalent leftSchedule rightSchedule sameFinal)

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
