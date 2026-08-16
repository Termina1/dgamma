module DGamma.CP3StatementChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality
import Data.List.Elem

%default total

||| Regression guard for round-1 blocker 1: Lemma 70 cannot be applied without
||| a checked reachability witness from an empty, well-formed registry.
public export
0 supportLemma70Guard :
  supportAtQuiescenceTheorem name key value world error ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  ReachedFromEmpty name key world error value nameEq keyEq state ->
  PrecedenceAcyclic nameEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  noFailedFibers state = True ->
  ComponentsTotalOnProvision @{nameEq} @{keyEq} state ->
  SupportMatchesActive nameEq keyEq state
supportLemma70Guard claim nameEq keyEq state reached acyclic
  quietState noFailures totality =
    claim nameEq keyEq state reached acyclic quietState noFailures totality

||| Lemma 68 is an independent exported statement, not an implicit assumption
||| hidden inside Lemma 70.
public export
0 supportLemma68Guard :
  supportWellFoundedTheorem name key value world error ->
  supportWellFoundedTheorem name key value world error
supportLemma68Guard claim = claim

||| Regression guards for Equation 62 and Theorem 73's canonical fields.
public export
0 canonicalOrderUniqueGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  UniqueKeys (supportOrder schedule)
canonicalOrderUniqueGuard schedule = orderUnique (supportLinearization schedule)

public export
0 canonicalCombinedOrderGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  (lower, upper : name) ->
  SupportPath nameEq originalFinal lower upper ->
  Elem lower (supportOrder schedule) -> Elem upper (supportOrder schedule) ->
  BeforeIn lower upper (supportOrder schedule)
canonicalCombinedOrderGuard schedule =
  supportPathsOrdered (supportLinearization schedule)

public export
0 canonicalCoverageGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  LifecycleActorsCovered (supportOrder schedule) (canonicalTrace schedule)
canonicalCoverageGuard schedule = lifecycleCoverage schedule

public export
0 canonicalInputPlacementGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  CanonicalInputPlacement name key world error value nameEq keyEq originalFinal
    (supportOrder schedule) (canonicalTrace schedule)
canonicalInputPlacementGuard schedule = inputPlacement schedule

public export
0 canonicalBlockGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  (n : name) -> (present : Elem n (supportOrder schedule)) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq n
    (canonicalTrace schedule)
canonicalBlockGuard schedule = canonicalBlock schedule

||| Regression guard for Equation 53: the canonical endpoint carries the full
||| fiber relation, not only lifecycle shape/provider-name observations.
public export
0 canonicalFullControlGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {trace : Transitions initial originalFinal} ->
  (schedule : CanonicalSchedule name key world error value nameEq keyEq trace) ->
  ControlEquivalent name key world error value nameEq originalFinal
    (canonicalFinal schedule)
canonicalFullControlGuard schedule = controlsEquivalent (canonicalEndpoint schedule)

||| Regression guards for Lemma 72's selected-episode deletion and outside-R
||| control/withdrawal conclusions.
public export
0 deletionSubsequenceGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  ActionSubsequence (EpisodeDeletedActor selected registered)
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode episode)))
      (closedTransitions (locatedEpisode episode)))
    (survivingEpisode result)
deletionSubsequenceGuard result = episodeDeletion result

public export
0 deletionOutsideControlGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  ControlEquivalentOutside nameEq registered originalFinal (survivingFinal result)
deletionOutsideControlGuard result = controlsPreservedOutside result

public export
0 deletionWithdrawnGuard :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} -> {selected : name} ->
  {episode : LocatedClosedEpisode name key world error value nameEq keyEq
    selected original} -> {registered : List name} ->
  (result : DeletionResult name key world error value nameEq keyEq original
    selected episode registered) ->
  RegisteredNamesWithdrawn nameEq registered originalFinal (survivingFinal result)
deletionWithdrawnGuard result = registeredWithdrawn result
