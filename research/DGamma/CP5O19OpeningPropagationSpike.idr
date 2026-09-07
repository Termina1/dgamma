module DGamma.CP5O19OpeningPropagationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Convert an OBSERVED raw move to an actual checked early guard. Both target
||| data and its equation are the existing producer's projections; preservation
||| derives the target-domain check, with no assumed intermediate applicability.
public export
0 o19CheckObservedRawMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before : SystemState name key value world error) ->
  (registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (raw : RawActivationMove nameEq keyEq action tag before) ->
  CheckedEarlyApplication name key world error value nameEq keyEq before action tag
o19CheckObservedRawMove nameEq keyEq action tag before wellFormed raw =
  MkCheckedEarlyApplication (rawActivationAfter raw)
    (rewrite rawActivationRuns raw in
     rewrite preservationTheoremProof nameEq keyEq action before
       (rawActivationAfter raw) tag wellFormed (rawActivationRuns raw) in Refl)

||| Propagate the EXISTING source Begin guard over one actual foreign
||| activation. Alignment supplies the dictionaries; ordinary preservation
||| supplies both checked-domain facts. No new guard oracle is introduced.
public export
0 o19BeginAfterActivation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {before, afterState : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  PaperActivationStep (Fired {before} {afterState} nameEq keyEq action tag checked) ->
  Not (actor = actionOwner action) ->
  (registryWellFormed @{nameEq} @{keyEq} before = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq before (LBegin actor) LBeginTag ->
  CheckedEarlyApplication name key world error value nameEq keyEq afterState (LBegin actor) LBeginTag
o19BeginAfterActivation {before} {afterState} nameEq keyEq actor action tag
  checked activation distinct wellFormed early =
    o19CheckObservedRawMove nameEq keyEq (LBegin actor) LBeginTag afterState
      (preservationTheoremProof nameEq keyEq action before afterState tag wellFormed
        (checkedActionProjects nameEq keyEq action before afterState tag checked))
      (beginRawAfterForeignActivation nameEq keyEq actor action tag
        (earlyApplicationChecked early) checked activation distinct
        (preservationTheoremProof nameEq keyEq action before afterState tag wellFormed
          (checkedActionProjects nameEq keyEq action before afterState tag checked)))

||| The actual cuts of one observed trace, including its final cut. This is
||| internal iteration evidence: the producer below derives it from ONE guard.
public export
data O19EarlyAlong :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  {before, finalState : SystemState name key value world error} ->
  Transitions before finalState -> Type where
  EarlyAlongEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {action : Action name key value world error} -> {tag : RuleTag} ->
    {before : SystemState name key value world error} ->
    (0 early : CheckedEarlyApplication name key world error value nameEq keyEq before action tag) ->
    O19EarlyAlong name key world error value nameEq keyEq action tag (NoTransitions {state = before})
  EarlyAlongStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {action : Action name key value world error} -> {tag : RuleTag} ->
    {before, middle, finalState : SystemState name key value world error} ->
    (step : Transition before middle) -> (rest : Transitions middle finalState) ->
    (0 early : CheckedEarlyApplication name key world error value nameEq keyEq before action tag) ->
    (0 remaining : O19EarlyAlong name key world error value nameEq keyEq action tag rest) ->
    O19EarlyAlong name key world error value nameEq keyEq action tag (MoreTransitions step rest)
