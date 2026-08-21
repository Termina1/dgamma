module DGamma.CP5ConfluenceDeletionChainSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionTheorem
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| Structural measure proposed for delete-then-match Path A.  It avoids
||| deciding equality of dependent episode witnesses: every Lemma-72 call drops
||| at least its selected L-Begin and L-Unload, hence this raw trace measure can
||| drive well-founded recursion.
public export
traceLength : Transitions first finalState -> Nat
traceLength NoTransitions = 0
traceLength (MoreTransitions transition rest) = S (traceLength rest)

public export
NoClosingEpisodes :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> Type
NoClosingEpisodes name key world error value nameEq keyEq trace =
  (selected : name) ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected trace ->
  Void

||| The public premises that must survive each deletion if Lemma 72 is used as
||| an iterative subroutine rather than once.  This record exposes an important
||| proof obligation hidden by the paper prose: totality, alignment, discipline,
||| independence, quiet, and no-failure must all be restricted/transported to
||| the freshly constructed survivor trace.
public export
record CanonicalizationPremises
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkCanonicalizationPremises
  0 chainAligned : AlignedTransitions name key world error value nameEq keyEq trace
  0 chainDiscipline : RegistrationDiscipline protocol nameEq trace
  0 chainInitialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True
  0 chainInitialEmpty : bindings (registry initial) = []
  0 chainQuiet : quiet @{nameEq} @{keyEq} finalState = True
  0 chainNoFailure : noFailedFibers finalState = True
  0 chainTotal : TraceComponentsTotal nameEq keyEq trace
  0 chainIndependent : TraceIndependent name key world error value keyEq trace

||| All occurrence-local inputs needed for one checked Lemma-72 call.  The
||| maximal-closing selector must derive the final two negative episode fields;
||| callers should not have to guess them.
public export
record DeletableClosingEpisode
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkDeletableClosingEpisode
  selectedActor : name
  selectedEpisode : LocatedClosedEpisode name key world error value nameEq keyEq
    selectedActor trace
  selectedRegistrations : List (RegistrationGeneration name)
  0 selectedOutsideRegistrations :
    (generation : RegistrationGeneration name) ->
    Elem generation selectedRegistrations ->
    Not (generationName generation = selectedActor)
  selectedStartOrdinal : Nat
  selectedStartLive : GenerationEnvironment name
  0 selectedBeforeScan : GenerationTraceScan nameEq 0 []
    (traceBeforeOpening selectedEpisode) selectedStartOrdinal selectedStartLive
  0 selectedRegisteredDuring : RegisteredGenerationsDuring selectedActor
    selectedStartOrdinal selectedRegistrations
    (MoreTransitions
      (beginTransition (closedOpening (locatedEpisode selectedEpisode)))
      (closedTransitions (locatedEpisode selectedEpisode)))
  0 selectedNoDependentClose : NoDependentClosingEpisode
    {nameEq = nameEq} {keyEq = keyEq} selectedActor trace
  0 selectedChildrenHaveNoEpisode : NoRegisteredEpisode nameEq
    selectedRegistrations 0 [] trace

||| One decreasing deletion step, including the complete premise-preservation
||| package needed by the recursive call.
public export
record DeletionChainStep
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace)
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
    trace) where
  constructor MkDeletionChainStep
  deletionResult : DeletionResult name key world error value nameEq keyEq trace
    (selectedActor candidate) (selectedEpisode candidate)
    (selectedRegistrations candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate)
  nextPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq (survivingTrace deletionResult)
  0 deletionStrictlyShorter :
    LTE (S (traceLength (survivingTrace deletionResult))) (traceLength trace)

||| Executable/constructive selection boundary for the finite trace.  The
||| `HasClosingStep` branch must choose a support/parent-maximal closing episode
||| and manufacture every negative premise required by Lemma 72.
public export
data ClosingStepChoice :
  (name : Type) -> (key : Type) -> (world : Type) -> (error : Type) ->
  (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) -> Type where
  ClosingFree : NoClosingEpisodes name key world error value nameEq keyEq trace ->
    ClosingStepChoice name key world error value protocol nameEq keyEq trace
      premises
  HasClosingStep :
    (candidate : DeletableClosingEpisode name key world error value nameEq keyEq
      trace) ->
    DeletionChainStep name key world error value protocol nameEq keyEq trace
      premises candidate ->
    ClosingStepChoice name key world error value protocol nameEq keyEq trace
      premises

||| Endpoint package after deleting every closing episode.  The cumulative
||| endpoint relation validates the union of withdrawn raw names and exact birth
||| generations and is the bridge into orchestration placement/episode sorting.
public export
record ClosingFreeReduction
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkClosingFreeReduction
  reducedFinal : SystemState name key value world error
  reducedTrace : Transitions initial reducedFinal
  reducedPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq reducedTrace
  0 reducedClosingFree : NoClosingEpisodes name key world error value nameEq keyEq
    reducedTrace
  cumulativeEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal reducedFinal

||| The already checked Lemma-72 implementation is available at the exact
||| public type expected by the chain.
public export
0 checkedDeletionSubroutine : deletionTheorem name key value world error
checkedDeletionSubroutine = deletionTheoremProof

||| Spike A: finite maximal selection plus preservation of the recursive public
||| premises.  This is expected to be XL even though the actual deletion call is
||| now one line, because maximality is over located episodes and the survivor
||| is relationally replayed rather than definitionally equal to a subsequence.
public export
0 chooseClosingStepSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  ClosingStepChoice name key world error value protocol nameEq keyEq trace
    premises
chooseClosingStepSpike = ?chooseClosingStepSpike_rhs

||| Spike B: well-founded recursion on `traceLength`, composing each deletion's
||| exact-generation withdrawal metadata and relational endpoint evidence.
public export
0 deleteAllClosingEpisodesSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq trace ->
  ClosingFreeReduction name key world error value protocol nameEq keyEq trace
deleteAllClosingEpisodesSpike = ?deleteAllClosingEpisodesSpike_rhs
