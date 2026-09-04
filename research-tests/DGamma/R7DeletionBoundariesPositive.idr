module DGamma.R7DeletionBoundariesPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

public export
0 scanOnly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  (0 aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  ClosingEpisodeScan name key world error value nameEq keyEq trace
scanOnly = closingEpisodeOccurrenceScanSpike

||| Genuine consumer discharge: canonicalization already authenticates this
||| exact trace under the explicit dictionaries carried by O7.
public export
0 scanFromCanonicalPremises :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq trace) ->
  ClosingEpisodeScan name key world error value nameEq keyEq trace
scanFromCanonicalPremises nameEq keyEq protocol initial finalState trace premises =
  closingEpisodeOccurrenceScanSpike nameEq keyEq initial finalState trace
    (replayAligned (chainReplayCapital premises))

public export
0 selectOnly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (0 scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
  MaximalClosingSelection name key world error value protocol nameEq keyEq trace premises scan
selectOnly = selectMaximalClosingEpisodeSpike

public export
0 enrichOnly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (0 noDependent : NoDependentClosingEpisodeForGeneration
    {nameEq = nameEq} {keyEq = keyEq} {global = trace}
    (selectedActor candidate) (selectedStartOrdinal candidate)
    (selectedStartLive candidate) (selectedEpisode candidate)) ->
  DeletionChainStep name key world error value protocol nameEq keyEq trace premises candidate
enrichOnly = enrichDeletionChainStepSpike

public export
0 coreOnly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceCore name key world error value protocol nameEq keyEq trace
coreOnly = deleteClosingEpisodesCoreSpike

public export
0 accountingOnly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ClosingFreeTraceCore name key world error value protocol nameEq keyEq trace ->
  ClosingFreeReduction name key world error value protocol nameEq keyEq trace
accountingOnly = assembleClosingFreeAccountingSpike

public export
0 compatibilityWrappers :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  ( ClosingStepChoice name key world error value protocol nameEq keyEq trace premises
  , ClosingFreeReduction name key world error value protocol nameEq keyEq trace
  )
compatibilityWrappers nameEq keyEq protocol trace premises =
  (chooseClosingStepSpike nameEq keyEq protocol trace premises,
   deleteAllClosingEpisodesSpike nameEq keyEq protocol trace premises)
