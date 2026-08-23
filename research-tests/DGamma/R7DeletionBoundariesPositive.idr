module DGamma.R7DeletionBoundariesPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total

public export
scanOnly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  ClosingEpisodeScan name key world error value nameEq keyEq trace
scanOnly = closingEpisodeOccurrenceScanSpike

public export
selectOnly :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, finalState : SystemState name key value world error) ->
  (trace : Transitions initial finalState) ->
  (premises : CanonicalizationPremises name key world error value protocol nameEq keyEq trace) ->
  (scan : ClosingEpisodeScan name key world error value nameEq keyEq trace) ->
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
