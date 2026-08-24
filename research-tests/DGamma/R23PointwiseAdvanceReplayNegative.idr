module DGamma.R23PointwiseAdvanceReplayNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionRelationalLifecycleAdvance
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality

%default total

||| Expected failure at the first suffix head of the corrected R23 fixture.
||| Revision 17 deliberately exposes pointwise `ControlEquivalent` at the local
||| diamond endpoint, while the older Lemma-72 lifecycle replayer still consumes
||| ordered-list `OrderedRegistryControlsRelated`.  Passing the pointwise value
||| as ordered capital is rejected.
0 relationalEndpointDoesNotSupplyOrderedAdvanceReplay :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) ->
  (sourceBefore, replayedBefore : SystemState name key value world error) ->
  (leftNamed : NamedTransition name key world error value (LAdvance actor)
    sourceBefore) ->
  applyAction @{nameEq} @{keyEq} (LAdvance actor) sourceBefore =
    Just (namedTag leftNamed, namedAfter leftNamed) ->
  registryWellFormed @{nameEq} @{keyEq} sourceBefore = True ->
  RelationalReplayEndpoint name key world error value nameEq keyEq
    sourceBefore replayedBefore ->
  RelatedNamedActionReplay name key world error value nameEq keyEq
    (LAdvance actor) sourceBefore replayedBefore leftNamed
relationalEndpointDoesNotSupplyOrderedAdvanceReplay nameEq keyEq actor
  sourceBefore replayedBefore leftNamed raw sourceWellFormed endpoint =
    replayRelatedAdvance nameEq keyEq actor sourceBefore replayedBefore leftNamed
      raw sourceWellFormed (replayedEffects endpoint) (replayedControls endpoint)
      (replayedWellFormed endpoint)
