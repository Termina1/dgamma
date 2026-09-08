module DGamma.CP5O20HistoryExecutionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20SharedBeginAdapterSpike
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Actual paired Begin preserves BOTH runtime and historical generation
||| clauses. Native source well-formedness supplies provision disjointness;
||| no successful callback, output relation or endpoint current map is input.
export
0 o20HistoryBeginCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive leftBefore rightBefore) ->
  BeginStep nameEq keyEq actor leftBefore leftAfter ->
  BeginStep nameEq keyEq (renameForward (historyCutBijection paired) actor) rightBefore rightAfter ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} rightBefore = True) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LBegin actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal
      (LBegin (renameForward (historyCutBijection paired) actor)) rightLive) leftAfter rightAfter
o20HistoryBeginCut {name} {key} {world} {error} {value} nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  leftBefore leftAfter rightBefore rightAfter (MkO20HistoryCut renaming runtime forward backward) leftOpening rightOpening valid =
    MkO20HistoryCut renaming
      (o20PairedActualBeginCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor
        leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening runtime
        (registryWellFormedPairwiseOpenAnchor {name} {key} {value} {world} {error} nameEq keyEq rightBefore valid))
      forward backward

||| Actual Retire edits controls but neither live generation environment.
||| The runtime successor is proved by the checked native retire producer;
||| history compatibility is retained, not inferred from endpoint support.
export
0 o20HistoryRetireCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftOld, rightOld : Fiber name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just leftOld) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward (historyCutBijection paired) actor) rightRegistry = Just rightOld) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (ORetire actor) (MkSystemState leftWorld leftRegistry) =
    Just (ORetireTag, MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (ORetire (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) =
    Just (ORetireTag, MkSystemState rightWorld
      (replaceBinding @{nameEq} (renameForward (historyCutBijection paired) actor) (retireFiber rightOld) rightRegistry))) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (ORetire actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal
      (ORetire (renameForward (historyCutBijection paired) actor)) rightLive)
    (MkSystemState leftWorld (replaceBinding @{nameEq} actor (retireFiber leftOld) leftRegistry))
    (MkSystemState rightWorld
      (replaceBinding @{nameEq} (renameForward (historyCutBijection paired) actor) (retireFiber rightOld) rightRegistry))
o20HistoryRetireCut {name} {key} {world} {error} {value} nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld (MkO20HistoryCut renaming runtime forward backward)
  leftFound rightFound leftChecked rightChecked =
    MkO20HistoryCut renaming
      (o20PairedObservedRetireCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor
        leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked runtime)
      forward backward

||| Exact current-generation insertion preserves a pointwise name/stamp map.
||| This generic lookup lemma is used in BOTH directions; its new-owner clause
||| is an actual generation-match equation, not an endpoint relation oracle.
export
0 o20HistoryPutCompatibility :
  {name : Type} -> (nameEq : DecEq name) ->
  (rawTarget : name -> name) -> (stampTarget : RegistrationGeneration name -> name) ->
  (actor : name) -> (newStamp : RegistrationGeneration name) -> (live : GenerationEnvironment name) ->
  (rawTarget actor = stampTarget newStamp) ->
  ((selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected live = Just stamp) -> (rawTarget selected = stampTarget stamp)) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (putCurrentGeneration @{nameEq} actor newStamp live) = Just stamp) ->
  (rawTarget selected = stampTarget stamp)
o20HistoryPutCompatibility nameEq rawTarget stampTarget actor newStamp live matched previous selected stamp found =
  case decEq @{nameEq} selected actor of
    Yes same => trans (cong rawTarget same)
      (trans matched (cong stampTarget (justInjective
        (trans (sym (lookupPutCurrentSelf nameEq actor newStamp live))
          (trans (cong (\query => lookupCurrentGeneration @{nameEq} query
            (putCurrentGeneration @{nameEq} actor newStamp live)) (sym same)) found)))))
    No different => previous selected stamp
      (trans (sym (lookupPutCurrentOther nameEq selected actor different newStamp live)) found)
