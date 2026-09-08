module DGamma.CP5O20HistoryExecutionSpike

import DGamma.Core
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

||| Matched actual root/generated Insert preserves the whole history cut.
||| The one local birth-stamp equation remains explicit: extracting it and
||| aligning fresh runtime names from arbitrary paired traces is NOT claimed.
export
0 o20HistoryMatchedInsertCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (component : Component key value world error) -> (leftParent, rightParent : Parent name) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  ParentRelatedBy (historyCutBijection paired) leftParent rightParent ->
  (leftAbsent : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Nothing)) ->
  (rightAbsent : (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    (renameForward (historyCutBijection paired) actor) rightRegistry = Nothing)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert actor leftParent component) (MkSystemState leftWorld leftRegistry) =
    Just (OInsertTag, MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (OInsert (renameForward (historyCutBijection paired) actor) rightParent component) (MkSystemState rightWorld rightRegistry) =
    Just (OInsertTag, MkSystemState rightWorld (insertBinding @{nameEq}
      (renameForward (historyCutBijection paired) actor) (freshFiber component rightParent) rightRegistry rightAbsent))) ->
  (generationForward mapping (MkRegistrationGeneration actor leftOrdinal) =
    MkRegistrationGeneration (renameForward (historyCutBijection paired) actor) rightOrdinal) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (OInsert actor leftParent component) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal
      (OInsert (renameForward (historyCutBijection paired) actor) rightParent component) rightLive)
    (MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent))
    (MkSystemState rightWorld (insertBinding @{nameEq}
      (renameForward (historyCutBijection paired) actor) (freshFiber component rightParent) rightRegistry rightAbsent))
o20HistoryMatchedInsertCut {name} {key} {world} {error} {value} nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  component leftParent rightParent leftWorld rightWorld leftRegistry rightRegistry
  (MkO20HistoryCut renaming runtime forward backward) parents leftAbsent rightAbsent leftChecked rightChecked matched =
    MkO20HistoryCut renaming
      (o20PairedObservedInsertCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor component leftParent rightParent parents
        leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked runtime)
      (o20HistoryPutCompatibility nameEq (renameForward renaming) (o20HistoricalTarget mapping)
        actor (MkRegistrationGeneration actor leftOrdinal) leftLive (sym (cong generationName matched)) forward)
      (o20HistoryPutCompatibility nameEq (renameBackward renaming) (\stamp => generationName (generationBackward mapping stamp))
        (renameForward renaming actor) (MkRegistrationGeneration (renameForward renaming actor) rightOrdinal) rightLive
        (trans (renameLeftInverse renaming actor)
          (sym (cong generationName (trans (cong (generationBackward mapping) (sym matched))
            (generationLeftInverse mapping (MkRegistrationGeneration actor leftOrdinal)))))) backward)

||| Actual empty-program Finish changes no live stamp and derives the whole
||| runtime successor through the existing checked native producer. This is
||| the empty native case, not a callback-domain or paired-extraction oracle.
export
0 o20HistoryEmptyFinishCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) -> (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView, rightView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading [] leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward (historyCutBijection paired) actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading [] rightOlder rightView))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LFinishTag, (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry)))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) = Just (LFinishTag, (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward (historyCutBijection paired) actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry)))) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LAdvance actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal
      (LAdvance (renameForward (historyCutBijection paired) actor)) rightLive)
    (MkSystemState leftWorld (replaceBinding @{nameEq} actor (MkFiber component leftParent leftRetired leftTable (Active leftOlder leftView)) leftRegistry)) (MkSystemState rightWorld (replaceBinding @{nameEq} (renameForward (historyCutBijection paired) actor) (MkFiber component rightParent rightRetired rightTable (Active rightOlder rightView)) rightRegistry))
o20HistoryEmptyFinishCut {name} {key} {world} {error} {value} nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
  leftWorld rightWorld leftRegistry rightRegistry (MkO20HistoryCut renaming runtime forward backward)
  leftFound rightFound leftChecked rightChecked =
    MkO20HistoryCut renaming
      (o20PairedObservedEmptyFinishCut {name} {key} {world} {error} {value} nameEq keyEq renaming actor
        component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
        leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked runtime)
      forward backward
