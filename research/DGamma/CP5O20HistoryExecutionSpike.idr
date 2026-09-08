module DGamma.CP5O20HistoryExecutionSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20SharedBeginAdapterSpike
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
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
