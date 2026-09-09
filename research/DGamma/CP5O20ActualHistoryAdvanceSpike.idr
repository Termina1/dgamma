module DGamma.CP5O20ActualHistoryAdvanceSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19AdvanceObservationSpike
import DGamma.CP5O20SingleRoleAdvanceExtractionSpike
import DGamma.CP5O20NativeAdvanceAttachmentSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20HistoryExecutionSpike
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5O20IndexedReloadingSourceSpike
import DGamma.CP5O20NativeTargetAttachmentSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Attach the history successor to TWO ACTUAL checked Advance endpoints.
||| The observed native packets supply primitive resolution/callback equations;
||| evaluator determinism supplies both target equations. Source lookups and
||| target guards remain explicit until single-role source extraction is wired.
export
0 o20HistoryActualAdvanceValues :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (component : Component key value world error) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent, rightParent : Parent name) -> (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView, rightView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAfter, rightAfter : SystemState name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading (step :: rest) leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward (historyCutBijection paired) actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading (step :: rest) rightOlder rightView))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component leftParent leftRetired leftTable (Reloading (step :: rest) leftOlder leftView)) leftRegistry = Just leftView) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component rightParent rightRetired rightTable (Reloading (step :: rest) rightOlder rightView)) rightRegistry = Just rightView) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (leftTag, leftAfter)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) = Just (rightTag, rightAfter)) ->
  (leftValues : O20NativeStepValues name key world error value nameEq keyEq (MkSystemState leftWorld leftRegistry) component leftTable step leftView) ->
  (rightValues : O20NativeStepValues name key world error value nameEq keyEq (MkSystemState rightWorld rightRegistry) component rightTable step rightView) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LAdvance actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal (LAdvance (renameForward (historyCutBijection paired) actor)) rightLive)
    leftAfter rightAfter
o20HistoryActualAdvanceValues {name} {key} {world} {error} {value} nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
  leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftTag rightTag paired
  leftFound rightFound leftTarget rightTarget leftChecked rightChecked leftValues rightValues =
    rewrite o20ActualAdvanceObservedEndpoint nameEq keyEq actor leftWorld leftRegistry leftAfter leftTag
      component leftParent leftRetired leftTable step rest leftOlder leftView leftFound leftTarget leftChecked leftValues in
    rewrite o20ActualAdvanceObservedEndpoint nameEq keyEq (renameForward (historyCutBijection paired) actor) rightWorld rightRegistry rightAfter rightTag
      component rightParent rightRetired rightTable step rest rightOlder rightView rightFound rightTarget rightChecked rightValues in
    o20HistoryObservedAdvanceCut nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
      component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
      leftWorld rightWorld leftRegistry rightRegistry
      (stepObservedAfter (nativeCallback leftValues)) (stepObservedAfter (nativeCallback rightValues))
      (stepObservedUndo (nativeCallback leftValues)) (stepObservedUndo (nativeCallback rightValues))
      (nativeCapability leftValues) (nativeCapability rightValues) leftTag rightTag paired leftFound rightFound
      (trans (resolveEffectValuesProjected nameEq keyEq (dependencies (componentDependencies component)) leftView (MkSystemState leftWorld leftRegistry)) (nativeResolution leftValues))
      (trans (resolveEffectValuesProjected nameEq keyEq (dependencies (componentDependencies component)) rightView (MkSystemState rightWorld rightRegistry)) (nativeResolution rightValues))
      (o20NativeCallbackProjected nameEq keyEq actor leftWorld leftRegistry component leftParent leftRetired leftTable
        (Reloading (step :: rest) leftOlder leftView) step leftView leftFound leftValues)
      (o20NativeCallbackProjected nameEq keyEq (renameForward (historyCutBijection paired) actor) rightWorld rightRegistry component rightParent rightRetired rightTable
        (Reloading (step :: rest) rightOlder rightView) step rightView rightFound rightValues)
      (trans leftChecked (cong (\state => Just (leftTag, state))
        (o20ActualAdvanceObservedEndpoint nameEq keyEq actor leftWorld leftRegistry leftAfter leftTag
          component leftParent leftRetired leftTable step rest leftOlder leftView leftFound leftTarget leftChecked leftValues)))
      (trans rightChecked (cong (\state => Just (rightTag, state))
        (o20ActualAdvanceObservedEndpoint nameEq keyEq (renameForward (historyCutBijection paired) actor) rightWorld rightRegistry rightAfter rightTag
          component rightParent rightRetired rightTable step rest rightOlder rightView rightFound rightTarget rightChecked rightValues)))

||| Two actual Iter edges now PRODUCE their resolver/callback values and
||| literal successor attachment. Only source-program lookups and target
||| guards remain explicit; no domain, callback or successor-cut oracle enters.
export
0 o20HistoryActualIterCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (component : Component key value world error) ->
  (step, next : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (more : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent, rightParent : Parent name) -> (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView, rightView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAfter, rightAfter : SystemState name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading (step :: next :: more) leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward (historyCutBijection paired) actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading (step :: next :: more) rightOlder rightView))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component leftParent leftRetired leftTable (Reloading (step :: next :: more) leftOlder leftView)) leftRegistry = Just leftView) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component rightParent rightRetired rightTable (Reloading (step :: next :: more) rightOlder rightView)) rightRegistry = Just rightView) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LIterTag, leftAfter)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) = Just (LIterTag, rightAfter)) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LAdvance actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal (LAdvance (renameForward (historyCutBijection paired) actor)) rightLive)
    leftAfter rightAfter
o20HistoryActualIterCut nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  component step next more leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
  leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter paired
  leftFound rightFound leftTarget rightTarget leftChecked rightChecked =
    o20HistoryActualAdvanceValues nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
      component step (next :: more) leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
      leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter LIterTag LIterTag paired
      leftFound rightFound leftTarget rightTarget leftChecked rightChecked
      (o20IterNativeValues nameEq keyEq actor (MkSystemState leftWorld leftRegistry) leftAfter
        component leftParent leftRetired leftTable step next more leftOlder leftView leftFound leftChecked)
      (o20IterNativeValues nameEq keyEq (renameForward (historyCutBijection paired) actor) (MkSystemState rightWorld rightRegistry) rightAfter
        component rightParent rightRetired rightTable step next more rightOlder rightView rightFound rightChecked)

||| Two actual last-step Finish edges produce their native callback packets
||| and land at their ACTUAL endpoints. Only source lookups and target guards
||| are explicit; empty Finish remains the separate no-callback constructor.
export
0 o20HistoryActualFinishOneCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (component : Component key value world error) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (leftParent, rightParent : Parent name) -> (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder, rightOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView, rightView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAfter, rightAfter : SystemState name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading [step] leftOlder leftView))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward (historyCutBijection paired) actor) rightRegistry = Just (MkFiber component rightParent rightRetired rightTable (Reloading [step] rightOlder rightView))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component leftParent leftRetired leftTable (Reloading [step] leftOlder leftView)) leftRegistry = Just leftView) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component rightParent rightRetired rightTable (Reloading [step] rightOlder rightView)) rightRegistry = Just rightView) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LFinishTag, leftAfter)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) = Just (LFinishTag, rightAfter)) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LAdvance actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal (LAdvance (renameForward (historyCutBijection paired) actor)) rightLive)
    leftAfter rightAfter
o20HistoryActualFinishOneCut nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  component step leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
  leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter paired
  leftFound rightFound leftTarget rightTarget leftChecked rightChecked =
    o20HistoryActualAdvanceValues nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
      component step [] leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
      leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter LFinishTag LFinishTag paired
      leftFound rightFound leftTarget rightTarget leftChecked rightChecked
      (o20FinishOneNativeValues nameEq keyEq actor (MkSystemState leftWorld leftRegistry) leftAfter
        component leftParent leftRetired leftTable step leftOlder leftView leftFound leftChecked)
      (o20FinishOneNativeValues nameEq keyEq (renameForward (historyCutBijection paired) actor) (MkSystemState rightWorld rightRegistry) rightAfter
        component rightParent rightRetired rightTable step rightOlder rightView rightFound rightChecked)

||| Open one indexed opposite-source observation. Both target guards, both
||| callbacks and both actual successor equations are then native outputs,
||| not caller hypotheses. The next producer supplies this source packet.
export
0 o20HistoryIterAtMatchingSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (component : Component key value world error) ->
  (step, next : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (more : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent : Parent name) -> (leftRetired : Bool) ->
  (leftTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAfter, rightAfter : SystemState name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading (step :: next :: more) leftOlder leftView))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LIterTag, leftAfter)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) = Just (LIterTag, rightAfter)) ->
  (rightSource : O20MatchingReloadingSource name key world error value nameEq
    (renameForward (historyCutBijection paired) actor) (MkSystemState rightWorld rightRegistry) component (step :: next :: more)) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LAdvance actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal (LAdvance (renameForward (historyCutBijection paired) actor)) rightLive)
    leftAfter rightAfter
o20HistoryIterAtMatchingSource nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  component step next more leftParent leftRetired leftTable leftOlder leftView
  leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter paired leftFound leftChecked rightChecked
  (MkO20MatchingReloadingSource rightParent rightRetired rightTable rightOlder rightView rightFound) =
    o20HistoryActualIterCut nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
      component step next more leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView
      leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter paired leftFound rightFound
      (o20CheckedIterTarget nameEq keyEq actor (MkSystemState leftWorld leftRegistry) leftAfter
        component leftParent leftRetired leftTable (step :: next :: more) leftOlder leftView leftFound leftChecked)
      (o20CheckedIterTarget nameEq keyEq (renameForward (historyCutBijection paired) actor) (MkSystemState rightWorld rightRegistry) rightAfter
        component rightParent rightRetired rightTable (step :: next :: more) rightOlder rightView rightFound rightChecked)
      leftChecked rightChecked

||| The pre-cut PRODUCES the indexed opposite source; both actual Iter edges
||| produce target guards, callbacks and final cuts. Only ONE left source
||| lookup remains explicit, not a right lookup, shared-program or success oracle.
export
0 o20HistoryIterKnownLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (component : Component key value world error) ->
  (step, next : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (more : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (leftParent : Parent name) -> (leftRetired : Bool) ->
  (leftTable : OwnedTable key value (componentProvisions component)) ->
  (leftOlder : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (leftView : View name (dependencies (componentDependencies component))) ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAfter, rightAfter : SystemState name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just (MkFiber component leftParent leftRetired leftTable (Reloading (step :: next :: more) leftOlder leftView))) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState leftWorld leftRegistry) = Just (LIterTag, leftAfter)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) = Just (LIterTag, rightAfter)) ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LAdvance actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal (LAdvance (renameForward (historyCutBijection paired) actor)) rightLive)
    leftAfter rightAfter
o20HistoryIterKnownLeft {name} {key} {world} {error} {value} nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  component step next more leftParent leftRetired leftTable leftOlder leftView
  leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter paired leftFound leftChecked rightChecked =
    o20HistoryIterAtMatchingSource nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
      component step next more leftParent leftRetired leftTable leftOlder leftView
      leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter paired leftFound leftChecked rightChecked
      (o20MatchingReloadingFromCut {name} {key} {world} {error} {value} {nameEq}
        {renaming = historyCutBijection paired} {actor}
        {left = MkSystemState leftWorld leftRegistry} {right = MkSystemState rightWorld rightRegistry}
        component (step :: next :: more) leftParent leftRetired leftTable leftOlder leftView leftFound (historyCutRuntime paired))

||| Open the single-role native left Iter source. Its constructor supplies the
||| source program and lookup; A28 derives the whole right source and all
||| runtime observations. No caller supplies an independently reconstructed
||| target equation or a callback equation.
export
0 o20HistoryIterFromPaperSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (actor : name) ->
  (leftOrdinal, rightOrdinal : Nat) -> (leftLive, rightLive : GenerationEnvironment name) ->
  (leftBefore, leftAfter, rightAfter : SystemState name key value world error) ->
  (rightWorld : world) -> (rightRegistry : Registry name key value world error) ->
  (paired : O20HistoryCut name key world error value nameEq mapping leftLive rightLive leftBefore (MkSystemState rightWorld rightRegistry)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) leftBefore = Just (LIterTag, leftAfter)) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance (renameForward (historyCutBijection paired) actor)) (MkSystemState rightWorld rightRegistry) = Just (LIterTag, rightAfter)) ->
  PaperAdvanceSource name key world error value nameEq keyEq actor LIterTag leftBefore ->
  O20HistoryCut name key world error value nameEq mapping
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} leftOrdinal (LAdvance actor) leftLive)
    (advanceGenerationEnvironment {name} {key} {value} {world} {error} @{nameEq} rightOrdinal (LAdvance (renameForward (historyCutBijection paired) actor)) rightLive)
    leftAfter rightAfter
o20HistoryIterFromPaperSource nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
  _ leftAfter rightAfter rightWorld rightRegistry paired leftChecked rightChecked
  (AdvanceSourceIter {ambient} {fibers} {component} {parent} {retiredFlag} {table} {step} {next} {more} {accumulator} {view} Refl found target) =
    o20HistoryIterKnownLeft nameEq keyEq mapping actor leftOrdinal rightOrdinal leftLive rightLive
      component step next more parent retiredFlag table accumulator view ambient rightWorld fibers rightRegistry
      leftAfter rightAfter paired found leftChecked rightChecked
