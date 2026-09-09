module DGamma.CP5O20ActualHistoryAdvanceSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O19AdvanceObservationSpike
import DGamma.CP5O20SingleRoleAdvanceExtractionSpike
import DGamma.CP5O20NativeAdvanceAttachmentSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20HistoryExecutionSpike
import DGamma.CP5O20PairedAdvanceSpike
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
