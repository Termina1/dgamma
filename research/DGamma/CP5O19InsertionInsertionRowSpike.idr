module DGamma.CP5O19InsertionInsertionRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP3StatementChecks
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Construct an insertion from its explicit setFresh observation and guard facts.
||| Preservation supplies the checked target domain; no early action assumed.
export
0 o19InsertAtObservedFresh :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (observed : (applied : CoeffectApplied source **
    (setFresh @{nameEq} child (freshFiber component parent) source = Just applied))) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
      (componentProvisions component) (bindings source) = True) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (MkSystemState ambient source)
    (OInsert child parent component) OInsertTag
o19InsertAtObservedFresh nameEq keyEq child parent component ambient source (applied ** inserted) guards wellFormed =
  o19CheckObservedRawMove nameEq keyEq (OInsert child parent component) OInsertTag
    (MkSystemState ambient source) wellFormed
    (MkRawActivationMove
      (MkSystemState ambient (coeffectAfter applied))
      (rewrite guards in rewrite inserted in Refl))


||| Actual fresh-plan production, not equality of unrelated absence tokens.
export
0 o19InsertFromAbsentGuards :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (child : name) -> (parent : Parent name) -> (component : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Nothing) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
      (componentProvisions component) (bindings source) = True) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (MkSystemState ambient source)
    (OInsert child parent component) OInsertTag
o19InsertFromAbsentGuards nameEq keyEq child parent component ambient source absent guards wellFormed =
  o19InsertAtObservedFresh nameEq keyEq child parent component ambient source
    (DGamma.CP4DeletionSelectedForeignOrchestration.setFreshFromAbsent nameEq child
      (freshFiber component parent) source absent) guards wellFormed

||| A foreign insertion cannot supply this licensing parent. Observe Parent
||| once; the child case is a named lookup frame, not a resolver transport.
export
0 o19ParentBeforeForeignInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent : Parent name) -> (child : name) ->
  (insertedParent : Parent name) -> (component : Component key value world error) ->
  (source : Registry name key value world error) ->
  (absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Nothing) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (licensor = child)) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent
    (insertBinding @{nameEq} child (freshFiber component insertedParent) source absent) =
   parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source)
o19ParentBeforeForeignInsert nameEq Root child insertedParent component source absent foreign = Refl
o19ParentBeforeForeignInsert nameEq (ChildOf licensor) child insertedParent component source absent foreign =
  cong isJust (lookupInsertOther @{nameEq} licensor child (foreign licensor Refl)
    (freshFiber component insertedParent) source absent)

||| Project insertion guards BACK across a foreign insertion: absence of a
||| licensing edge excludes newly supplied parents; declaration disjointness
||| is a conjunction whose tail is the original registry condition.
export
0 o19InsertGuardsBeforeForeign :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (child : name) -> (insertedParent : Parent name) -> (insertedComponent : Component key value world error) ->
  (source : Registry name key value world error) ->
  (absent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Nothing) ->
  ((licensor : name) -> (parent = ChildOf licensor) -> Not (licensor = child)) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent
      (insertBinding @{nameEq} child (freshFiber insertedComponent insertedParent) source absent) &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq} (componentProvisions component)
      (bindings (insertBinding @{nameEq} child (freshFiber insertedComponent insertedParent) source absent)) = True) ->
  (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent source &&
    provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq}
      (componentProvisions component) (bindings source) = True)
o19InsertGuardsBeforeForeign {name} {key} {value} {world} {error} nameEq keyEq parent component child
  insertedParent insertedComponent (MkCoeffectContext entries unique) absent foreign valid =
    trans (boolAndCong
      (trans (sym (o19ParentBeforeForeignInsert nameEq parent child insertedParent insertedComponent
        (MkCoeffectContext entries unique) absent foreign))
        (boolAndLeft (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent (insertBinding @{nameEq} child (freshFiber insertedComponent insertedParent) (MkCoeffectContext entries unique) absent)) (provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq} (componentProvisions component) (bindings (insertBinding @{nameEq} child (freshFiber insertedComponent insertedParent) (MkCoeffectContext entries unique) absent))) valid))
      (boolAndRight (not (provisionOverlap @{keyEq} (componentProvisions component) (componentProvisions insertedComponent))) (provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq} (componentProvisions component) entries)
        (boolAndRight (parentPresent {name} {key} {value} {world} {error} @{nameEq} parent (insertBinding @{nameEq} child (freshFiber insertedComponent insertedParent) (MkCoeffectContext entries unique) absent)) (provisionsDisjointFrom {name} {key} {value} {world} {error} @{keyEq} (componentProvisions component) (bindings (insertBinding @{nameEq} child (freshFiber insertedComponent insertedParent) (MkCoeffectContext entries unique) absent))) valid))) Refl

||| At an explicit first insertion result, eliminate the ACTUAL second plan
||| and construct its checked early execution. Both domain and guard facts
||| come from this source plan, not from a selected desired target state.
export
0 o19RightInsertionBeforeObservedLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftChild, rightChild : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (leftAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} leftChild source = Nothing) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  ForeignInsertPlanView name key world error value nameEq keyEq rightChild rightParent rightComponent ambient
    (insertBinding @{nameEq} leftChild (freshFiber leftComponent leftParent) source leftAbsent) tag afterState ->
  Not (rightChild = leftChild) ->
  ((licensor : name) -> (rightParent = ChildOf licensor) -> Not (licensor = leftChild)) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (MkSystemState ambient source)
    (OInsert rightChild rightParent rightComponent) OInsertTag
o19RightInsertionBeforeObservedLeft nameEq keyEq leftChild rightChild leftParent rightParent
  leftComponent rightComponent ambient source leftAbsent _ _ (MkForeignInsertPlanView rightAbsent rightGuards)
  distinct foreign wellFormed =
    o19InsertFromAbsentGuards nameEq keyEq rightChild rightParent rightComponent ambient source
      (trans (sym (lookupInsertOther @{nameEq} rightChild leftChild distinct
        (freshFiber leftComponent leftParent) source leftAbsent)) rightAbsent)
      (o19InsertGuardsBeforeForeign nameEq keyEq rightParent rightComponent leftChild leftParent leftComponent
        source leftAbsent foreign rightGuards) wellFormed

||| Eliminate the original first plan once, then PRODUCE the actual second
||| plan at its exact reached registry before crossing the observed boundary.
export
0 o19InsertionBeforePairPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftChild, rightChild : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (middle, afterState : SystemState name key value world error) -> (leftTag, rightTag : RuleTag) ->
  ForeignInsertPlanView name key world error value nameEq keyEq leftChild leftParent leftComponent ambient source leftTag middle ->
  (checkedApplyAction @{nameEq} @{keyEq} (OInsert rightChild rightParent rightComponent) middle = Just (rightTag, afterState)) ->
  Not (rightChild = leftChild) ->
  ((licensor : name) -> (rightParent = ChildOf licensor) -> Not (licensor = leftChild)) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkSystemState ambient source) = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq (MkSystemState ambient source)
    (OInsert rightChild rightParent rightComponent) OInsertTag
o19InsertionBeforePairPlan nameEq keyEq leftChild rightChild leftParent rightParent leftComponent rightComponent
  ambient source _ afterState _ rightTag (MkForeignInsertPlanView leftAbsent leftGuards) rightChecked
  distinct foreign wellFormed =
    o19RightInsertionBeforeObservedLeft nameEq keyEq leftChild rightChild leftParent rightParent leftComponent rightComponent
      ambient source leftAbsent rightTag afterState
      (foreignInsertPlanView nameEq keyEq rightChild rightParent rightComponent ambient
        (insertBinding @{nameEq} leftChild (freshFiber leftComponent leftParent) source leftAbsent) rightTag afterState
        (checkedActionProjects nameEq keyEq (OInsert rightChild rightParent rightComponent)
          (MkSystemState ambient (insertBinding @{nameEq} leftChild (freshFiber leftComponent leftParent) source leftAbsent))
          afterState rightTag rightChecked)) distinct foreign wellFormed

||| Full actual-pair early O/O insertion producer. Both plans come from the
||| original checked edges; only the genuine child/licensing exclusions and
||| original well-formedness are required. No early-run/target oracle remains.
export
0 o19InsertionBeforeCheckedPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftChild, rightChild : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (before, middle, afterState : SystemState name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (checkedApplyAction @{nameEq} @{keyEq} (OInsert leftChild leftParent leftComponent) before = Just (leftTag, middle)) ->
  (checkedApplyAction @{nameEq} @{keyEq} (OInsert rightChild rightParent rightComponent) middle = Just (rightTag, afterState)) ->
  Not (rightChild = leftChild) ->
  ((licensor : name) -> (rightParent = ChildOf licensor) -> Not (licensor = leftChild)) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} before = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq before
    (OInsert rightChild rightParent rightComponent) OInsertTag
o19InsertionBeforeCheckedPair nameEq keyEq leftChild rightChild leftParent rightParent leftComponent rightComponent
  (MkSystemState ambient source) middle afterState leftTag rightTag leftChecked rightChecked distinct foreign wellFormed =
    o19InsertionBeforePairPlan nameEq keyEq leftChild rightChild leftParent rightParent leftComponent rightComponent
      ambient source middle afterState leftTag rightTag
      (foreignInsertPlanView nameEq keyEq leftChild leftParent leftComponent ambient source leftTag middle
        (checkedActionProjects nameEq keyEq (OInsert leftChild leftParent leftComponent)
          (MkSystemState ambient source) middle leftTag leftChecked))
      rightChecked distinct foreign wellFormed
