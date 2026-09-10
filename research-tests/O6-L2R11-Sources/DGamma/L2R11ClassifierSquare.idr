module DGamma.L2R11ClassifierSquare

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4InsertReplay
import DGamma.L2R5Extensional
import DGamma.L2R5CurrentCut
import DGamma.L2R6Iteration
import DGamma.L2R5RootCatalog
import DGamma.L2R10MoveCutObservation
import DGamma.L2R9ControlClass
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A genuine local early-root crossing square with extensional endpoint.
||| This is NOT an AdmittedDistanceMove: physical whole-word adjacency,
||| forcing, phase/NeverRetired/uniqueness transport and decrement are separate.
public export
record ClassifierSquare
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (root : name) (component : Component key value world error)
  (source : SystemState name key value world error)
  (action : Action name key value world error) (tag : RuleTag)
  (oldFinal : SystemState name key value world error) where
  constructor MkClassifierSquare
  squareMiddle : SystemState name key value world error
  squareFinal : SystemState name key value world error
  0 earlyChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) source = Just (OInsertTag, squareMiddle)
  0 laterChecked : checkedApplyAction @{nameEq} @{keyEq} action squareMiddle = Just (tag, squareFinal)
  0 squareAdmitted : AdmittedCrossing nameEq root source action
  0 squareCurrentCut : DGamma.CP5AvailabilityAwarePlacement.rootDeclaredProvisionsFree name key world error value keyEq component source = True
  0 squareEndpoint : RegistryExtensional name key world error value nameEq oldFinal squareFinal

||| Match a produced checked snapshot packet against a known native edge
||| at the SAME source/action/tag. Only the packet is eliminated.
export
0 snapshotPacketMatches : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (source, target : SystemState name key value world error) ->
  (expected : RuntimeSnapshot name key world error value) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action source = Just (tag, target)) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action source tag expected ->
  runtimeSnapshot target = expected
snapshotPacketMatches nameEq keyEq action tag source target expected checked
  (MkCheckedSnapshotStep afterState produced exact) =
  trans (cong runtimeSnapshot (cong snd (justInjective (trans (sym checked) produced)))) exact

||| Recover the canonical retirement snapshot from the original checked
||| Retire edge and its native installed fiber, not a supplied state equality.
export
0 originalRetireSnapshot : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) before = Just (ORetireTag, afterState)) ->
  runtimeSnapshot afterState = runtimeSnapshot {name} {key} {value} {world} {error}
    (MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber fiber) (registry before)))
originalRetireSnapshot nameEq keyEq child fiber before afterState found valid original =
  cong runtimeSnapshot (cong snd (justInjective (trans (sym original)
    (childRetireAtFound nameEq keyEq child fiber before found valid))))

||| GENUINE foreign-own-child Retire/root local square. The source-aware
||| classifier facts and original pair authenticate the crossing. Only early
||| root applicability is additionally required (the selected request observes
||| it); the late Retire and extensional endpoint are PRODUCED, not assumed.
export
0 produceRetireClassifierSquare : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, root : name) ->
  (fiber : Fiber name key value world error) -> (component : Component key value world error) ->
  (before, retiredState, oldFinal, earlyRoot : SystemState name key value world error) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just fiber) ->
  (0 ownChild : fiberParent fiber = ChildOf parent) ->
  (0 parentForeign : Not (parent = root)) -> (0 childDifferent : Not (child = root)) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 retired : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) before = Just (ORetireTag, retiredState)) ->
  (0 oldRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) retiredState = Just (OInsertTag, oldFinal)) ->
  (0 early : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) before = Just (OInsertTag, earlyRoot)) ->
  ClassifierSquare name key world error value nameEq keyEq root component before (ORetire child) ORetireTag oldFinal
produceRetireClassifierSquare nameEq keyEq child parent root fiber component before retiredState oldFinal earlyRoot
  found ownChild parentForeign childDifferent valid retired oldRoot early =
  MkClassifierSquare earlyRoot
    (MkSystemState (worldState earlyRoot) (replaceBinding @{nameEq} child (retireFiber fiber) (registry earlyRoot)))
    early
    (childRetireAtFound nameEq keyEq child fiber earlyRoot
      (trans (childForeignLookupFrame nameEq keyEq child (OInsert root Root component) OInsertTag early childDifferent) found)
      (checkedActionTargetValid nameEq keyEq (OInsert root Root component) before earlyRoot OInsertTag early))
    (CrossChildRetire fiber found ownChild parentForeign)
    (checkedRootCurrentAvailable nameEq keyEq root component before earlyRoot OInsertTag early)
    (snapshotIntoExtensional nameEq oldFinal
      (MkSystemState (worldState earlyRoot) (replaceBinding @{nameEq} child (retireFiber fiber) (registry earlyRoot)))
      (snapshotPacketMatches nameEq keyEq (OInsert root Root component) OInsertTag retiredState oldFinal
        (runtimeSnapshot (MkSystemState (worldState earlyRoot) (replaceBinding @{nameEq} child (retireFiber fiber) (registry earlyRoot))))
        oldRoot
        (replayInsertAfterRetirement nameEq keyEq child root Root fiber component before earlyRoot retiredState OInsertTag
          early childDifferent found valid
          (checkedActionTargetValid nameEq keyEq (ORetire child) before retiredState ORetireTag retired)
          (originalRetireSnapshot nameEq keyEq child fiber before retiredState found valid retired))))

||| Successful early insertion produces name freshness against every actual
||| installed child. This needs no assumption that parent-distinct implies
||| child-distinct and no initially-installed birth provenance oracle.
export
0 earlyRootDistinctFromChild : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, root : name) ->
  (fiber : Fiber name key value world error) -> (component : Component key value world error) ->
  (before, earlyRoot : SystemState name key value world error) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just fiber) ->
  (0 early : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) before = Just (OInsertTag, earlyRoot)) ->
  Not (child = root)
earlyRootDistinctFromChild {name} {key} {world} {error} {value}
  nameEq keyEq child root fiber component (MkSystemState ambient source) earlyRoot found early same =
  nothingIsNotJust (trans (sym (foreignInsertViewAbsent
    (foreignInsertPlanView nameEq keyEq root Root component ambient source OInsertTag earlyRoot
      (checkedActionProjects nameEq keyEq (OInsert root Root component) (MkSystemState ambient source) earlyRoot OInsertTag early))))
    (trans (sym (cong (\wanted => lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted source) same)) found))

||| Classifier-case square production. ONLY the foreign own-child case is
||| accepted; missing, root and local-child controls remain explicit Nothing.
||| Child/root inequality is derived from early insertion, not an input.
export
0 retireSquareOnClassifier : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, root : name) ->
  (component : Component key value world error) ->
  (before, retiredState, oldFinal, earlyRoot : SystemState name key value world error) ->
  (classification : ControlClass nameEq root child before) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 retired : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) before = Just (ORetireTag, retiredState)) ->
  (0 oldRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) retiredState = Just (OInsertTag, oldFinal)) ->
  (0 early : checkedApplyAction @{nameEq} @{keyEq} (OInsert root Root component) before = Just (OInsertTag, earlyRoot)) ->
  Maybe (ClassifierSquare name key world error value nameEq keyEq root component before (ORetire child) ORetireTag oldFinal)
retireSquareOnClassifier nameEq keyEq child root component before retiredState oldFinal earlyRoot
  (MissingControl missing) valid retired oldRoot early = Nothing
retireSquareOnClassifier nameEq keyEq child root component before retiredState oldFinal earlyRoot
  (RootControl fiber found parent) valid retired oldRoot early = Nothing
retireSquareOnClassifier nameEq keyEq child root component before retiredState oldFinal earlyRoot
  (LocalChildControl fiber found parent) valid retired oldRoot early = Nothing
retireSquareOnClassifier nameEq keyEq child root component before retiredState oldFinal earlyRoot
  (ForeignChildControl parent fiber found own foreign) valid retired oldRoot early =
  Just (produceRetireClassifierSquare nameEq keyEq child parent root fiber component before retiredState oldFinal earlyRoot
    found own foreign (earlyRootDistinctFromChild nameEq keyEq child root fiber component before earlyRoot found early)
    valid retired oldRoot early)

||| Retire branch of the ACTUAL selected request. Native early applicability
||| is recovered by trans from its producer-owned observed result equation.
||| The original two edges at this source are still explicit: linking their
||| adjacency/dictionaries to selectedCutLocated is a separate obligation.
export
0 selectedRetireSquare : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) ->
  (cut : SelectedSquareCut name key world error value nameEq keyEq trail) -> (child : name) ->
  (0 selectedAction : cutAction cut = ORetire child) ->
  (retiredState, oldFinal, earlyRoot : SystemState name key value world error) ->
  (0 accepted : earlyRootResult cut = Just (OInsertTag, earlyRoot)) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} (cutSource cut) = True) ->
  (0 retired : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) (cutSource cut) = Just (ORetireTag, retiredState)) ->
  (0 oldRoot : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert (catalogRoot (cutEntry cut)) Root (catalogComponent (cutEntry cut))) retiredState = Just (OInsertTag, oldFinal)) ->
  Maybe (ClassifierSquare name key world error value nameEq keyEq
    (catalogRoot (cutEntry cut)) (catalogComponent (cutEntry cut)) (cutSource cut) (cutAction cut) ORetireTag oldFinal)
selectedRetireSquare {name} {key} {world} {error} {value}
  nameEq keyEq trail cut child selectedAction retiredState oldFinal earlyRoot accepted valid retired oldRoot =
  replace {p = \action => Maybe (ClassifierSquare name key world error value nameEq keyEq
      (catalogRoot (cutEntry cut)) (catalogComponent (cutEntry cut)) (cutSource cut) action ORetireTag oldFinal)}
    (sym selectedAction)
    (retireSquareOnClassifier nameEq keyEq child (catalogRoot (cutEntry cut)) (catalogComponent (cutEntry cut))
      (cutSource cut) retiredState oldFinal earlyRoot
      (controlAtLookup nameEq (catalogRoot (cutEntry cut)) child (cutSource cut)
        (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry (cutSource cut))) Refl)
      valid retired oldRoot (trans (earlyRootEquation cut) accepted))
