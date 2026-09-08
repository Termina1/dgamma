module DGamma.L2R2CheckedSnapshot

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RuntimeBindings
import DGamma.CP4ProgressNoDeadlock
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A native checked successor plus exact world/ordered-bindings observation.
||| Runtime state is retained; the evaluator equation and snapshot equality are
||| erased. Auxiliary CP4RuntimeBindings:12/21-style result, not a CP3 copy.
public export
record CheckedSnapshotStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (source : SystemState name key value world error)
  (expectedTag : RuleTag)
  (expectedSnapshot : RuntimeSnapshot name key world error value) where
  constructor MkCheckedSnapshotStep
  snapshotAfter : SystemState name key value world error
  0 snapshotChecked : checkedApplyAction @{nameEq} @{keyEq} action source =
    Just (expectedTag, snapshotAfter)
  0 snapshotExact : runtimeSnapshot snapshotAfter = expectedSnapshot

||| Eliminate one explicit raw evaluator result. A successful runtime snapshot
||| forces native success; raw Preservation supplies the checked successor.
||| No desired-state equality or successful replay is assumed as an extra input.
export
0 checkedSnapshotObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (source : SystemState name key value world error) ->
  (expectedTag : RuleTag) ->
  (expected : RuntimeSnapshot name key world error value) ->
  (observed : Maybe (RuleTag, SystemState name key value world error)) ->
  (0 raw : applyAction @{nameEq} @{keyEq} action source = observed) ->
  (0 exact : observeActionResult observed = Just (expectedTag, expected)) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} source = True) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action source expectedTag expected
checkedSnapshotObserved nameEq keyEq action source expectedTag expected Nothing raw exact valid =
  void (nothingIsNotJust exact)
checkedSnapshotObserved {name} {key} {world} {error} {value}
  nameEq keyEq action source expectedTag expected (Just (tag, afterState)) raw exact valid =
  replace {p = \chosen => CheckedSnapshotStep name key world error value nameEq keyEq action source chosen expected}
    (cong fst (justInjective exact))
    (MkCheckedSnapshotStep afterState
      (checkedFromRaw nameEq keyEq action source afterState tag valid raw)
      (cong snd (justInjective exact)))

||| Transport one existing checked native edge to a well-formed source with
||| exactly the same runtime snapshot. The source may own different erased
||| uniqueness proofs. Both the successful target and its checked equation are
||| produced by observation coherence, not supplied by a replay callback.
export
0 checkedAcrossSnapshot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (originalSource, originalAfter, current : SystemState name key value world error) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action originalSource = Just (tag, originalAfter)) ->
  (0 same : runtimeSnapshot originalSource = runtimeSnapshot current) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  CheckedSnapshotStep name key world error value nameEq keyEq action current tag (runtimeSnapshot originalAfter)
checkedAcrossSnapshot nameEq keyEq action tag originalSource originalAfter current checked same valid =
  checkedSnapshotObserved nameEq keyEq action current tag (runtimeSnapshot originalAfter)
    (applyAction @{nameEq} @{keyEq} action current) Refl
    (trans (sym (applyActionObservationCoherent nameEq keyEq action originalSource current same))
      (cong observeActionResult (checkedActionProjects nameEq keyEq action originalSource originalAfter tag checked))) valid
