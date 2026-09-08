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
