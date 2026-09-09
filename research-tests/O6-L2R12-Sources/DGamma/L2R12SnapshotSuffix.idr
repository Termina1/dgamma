module DGamma.L2R12SnapshotSuffix

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.L2R2CheckedSnapshot
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Native aligned suffix replay from any well-formed snapshot-equal source.
||| Every alternate edge is produced by checkedAcrossSnapshot; no callback
||| or unchanged resolver is a premise. CPS avoids computed existential views.
export
0 replaySnapshotSuffixCPS : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (first, finalState : SystemState name key value world error) ->
  (trace : Transitions first finalState) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  (current : SystemState name key value world error) ->
  (0 same : runtimeSnapshot current = runtimeSnapshot first) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} current = True) ->
  (0 answer : Type) ->
  (0 done : (target : SystemState name key value world error) ->
    (replayed : Transitions current target) ->
    transitionCount replayed = transitionCount trace ->
    runtimeSnapshot target = runtimeSnapshot finalState ->
    registryWellFormed @{nameEq} @{keyEq} target = True -> answer) -> answer
replaySnapshotSuffixCPS nameEq keyEq _ _ _ AlignedEnd current same valid answer done =
  done current NoTransitions Refl same valid
replaySnapshotSuffixCPS nameEq keyEq first finalState _
  (AlignedStep {middle} action tag checked rest later) current same valid answer done =
  replaySnapshotSuffixCPS nameEq keyEq middle finalState rest later
    (snapshotAfter (checkedAcrossSnapshot nameEq keyEq action tag first middle current checked (sym same) valid))
    (snapshotExact (checkedAcrossSnapshot nameEq keyEq action tag first middle current checked (sym same) valid))
    (checkedActionTargetValid nameEq keyEq action current
      (snapshotAfter (checkedAcrossSnapshot nameEq keyEq action tag first middle current checked (sym same) valid)) tag
      (snapshotChecked (checkedAcrossSnapshot nameEq keyEq action tag first middle current checked (sym same) valid)))
    answer (\target, replayed, count, endpoint, targetValid => done target
      (MoreTransitions (Fired {before = current}
        {afterState = snapshotAfter (checkedAcrossSnapshot nameEq keyEq action tag first middle current checked (sym same) valid)}
        nameEq keyEq action tag
        (snapshotChecked (checkedAcrossSnapshot nameEq keyEq action tag first middle current checked (sym same) valid))) replayed)
      (cong S count) endpoint targetValid)
