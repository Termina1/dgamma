module DGamma.CP5O20RootStageAttachmentSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5SupportedBirthCoverageSpike
import Data.Nat

%default total
%unbound_implicits off

||| One actual opposite root insertion together with its physical ordinal
||| equation, relative to the explicit right scanner offset. This packet
||| does not contain a paired stage sequence or an endpoint relation.
public export
record O20RootBirthMatch
  (name, key, world, error : Type) (value : key -> Type)
  (mapping : RegistrationGenerationBijection name)
  (root : name) (component : Component key value world error)
  (leftOrdinal, rightOrdinal : Nat)
  {rightFirst, rightFinal : SystemState name key value world error}
  (right : Transitions rightFirst rightFinal) where
  constructor MkO20RootBirthMatch
  0 matchedRootBirth : LocatedActionOccurrence (OInsert root Root component) right
  0 matchedRootOrdinal :
    (generationForward mapping (MkRegistrationGeneration root leftOrdinal) =
      MkRegistrationGeneration root (rightOrdinal + locatedActionOrdinal matchedRootBirth))

||| Prepending one physical right edge shifts the occurrence count, not its
||| absolute scanner stamp. The same located birth is extended structurally.
export
0 o20RootMatchPrepend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {mapping : RegistrationGenerationBijection name} ->
  {root : name} -> {component : Component key value world error} ->
  {leftOrdinal : Nat} -> (rightOrdinal : Nat) ->
  {rightFirst, rightMiddle, rightFinal : SystemState name key value world error} ->
  (step : Transition rightFirst rightMiddle) ->
  (rest : Transitions rightMiddle rightFinal) ->
  O20RootBirthMatch name key world error value mapping root component
    leftOrdinal (S rightOrdinal) rest ->
  O20RootBirthMatch name key world error value mapping root component
    leftOrdinal rightOrdinal (MoreTransitions step rest)
o20RootMatchPrepend {root} rightOrdinal step rest (MkO20RootBirthMatch birth exact) =
  MkO20RootBirthMatch
    (MkLocatedActionOccurrence (actionBeforeState birth) (actionAfterState birth)
      (MoreTransitions step (beforeActionOccurrence birth))
      (locatedTransition birth) (afterActionOccurrence birth) (locatedAction birth)
      (cong (MoreTransitions step) (actionOccurrenceDecomposition birth)))
    (trans exact (cong (MkRegistrationGeneration root)
      (plusSuccRightSucc rightOrdinal (locatedActionOrdinal birth))))

||| A matched external-root head supplies its own occurrence and stamp.
||| The explicit action equation transports the requested root/component.
export
0 o20RootMatchHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (mapping : RegistrationGenerationBijection name) ->
  (actual, root : name) ->
  (actualComponent, component : Component key value world error) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  {rightFirst, rightMiddle, rightFinal : SystemState name key value world error} ->
  (step : Transition rightFirst rightMiddle) ->
  (rest : Transitions rightMiddle rightFinal) ->
  (transitionAction step = OInsert actual Root actualComponent) ->
  (OInsert actual Root actualComponent = OInsert root Root component) ->
  (generationForward mapping (MkRegistrationGeneration actual leftOrdinal) =
    MkRegistrationGeneration actual rightOrdinal) ->
  O20RootBirthMatch name key world error value mapping root component
    (leftOrdinal + Z) rightOrdinal (MoreTransitions step rest)
o20RootMatchHead mapping actual _ actualComponent _ leftOrdinal rightOrdinal
  step rest action Refl matched =
  MkO20RootBirthMatch
    (MkLocatedActionOccurrence _ _ NoTransitions step rest action Refl)
    (trans (cong (\ordinal => generationForward mapping
      (MkRegistrationGeneration actual ordinal)) (plusZeroRightNeutral leftOrdinal))
      (trans matched (cong (MkRegistrationGeneration actual)
        (sym (plusZeroRightNeutral rightOrdinal)))))

||| Internal Nat eliminator for a non-root left head. Its recursive argument
||| is the tail induction result, not a canonical pairing assumption.
export
0 o20RootMatchSkipLeft :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (mapping : RegistrationGenerationBijection name) ->
  (leftOrdinal, rightOrdinal : Nat) ->
  {leftFirst, leftMiddle, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (step : Transition leftFirst leftMiddle) -> (rest : Transitions leftMiddle leftFinal) ->
  (right : Transitions rightFirst rightFinal) ->
  (action : Action name key value world error) ->
  (transitionAction step = action) -> (isExternalRootBirthAction action = False) ->
  (root : name) -> (component : Component key value world error) ->
  ((position : Nat) ->
    (rawClosingActionAt name key world error value position rest = Just (OInsert root Root component)) ->
    O20RootBirthMatch name key world error value mapping root component
      ((S leftOrdinal) + position) rightOrdinal right) ->
  (position : Nat) ->
  (rawClosingActionAt name key world error value position (MoreTransitions step rest) =
    Just (OInsert root Root component)) ->
  O20RootBirthMatch name key world error value mapping root component
    (leftOrdinal + position) rightOrdinal right
o20RootMatchSkipLeft {name} {key} {world} {error} {value} mapping leftOrdinal rightOrdinal
  step rest right action exact notRoot root component recurse Z observed =
  absurd (trans (sym (cong isExternalRootBirthAction
    (trans (sym exact) (coveredHeadActionObserved name key world error value
      step rest (OInsert root Root component) observed)))) notRoot)
o20RootMatchSkipLeft {name} {key} {world} {error} {value} mapping leftOrdinal rightOrdinal
  step rest right action exact notRoot root component recurse (S position) observed =
  replace {p = \ordinal => O20RootBirthMatch name key world error value mapping
    root component ordinal rightOrdinal right}
    (plusSuccRightSucc leftOrdinal position) (recurse position observed)
