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
