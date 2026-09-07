module DGamma.CP5O19ActivationRowSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19OpeningPropagationSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| One observed row boundary: the moved right activation is now immediately
||| after the exact untouched prefix. The actual reached bundle, uniqueness,
||| derivation and its structural node count belong to this SAME output.
||| This does not yet assert a whole Cartesian plan or installed target blocks.
public export
record O19ActivationRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal)
  (earlier : Transitions initial before)
  (sourceRight : Transition rightBefore rightAfter)
  (crossings : Nat) where
  constructor MkO19ActivationRow
  rowCursor : O19ReachedCursor name key world error value protocol nameEq keyEq source
  rowMiddle : SystemState name key value world error
  rowRight : Transition before rowMiddle
  rowRest : Transitions rowMiddle (cursorFinal rowCursor)
  0 rowDecomposition : appendTransitions earlier (MoreTransitions rowRight rowRest) = cursorTrace rowCursor
  0 rowAction : transitionAction rowRight = transitionAction sourceRight
  0 rowTag : transitionTag rowRight = transitionTag sourceRight
  0 rowActor : transitionActor rowRight = transitionActor sourceRight
  0 rowActivation : PaperActivationStep rowRight
  0 rowNodeCount : finiteAdjacentSwapNodeCount (cursorDerivation rowCursor) = crossings

||| Construct the zero-row boundary together with its count. Refl here sees
||| only the finite Done constructor, never a separately evaluated builder.
export
0 o19ActivationRowZero :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (right : Transition before rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (MoreTransitions right later) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  PaperActivationStep right ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier right 0
o19ActivationRowZero {sourceFinal} {rightAfter} nameEq keyEq protocol source earlier
  right later decomposition premises unique activation =
    MkO19ActivationRow
      (MkO19ReachedCursor sourceFinal source premises unique FiniteAdjacentSwapDone)
      rightAfter right later decomposition Refl Refl Refl activation Refl

||| Consume an EXPLICIT produced diamond/result, extending its own exact
||| trace and the original derivation simultaneously. The count proof is
||| structural append addition; no scalar observer inspects a replay builder.
export
0 o19ActivationRowStepObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal, before, middle, rightBefore, rightAfter : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial before) ->
  (left : Transition before middle) -> (sourceRight : Transition rightBefore rightAfter) ->
  (crossings : Nat) ->
  (previous : O19ActivationRow name key world error value protocol nameEq keyEq source
    (appendTransitions earlier (MoreTransitions left NoTransitions)) sourceRight crossings) ->
  (leftActivation : PaperActivationStep left) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left (rowRight previous) **
    AdjacentSwapResult name key world error value protocol nameEq keyEq
      (cursorTrace (rowCursor previous)) earlier left (rowRight previous) (rowRest previous) diamond) ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier sourceRight (S crossings)
o19ActivationRowStepObserved {name} {key} {world} {error} {value}
  nameEq keyEq protocol source earlier left sourceRight crossings previous
  leftActivation (diamond ** result) =
    MkO19ActivationRow
      (MkO19ReachedCursor (replayedFinal result) (swappedTrace result) (swappedPremises result)
        (uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
          (FiniteAdjacentSwapStep (cursorTrace (rowCursor previous)) earlier left
          (rowRight previous) (rowRest previous)
          (AdjacentActivationActivation left (rowRight previous) leftActivation (rowActivation previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone) (cursorUnique (rowCursor previous)))
        (o19AppendFinite (cursorDerivation (rowCursor previous)) (FiniteAdjacentSwapStep (cursorTrace (rowCursor previous)) earlier left
          (rowRight previous) (rowRest previous)
          (AdjacentActivationActivation left (rowRight previous) leftActivation (rowActivation previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone)))
      (swappedMiddle diamond) (movedRight diamond)
      (MoreTransitions (movedLeft diamond) (replayedSuffix result))
      (sym (swappedDecomposition result))
      (trans (movedRightAction diamond) (rowAction previous))
      (trans (movedRightTag diamond) (rowTag previous))
      (trans (o19TransitionActorOwner (movedRight diamond))
        (trans (cong actionOwner (trans (movedRightAction diamond) (rowAction previous)))
          (sym (o19TransitionActorOwner sourceRight))))
      (movedRightActivationBranch diamond (rowActivation previous))
      (trans (o19AppendFiniteCount (cursorDerivation (rowCursor previous)) (FiniteAdjacentSwapStep (cursorTrace (rowCursor previous)) earlier left
          (rowRight previous) (rowRest previous)
          (AdjacentActivationActivation left (rowRight previous) leftActivation (rowActivation previous))
          diamond result (swappedTrace result) FiniteAdjacentSwapDone))
        (trans (cong (\count => count + 1) (rowNodeCount previous))
          (plusCommutative crossings 1)))
