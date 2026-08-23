module DGamma.R9WholeBlockSingletonPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 noElemNil : Elem x [] -> Void
noElemNil Here impossible
noElemNil (There later) impossible

0 indexBelowOneIsZero : LTE (S n) 1 -> n = 0
indexBelowOneIsZero bound = case fromLteSucc bound of
  LTEZero => Refl

0 pairZeroExact : (leftPosition, rightPosition : Nat) ->
  leftPosition = 0 -> rightPosition = 0 ->
  (leftPosition, rightPosition) = (the Nat 0, the Nat 0)
pairZeroExact 0 0 Refl Refl = Refl

0 singletonElemExact :
  (pair : (Nat, Nat)) -> Elem pair [(the Nat 0, the Nat 0)] ->
  pair = (the Nat 0, the Nat 0)
singletonElemExact (0, 0) Here = Refl
singletonElemExact pair (There later) = void (noElemNil later)

0 singletonComplete :
  (leftCount, rightCount : Nat) ->
  leftCount = 1 -> rightCount = 1 ->
  (leftPosition, rightPosition : Nat) ->
  LTE (S leftPosition) leftCount -> LTE (S rightPosition) rightCount ->
  Elem (leftPosition, rightPosition) [(the Nat 0, the Nat 0)]
singletonComplete leftCount rightCount leftOne rightOne leftPosition rightPosition
  leftBound rightBound =
    let leftZero = indexBelowOneIsZero (replace {p = \count => LTE (S leftPosition) count} leftOne leftBound)
        rightZero = indexBelowOneIsZero (replace {p = \count => LTE (S rightPosition) count} rightOne rightBound)
        pairExact = pairZeroExact leftPosition rightPosition leftZero rightZero
     in replace {p = \pair => Elem pair [(the Nat 0, the Nat 0)]} (sym pairExact) Here

0 singletonSound :
  (leftCount, rightCount : Nat) ->
  leftCount = 1 -> rightCount = 1 ->
  (leftPosition, rightPosition : Nat) ->
  Elem (leftPosition, rightPosition) [(the Nat 0, the Nat 0)] ->
  (LTE (S leftPosition) leftCount, LTE (S rightPosition) rightCount)
singletonSound leftCount rightCount leftOne rightOne leftPosition rightPosition
  present =
    case singletonElemExact (leftPosition, rightPosition) present of
      Refl => (replace {p = \count => LTE 1 count} (sym leftOne) (LTESucc LTEZero),
               replace {p = \count => LTE 1 count} (sym rightOne) (LTESucc LTEZero))

||| Positive singleton-block constructor. The caller supplies one actual finite
||| node and its action/tag labels; the Cartesian fields require exactly that one
||| (0,0) crossing and no overshoot node.
public export
0 singletonWholeBlockWitness :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {targetTrace : Transitions initial targetFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  (derivation : NonEmptyFiniteAdjacentSwapDerivation name key world error value
    protocol nameEq keyEq sourceTrace targetTrace) ->
  (labels : BlockCrossingOriginPlan name key world error value protocol
    nameEq keyEq sourceTrace
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety))
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety))
    (identityActionRegistrationReplayCorrespondence sourceTrace)
    (nonEmptyToFiniteAdjacentSwapDerivation derivation)
    [(the Nat 0, the Nat 0)]) ->
  actorBlockTransitionCount
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety)) = 1 ->
  actorBlockTransitionCount
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety)) = 1 ->
  nonEmptyAdjacentSwapNodeCount derivation = 1 ->
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace
singletonWholeBlockWitness {sourceBlocks} {orderSwap} safety derivation labels
  leftOne rightOne oneNode =
  MkWholeBlockSwapDerivation
    derivation
    [(the Nat 0, the Nat 0)]
    labels
    (singletonComplete
      (actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorLeft orderSwap) (safetyLeftInOrder safety)))
      (actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorRight orderSwap) (safetyRightInOrder safety)))
      leftOne rightOne)
    (singletonSound
      (actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorLeft orderSwap) (safetyLeftInOrder safety)))
      (actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorRight orderSwap) (safetyRightInOrder safety)))
      leftOne rightOne)
    (UniqueCons noElemNil UniqueNil)
    (trans oneNode (sym (trans
      (cong (\count => count * actorBlockTransitionCount
        (decomposedBlock sourceBlocks (actorRight orderSwap)
          (safetyRightInOrder safety))) leftOne)
      (trans
        (multOneLeftNeutral (actorBlockTransitionCount
          (decomposedBlock sourceBlocks (actorRight orderSwap)
            (safetyRightInOrder safety))))
        rightOne))))
