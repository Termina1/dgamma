module DGamma.R9WholeBlockTwoByOnePositive

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

0 belowOneZero : LTE (S n) 1 -> n = 0
belowOneZero bound = case fromLteSucc bound of LTEZero => Refl

public export
data BelowTwo : Nat -> Type where
  BelowTwoZero : BelowTwo 0
  BelowTwoOne : BelowTwo 1

0 belowTwo : LTE (S n) 2 -> BelowTwo n
belowTwo bound with (fromLteSucc bound)
  _ | LTEZero = BelowTwoZero
  _ | LTESucc LTEZero = BelowTwoOne
  _ | LTESucc (LTESucc impossibleBound) impossible

0 labels21Complete : (leftPosition, rightPosition : Nat) ->
  LTE (S leftPosition) 2 -> LTE (S rightPosition) 1 ->
  Elem (leftPosition, rightPosition) [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]
labels21Complete leftPosition rightPosition leftBound rightBound =
  case belowOneZero rightBound of
    Refl => case belowTwo leftBound of
      BelowTwoZero => Here
      BelowTwoOne => There Here

0 elemTwo : Elem x [first, second] -> Either (x = first) (x = second)
elemTwo Here = Left Refl
elemTwo (There Here) = Right Refl
elemTwo (There (There later)) impossible

0 labels21Sound : (leftPosition, rightPosition : Nat) ->
  Elem (leftPosition, rightPosition)
    [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)] ->
  (LTE (S leftPosition) 2, LTE (S rightPosition) 1)
labels21Sound leftPosition rightPosition present =
  case elemTwo present of
    Left exact => replace
      {p = \pair => (LTE (S (fst pair)) 2, LTE (S (snd pair)) 1)}
      (sym exact) (LTESucc LTEZero, LTESucc LTEZero)
    Right exact => replace
      {p = \pair => (LTE (S (fst pair)) 2, LTE (S (snd pair)) 1)}
      (sym exact) (LTESucc (LTESucc LTEZero), LTESucc LTEZero)

0 pair00Not10 : Not (Elem (the Nat 0, the Nat 0) [(the Nat 1, the Nat 0)])
pair00Not10 Here impossible
pair00Not10 (There later) = noElemNil later

0 labels21Unique : UniqueKeys [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]
labels21Unique = UniqueCons pair00Not10 (UniqueCons noElemNil UniqueNil)

0 product21 : 2 * 1 = 2
product21 = Refl

||| Boundary producer for legitimate 2x1 blocks. It consumes exactly two actual
||| derivation nodes already labeled (0,0) and (1,0), then discharges every
||| Cartesian bound/coverage/uniqueness/count field without additional capital.
public export
0 twoByOneWholeBlockWitness :
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
  BlockCrossingOriginPlan name key world error value protocol nameEq keyEq
    sourceTrace
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety))
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety))
    (identityActionRegistrationReplayCorrespondence sourceTrace)
    (nonEmptyToFiniteAdjacentSwapDerivation derivation) [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)] ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap)
    (safetyLeftInOrder safety)) = 2 ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap)
    (safetyRightInOrder safety)) = 1 ->
  nonEmptyAdjacentSwapNodeCount derivation = 2 ->
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace
twoByOneWholeBlockWitness {sourceBlocks} {orderSwap} safety derivation labels
  leftTwo rightOne twoNodes =
    MkWholeBlockSwapDerivation derivation [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)] labels
      (\leftPosition, rightPosition, leftBound, rightBound =>
        labels21Complete leftPosition rightPosition
          (replace {p = \count => LTE (S leftPosition) count} leftTwo leftBound)
          (replace {p = \count => LTE (S rightPosition) count} rightOne rightBound))
      (\leftPosition, rightPosition, present =>
        let bounded = labels21Sound leftPosition rightPosition present in
          ( replace {p = \count => LTE (S leftPosition) count}
              (sym leftTwo) (fst bounded)
          , replace {p = \count => LTE (S rightPosition) count}
              (sym rightOne) (snd bounded)))
      labels21Unique
      (trans twoNodes (sym (trans
        (cong (\count => count * actorBlockTransitionCount
          (decomposedBlock sourceBlocks (actorRight orderSwap)
            (safetyRightInOrder safety))) leftTwo)
        (trans
          (cong (\count => 2 * count) rightOne)
          (multOneRightNeutral 2)))))
