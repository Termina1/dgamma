module DGamma.R9WholeBlockTwoByTwoPositive

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

public export
data BelowTwo : Nat -> Type where
  BelowTwoZero : BelowTwo 0
  BelowTwoOne : BelowTwo 1

0 belowTwo : LTE (S n) 2 -> BelowTwo n
belowTwo bound with (fromLteSucc bound)
  _ | LTEZero = BelowTwoZero
  _ | LTESucc LTEZero = BelowTwoOne
  _ | LTESucc (LTESucc impossibleBound) impossible

0 labels22Complete : (leftPosition, rightPosition : Nat) ->
  LTE (S leftPosition) 2 -> LTE (S rightPosition) 2 ->
  Elem (leftPosition, rightPosition)
    [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
     (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]
labels22Complete leftPosition rightPosition leftBound rightBound =
  case belowTwo leftBound of
    BelowTwoZero => case belowTwo rightBound of
      BelowTwoZero => Here
      BelowTwoOne => There Here
    BelowTwoOne => case belowTwo rightBound of
      BelowTwoZero => There (There Here)
      BelowTwoOne => There (There (There Here))

0 elemFour : Elem x [first, second, third, fourth] ->
  Either (x = first) (Either (x = second) (Either (x = third) (x = fourth)))
elemFour Here = Left Refl
elemFour (There Here) = Right (Left Refl)
elemFour (There (There Here)) = Right (Right (Left Refl))
elemFour (There (There (There Here))) = Right (Right (Right Refl))
elemFour (There (There (There (There later)))) impossible

0 labels22Sound : (leftPosition, rightPosition : Nat) ->
  Elem (leftPosition, rightPosition)
    [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
     (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)] ->
  (LTE (S leftPosition) 2, LTE (S rightPosition) 2)
labels22Sound leftPosition rightPosition present =
  case elemFour present of
    Left exact => replace
      {p = \pair => (LTE (S (fst pair)) 2, LTE (S (snd pair)) 2)}
      (sym exact) (LTESucc LTEZero, LTESucc LTEZero)
    Right (Left exact) => replace
      {p = \pair => (LTE (S (fst pair)) 2, LTE (S (snd pair)) 2)}
      (sym exact) (LTESucc LTEZero, LTESucc (LTESucc LTEZero))
    Right (Right (Left exact)) => replace
      {p = \pair => (LTE (S (fst pair)) 2, LTE (S (snd pair)) 2)}
      (sym exact) (LTESucc (LTESucc LTEZero), LTESucc LTEZero)
    Right (Right (Right exact)) => replace
      {p = \pair => (LTE (S (fst pair)) 2, LTE (S (snd pair)) 2)}
      (sym exact)
      (LTESucc (LTESucc LTEZero), LTESucc (LTESucc LTEZero))

0 aAbsent : Not (Elem (the Nat 0, the Nat 0)
  [(the Nat 0, the Nat 1), (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)])
aAbsent Here impossible
aAbsent (There Here) impossible
aAbsent (There (There Here)) impossible
aAbsent (There (There (There later))) = noElemNil later

0 bAbsent : Not (Elem (the Nat 0, the Nat 1)
  [(the Nat 1, the Nat 0), (the Nat 1, the Nat 1)])
bAbsent Here impossible
bAbsent (There Here) impossible
bAbsent (There (There later)) = noElemNil later

0 cAbsent : Not (Elem (the Nat 1, the Nat 0) [(the Nat 1, the Nat 1)])
cAbsent Here impossible
cAbsent (There later) = noElemNil later

0 labels22Unique : UniqueKeys
  [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
   (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]
labels22Unique = UniqueCons aAbsent
  (UniqueCons bAbsent (UniqueCons cAbsent (UniqueCons noElemNil UniqueNil)))

0 product22 : 2 * 2 = S (S (S (S Z)))
product22 = Refl

||| Boundary producer for a legitimate 2x2 crossing. Four actual nodes and four
||| exact labels discharge the strengthened record with no additional invariant.
public export
0 twoByTwoWholeBlockWitness :
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
    (nonEmptyToFiniteAdjacentSwapDerivation derivation)
    [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
     (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)] ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap)
    (safetyLeftInOrder safety)) = 2 ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap)
    (safetyRightInOrder safety)) = 2 ->
  nonEmptyAdjacentSwapNodeCount derivation = S (S (S (S Z))) ->
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace
twoByTwoWholeBlockWitness {sourceBlocks} {orderSwap} safety derivation labels
  leftTwo rightTwo fourNodes =
    MkWholeBlockSwapDerivation derivation
      [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
       (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]
      labels
      (\leftPosition, rightPosition, leftBound, rightBound =>
        labels22Complete leftPosition rightPosition
          (replace {p = \count => LTE (S leftPosition) count} leftTwo leftBound)
          (replace {p = \count => LTE (S rightPosition) count} rightTwo rightBound))
      (\leftPosition, rightPosition, present =>
        let bounded = labels22Sound leftPosition rightPosition present in
          ( replace {p = \count => LTE (S leftPosition) count}
              (sym leftTwo) (fst bounded)
          , replace {p = \count => LTE (S rightPosition) count}
              (sym rightTwo) (snd bounded)))
      labels22Unique
      (trans fourNodes (sym (trans
        (cong (\count => count * actorBlockTransitionCount
          (decomposedBlock sourceBlocks (actorRight orderSwap)
            (safetyRightInOrder safety))) leftTwo)
        (trans (cong (\count => 2 * count) rightTwo) product22))))
