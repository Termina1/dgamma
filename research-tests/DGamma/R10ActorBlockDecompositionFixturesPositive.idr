module DGamma.R10ActorBlockDecompositionFixturesPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 noBeforeSingleton : BeforeIn earlier later [only] -> Void
noBeforeSingleton (BeforeHere Here) impossible
noBeforeSingleton (BeforeHere (There rest)) impossible
noBeforeSingleton (BeforeThere later) impossible

0 elemSingletonEquality : Elem left [right] -> left = right
elemSingletonEquality Here = Refl
elemSingletonEquality (There later) impossible

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

0 zeroNotOne : Not (the Nat 0 = 1)
zeroNotOne Refl impossible
0 zeroNotTwo : Not (the Nat 0 = 2)
zeroNotTwo Refl impossible
0 zeroNotThree : Not (the Nat 0 = 3)
zeroNotThree Refl impossible
0 oneNotTwo : Not (the Nat 1 = 2)
oneNotTwo Refl impossible
0 oneNotThree : Not (the Nat 1 = 3)
oneNotThree Refl impossible

||| A concrete two-entry decomposition assembler.  The 1x1 range law is proved
||| from exact starts/counts; it is not a premise.
public export
0 actorBlocksOneByOne :
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (leftActor, rightActor : name) ->
  Not (leftActor = rightActor) ->
  (blocks : (n : name) -> Elem n [leftActor, rightActor] ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n trace) ->
  ((earlier, later : name) ->
    (earlierIn : Elem earlier [leftActor, rightActor]) ->
    (laterIn : Elem later [leftActor, rightActor]) ->
    BeforeIn earlier later [leftActor, rightActor] ->
    BlockBefore name key world error value nameEq keyEq trace earlier later
      (blocks earlier earlierIn) (blocks later laterIn)) ->
  LifecycleActorsCovered [leftActor, rightActor] trace ->
  transitionCount (traceBeforeBlock {global = trace} (blocks leftActor Here)) = 0 ->
  transitionCount (traceBeforeBlock {global = trace} (blocks rightActor (There Here))) = 1 ->
  actorBlockTransitionCount (blocks leftActor Here) = 1 ->
  actorBlockTransitionCount (blocks rightActor (There Here)) = 1 ->
  ActorBlockDecomposition name key world error value nameEq keyEq
    [leftActor, rightActor] trace
actorBlocksOneByOne leftActor rightActor distinct blocks ordered covered leftStart rightStart
  leftCount rightCount =
  MkActorBlockDecomposition blocks ordered ranges covered
  where
  0 ranges : (earlier, later : name) ->
    (earlierIn : Elem earlier [leftActor, rightActor]) ->
    (laterIn : Elem later [leftActor, rightActor]) ->
    BeforeIn earlier later [leftActor, rightActor] ->
    (earlierPosition, laterPosition : Nat) ->
    LTE (S earlierPosition)
      (S (transitionCount (blockBody {global = trace} (blocks earlier earlierIn)))) ->
    LTE (S laterPosition)
      (S (transitionCount (blockBody {global = trace} (blocks later laterIn)))) ->
    Not (transitionCount (traceBeforeBlock {global = trace} (blocks earlier earlierIn)) +
      earlierPosition =
      transitionCount (traceBeforeBlock {global = trace} (blocks later laterIn)) + laterPosition)
  ranges _ _ Here (There Here) (BeforeHere Here)
    earlierPosition laterPosition earlierBound laterBound exact =
      let earlierZero = belowOneZero
            (replace {p = \count => LTE (S earlierPosition) count}
              leftCount earlierBound)
          laterZero = belowOneZero
            (replace {p = \count => LTE (S laterPosition) count}
              rightCount laterBound)
          leftStarted = replace {p = \start => start + earlierPosition =
            transitionCount (traceBeforeBlock {global = trace}
              (blocks rightActor (There Here))) + laterPosition}
            leftStart exact
          bothStarted = replace {p = \start => 0 + earlierPosition =
            start + laterPosition} rightStart leftStarted
          leftPositioned = replace {p = \position => 0 + position =
            1 + laterPosition} earlierZero bothStarted
          normalized = replace {p = \position => 0 = 1 + position}
            laterZero leftPositioned
       in zeroNotOne normalized
  ranges _ _ Here (There Here) (BeforeThere before)
    earlierPosition laterPosition earlierBound laterBound exact =
      void (noBeforeSingleton before)
  ranges _ _ Here Here before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere same => void (distinct (elemSingletonEquality same))
        BeforeThere tail => void (noBeforeSingleton tail)
  ranges _ _ (There Here) (There Here) before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere later => void (distinct Refl)
        BeforeThere tail => void (noBeforeSingleton tail)
  ranges _ _ (There Here) Here before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere later => void (distinct Refl)
        BeforeThere tail => void (noBeforeSingleton tail)

||| 2x1 range arithmetic: exact positions are (0|1) versus 2.
public export
0 actorBlocksTwoByOne :
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (leftActor, rightActor : name) ->
  Not (leftActor = rightActor) ->
  (blocks : (n : name) -> Elem n [leftActor, rightActor] ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n trace) ->
  ((earlier, later : name) ->
    (earlierIn : Elem earlier [leftActor, rightActor]) ->
    (laterIn : Elem later [leftActor, rightActor]) ->
    BeforeIn earlier later [leftActor, rightActor] ->
    BlockBefore name key world error value nameEq keyEq trace earlier later
      (blocks earlier earlierIn) (blocks later laterIn)) ->
  LifecycleActorsCovered [leftActor, rightActor] trace ->
  transitionCount (traceBeforeBlock {global = trace} (blocks leftActor Here)) = 0 ->
  transitionCount (traceBeforeBlock {global = trace} (blocks rightActor (There Here))) = 2 ->
  actorBlockTransitionCount (blocks leftActor Here) = 2 ->
  actorBlockTransitionCount (blocks rightActor (There Here)) = 1 ->
  ActorBlockDecomposition name key world error value nameEq keyEq
    [leftActor, rightActor] trace
actorBlocksTwoByOne leftActor rightActor distinct blocks ordered covered leftStart rightStart
  leftCount rightCount =
  MkActorBlockDecomposition blocks ordered ranges covered
  where
  0 ranges : (earlier, later : name) ->
    (earlierIn : Elem earlier [leftActor, rightActor]) ->
    (laterIn : Elem later [leftActor, rightActor]) ->
    BeforeIn earlier later [leftActor, rightActor] ->
    (earlierPosition, laterPosition : Nat) ->
    LTE (S earlierPosition)
      (S (transitionCount (blockBody {global = trace} (blocks earlier earlierIn)))) ->
    LTE (S laterPosition)
      (S (transitionCount (blockBody {global = trace} (blocks later laterIn)))) ->
    Not (transitionCount (traceBeforeBlock {global = trace} (blocks earlier earlierIn)) +
      earlierPosition =
      transitionCount (traceBeforeBlock {global = trace} (blocks later laterIn)) + laterPosition)
  ranges _ _ Here (There Here) (BeforeHere Here)
    earlierPosition laterPosition earlierBound laterBound exact =
      let earlierSmall = belowTwo
            (replace {p = \count => LTE (S earlierPosition) count}
              leftCount earlierBound)
          laterZero = belowOneZero
            (replace {p = \count => LTE (S laterPosition) count}
              rightCount laterBound)
          leftStarted = replace {p = \start => start + earlierPosition =
            transitionCount (traceBeforeBlock {global = trace}
              (blocks rightActor (There Here))) + laterPosition}
            leftStart exact
          bothStarted = replace {p = \start => 0 + earlierPosition =
            start + laterPosition} rightStart leftStarted
          normalized = replace {p = \position => 0 + earlierPosition =
            2 + position} laterZero bothStarted
       in case earlierSmall of
            BelowTwoZero => zeroNotTwo normalized
            BelowTwoOne => oneNotTwo normalized
  ranges _ _ Here (There Here) (BeforeThere before)
    earlierPosition laterPosition earlierBound laterBound exact =
      void (noBeforeSingleton before)
  ranges _ _ Here Here before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere same => void (distinct (elemSingletonEquality same))
        BeforeThere tail => void (noBeforeSingleton tail)
  ranges _ _ (There Here) (There Here) before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere later => void (distinct Refl)
        BeforeThere tail => void (noBeforeSingleton tail)
  ranges _ _ (There Here) Here before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere later => void (distinct Refl)
        BeforeThere tail => void (noBeforeSingleton tail)

||| Repeated-Iter 2x2 geometry: the selected positions (0|1) inhabit disjoint
||| coordinate ranges 0..1 and 2..3.
public export
0 actorBlocksTwoByTwo :
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (leftActor, rightActor : name) ->
  Not (leftActor = rightActor) ->
  (blocks : (n : name) -> Elem n [leftActor, rightActor] ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n trace) ->
  ((earlier, later : name) ->
    (earlierIn : Elem earlier [leftActor, rightActor]) ->
    (laterIn : Elem later [leftActor, rightActor]) ->
    BeforeIn earlier later [leftActor, rightActor] ->
    BlockBefore name key world error value nameEq keyEq trace earlier later
      (blocks earlier earlierIn) (blocks later laterIn)) ->
  LifecycleActorsCovered [leftActor, rightActor] trace ->
  transitionCount (traceBeforeBlock {global = trace} (blocks leftActor Here)) = 0 ->
  transitionCount (traceBeforeBlock {global = trace} (blocks rightActor (There Here))) = 2 ->
  actorBlockTransitionCount (blocks leftActor Here) = 2 ->
  actorBlockTransitionCount (blocks rightActor (There Here)) = 2 ->
  ActorBlockDecomposition name key world error value nameEq keyEq
    [leftActor, rightActor] trace
actorBlocksTwoByTwo leftActor rightActor distinct blocks ordered covered leftStart rightStart
  leftCount rightCount =
  MkActorBlockDecomposition blocks ordered ranges covered
  where
  0 ranges : (earlier, later : name) ->
    (earlierIn : Elem earlier [leftActor, rightActor]) ->
    (laterIn : Elem later [leftActor, rightActor]) ->
    BeforeIn earlier later [leftActor, rightActor] ->
    (earlierPosition, laterPosition : Nat) ->
    LTE (S earlierPosition)
      (S (transitionCount (blockBody {global = trace} (blocks earlier earlierIn)))) ->
    LTE (S laterPosition)
      (S (transitionCount (blockBody {global = trace} (blocks later laterIn)))) ->
    Not (transitionCount (traceBeforeBlock {global = trace} (blocks earlier earlierIn)) +
      earlierPosition =
      transitionCount (traceBeforeBlock {global = trace} (blocks later laterIn)) + laterPosition)
  ranges _ _ Here (There Here) (BeforeHere Here)
    earlierPosition laterPosition earlierBound laterBound exact =
      let earlierSmall = belowTwo
            (replace {p = \count => LTE (S earlierPosition) count}
              leftCount earlierBound)
          laterSmall = belowTwo
            (replace {p = \count => LTE (S laterPosition) count}
              rightCount laterBound)
          leftStarted = replace {p = \start => start + earlierPosition =
            transitionCount (traceBeforeBlock {global = trace}
              (blocks rightActor (There Here))) + laterPosition}
            leftStart exact
          normalized = replace {p = \start => 0 + earlierPosition =
            start + laterPosition} rightStart leftStarted
       in case earlierSmall of
            BelowTwoZero => case laterSmall of
              BelowTwoZero => zeroNotTwo normalized
              BelowTwoOne => zeroNotThree normalized
            BelowTwoOne => case laterSmall of
              BelowTwoZero => oneNotTwo normalized
              BelowTwoOne => oneNotThree normalized
  ranges _ _ Here (There Here) (BeforeThere before)
    earlierPosition laterPosition earlierBound laterBound exact =
      void (noBeforeSingleton before)
  ranges _ _ Here Here before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere same => void (distinct (elemSingletonEquality same))
        BeforeThere tail => void (noBeforeSingleton tail)
  ranges _ _ (There Here) (There Here) before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere later => void (distinct Refl)
        BeforeThere tail => void (noBeforeSingleton tail)
  ranges _ _ (There Here) Here before
    earlierPosition laterPosition earlierBound laterBound exact =
      case before of
        BeforeHere later => void (distinct Refl)
        BeforeThere tail => void (noBeforeSingleton tail)
