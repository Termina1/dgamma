module DGamma.CP5L2R1ExtendedZeroGap

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Research counterpart of CP3:1873 BlockBefore, over the extended grammar.
||| Both physical prefix expressions are written out instead of copying the
||| two production prefix helpers. No zero-length gap is required by the type.
public export
record BlockBeforeExtended
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) (earlierName, laterName : name)
  (earlier : LocatedOpenEpisodeBlockExtended name key world error value nameEq keyEq earlierName global)
  (later : LocatedOpenEpisodeBlockExtended name key world error value nameEq keyEq laterName global) where
  constructor MkBlockBeforeExtended
  extendedBetweenBlocks : Transitions (extendedEnd earlier) (extendedPreStart later)
  0 extendedBlocksOrdered :
    appendTransitions (extendedBefore later)
      (MoreTransitions (beginTransition (extendedOpening later)) NoTransitions) =
    appendTransitions
      (appendTransitions (extendedBefore earlier)
        (MoreTransitions (beginTransition (extendedOpening earlier)) (extendedBody earlier)))
      (appendTransitions extendedBetweenBlocks
        (MoreTransitions (beginTransition (extendedOpening later)) NoTransitions))

||| Structural transition-count additivity, with no state observation or
||| proof-token equality. Needed to rule out ANY physical gap witness.
export
0 extendedCountAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  transitionCount (appendTransitions left right) = transitionCount left + transitionCount right
extendedCountAppend NoTransitions right = Refl
extendedCountAppend (MoreTransitions step rest) right = cong S (extendedCountAppend rest right)

||| If normalization has produced coincident PHYSICAL cut counts, every
||| BlockBeforeExtended witness has a zero-length gap. The cut-count premise
||| is explicit: the extended grammar alone does not prove normalization.
export
0 zeroGapFromExtendedCutCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {earlierName, laterName : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (earlier : LocatedOpenEpisodeBlockExtended name key world error value nameEq keyEq earlierName global) ->
  (later : LocatedOpenEpisodeBlockExtended name key world error value nameEq keyEq laterName global) ->
  (ordered : BlockBeforeExtended name key world error value nameEq keyEq global earlierName laterName earlier later) ->
  (0 sameCut : transitionCount
    (appendTransitions (extendedBefore earlier)
      (MoreTransitions (beginTransition (extendedOpening earlier)) (extendedBody earlier))) =
    transitionCount (extendedBefore later)) ->
  transitionCount (extendedBetweenBlocks ordered) = 0
zeroGapFromExtendedCutCount earlier later ordered sameCut =
  sym (plusRightCancel 0 (transitionCount (extendedBetweenBlocks ordered)) 1
    (plusLeftCancel
      (transitionCount (appendTransitions (extendedBefore earlier)
        (MoreTransitions (beginTransition (extendedOpening earlier)) (extendedBody earlier))))
      1 (transitionCount (extendedBetweenBlocks ordered) + 1)
      (trans (cong (\count => count + 1) sameCut)
        (trans (sym (extendedCountAppend (extendedBefore later)
          (MoreTransitions (beginTransition (extendedOpening later)) NoTransitions)))
          (trans (cong transitionCount (extendedBlocksOrdered ordered))
            (trans (extendedCountAppend
              (appendTransitions (extendedBefore earlier)
                (MoreTransitions (beginTransition (extendedOpening earlier)) (extendedBody earlier)))
              (appendTransitions (extendedBetweenBlocks ordered)
                (MoreTransitions (beginTransition (extendedOpening later)) NoTransitions)))
              (cong (\count => transitionCount
                (appendTransitions (extendedBefore earlier)
                  (MoreTransitions (beginTransition (extendedOpening earlier)) (extendedBody earlier))) + count)
                (extendedCountAppend (extendedBetweenBlocks ordered)
                  (MoreTransitions (beginTransition (extendedOpening later)) NoTransitions)))))))))
