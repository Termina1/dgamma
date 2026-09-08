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
