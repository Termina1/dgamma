module DGamma.L2R2ConditionalGap

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ExtendedZeroGap
import Decidable.Equality

%default total
%unbound_implicits off

||| Explicit residual-gap coverage obligation: a nonempty physical gap starts
||| with actual root orchestration. Normalization must PRODUCE this evidence;
||| it does not follow from ActorLifecycleOnlyExtended alone. No new block
||| grammar or availability-attachment variant is defined by this family.
public export
0 RemainingGapHeadIsRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type
RemainingGapHeadIsRoot nameEq NoTransitions = Unit
RemainingGapHeadIsRoot nameEq (MoreTransitions step rest) = RootOrchestrationStep nameEq step

||| Quantified interim zero-gap theorem on physical extended blocks. Besides
||| residual-root-head coverage, it REQUIRES no root orchestration in the actual
||| gap (hence no availability-forced root). No cut-count equality is assumed.
||| This stronger explicit premise is NOT claimed for arbitrary normalized
||| traces: A12 is exactly why it can fail. The block grammar remains the
||| inherited R192 extension. Count transport avoids eliminating projected
||| dependent block endpoints; callers may use the actual gap and Refl.
export
0 extendedZeroGapWithoutRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {earlierName, laterName : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (earlier : LocatedOpenEpisodeBlockExtended name key world error value nameEq keyEq earlierName global) ->
  (later : LocatedOpenEpisodeBlockExtended name key world error value nameEq keyEq laterName global) ->
  (ordered : BlockBeforeExtended name key world error value nameEq keyEq global earlierName laterName earlier later) ->
  {gapFirst, gapFinal : SystemState name key value world error} ->
  (gap : Transitions gapFirst gapFinal) ->
  (0 physical : transitionCount gap = transitionCount (extendedBetweenBlocks ordered)) ->
  (0 covered : RemainingGapHeadIsRoot nameEq gap) ->
  NoRootOrchestration nameEq gap ->
  transitionCount (extendedBetweenBlocks ordered) = 0
extendedZeroGapWithoutRoot earlier later ordered _ physical covered NoRootOrchestrationEnd =
  sym physical
extendedZeroGapWithoutRoot earlier later ordered _ physical covered
  (NoRootOrchestrationStep step rest rejected tail) = void (rejected covered)
