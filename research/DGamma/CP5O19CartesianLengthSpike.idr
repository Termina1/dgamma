module DGamma.CP5O19CartesianLengthSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Structural action-fold/count equality. This makes the already-exported
||| authentic sealed-spine fold theorem available for Cartesian cut lengths,
||| without opening the frozen constructors or adding a caller length axiom.
export
0 o19ActionFoldCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  (source : Transitions first last) ->
  traceActionFold name key world error value Nat (\action, count => S count) Z source = transitionCount source
o19ActionFoldCount NoTransitions = Refl
o19ActionFoldCount (MoreTransitions step rest) = cong S (o19ActionFoldCount rest)

||| Structural trace append cardinality, with dependent intermediate state.
export
0 o19TransitionCountAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transitions first middle) -> (right : Transitions middle last) ->
  transitionCount (appendTransitions left right) = transitionCount left + transitionCount right
o19TransitionCountAppend NoTransitions right = Refl
o19TransitionCountAppend (MoreTransitions step rest) right = cong S (o19TransitionCountAppend rest right)

||| ACTUAL sealed suffix preserves transition count via its public action
||| fold eliminator. Frozen spine constructors remain inaccessible/unchanged.
export
0 o19SealedSuffixCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {sourceFirst, sourceLast, reachedFirst, reachedLast : SystemState name key value world error} ->
  (source : Transitions sourceFirst sourceLast) -> (reached : Transitions reachedFirst reachedLast) ->
  SealedSuffixReplaySpine name key world error value nameEq keyEq source reached ->
  transitionCount reached = transitionCount source
o19SealedSuffixCount {name} {key} {world} {error} {value} {nameEq} {keyEq} source reached seal =
  trans (sym (o19ActionFoldCount reached))
    (trans (sealedSuffixActionFoldSame name key world error value nameEq keyEq Nat (\action, count => S count) Z seal)
      (o19ActionFoldCount source))
