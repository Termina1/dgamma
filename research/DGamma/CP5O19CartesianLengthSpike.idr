module DGamma.CP5O19CartesianLengthSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19MixedRowDispatcherSpike
import Data.List
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

||| The same ACTUAL produced adjacent node preserves whole-trace length.
||| Its authenticated source decomposition and own sealed suffix are used;
||| no arbitrary replay map is mistaken for a bijection/count certificate.
export
0 o19AdjacentResultCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, first, middle, last, sourceFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (earlier : Transitions initial first) ->
  (left : Transition first middle) -> (right : Transition middle last) -> (later : Transitions last sourceFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq source earlier left right later diamond) ->
  transitionCount (swappedTrace result) = transitionCount source
o19AdjacentResultCount source earlier left right later diamond result =
  trans (cong transitionCount (swappedDecomposition result))
    (trans (o19TransitionCountAppend earlier (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) (replayedSuffix result))))
      (trans (cong (\count => transitionCount earlier + S (S count))
        (o19SealedSuffixCount later (replayedSuffix result) (sealedSuffixReplay result)))
        (trans (sym (o19TransitionCountAppend earlier (MoreTransitions left (MoreTransitions right later))))
          (cong transitionCount (originalDecomposition result)))))

||| Whole finite derivation preserves the ACTUAL reached trace length,
||| by recursion on its explicit node chain. This supports later Cartesian
||| range extraction but is not a block-origin/product-count theorem.
export
0 o19FiniteTraceCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, sourceFinal, reachedFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {reached : Transitions initial reachedFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source reached ->
  transitionCount reached = transitionCount source
o19FiniteTraceCount FiniteAdjacentSwapDone = Refl
o19FiniteTraceCount (FiniteAdjacentSwapStep source earlier left right later orientation diamond result reached rest) =
  trans (o19FiniteTraceCount rest) (o19AdjacentResultCount source earlier left right later diamond result)

||| Structural bridge from exact residual ACTION WORDS to actual trace-cut
||| lengths. This counts the explicit spine, not a separately evaluated row.
export
0 o19ActionWordLength :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> length (o19ActionWord trace) = transitionCount trace
o19ActionWordLength NoTransitions = Refl
o19ActionWordLength (MoreTransitions step rest) = cong S (o19ActionWordLength rest)
