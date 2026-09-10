module DGamma.L2R4CatalogCoverage

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R3AttachedGap
import DGamma.L2R4OrdinalObservation
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| General NF producer from lookup-complete actual bundle catalog coverage
||| of a supplied region. Its stronger input covers EVERY native action in
||| that region, hence every root orchestration occurrence. It does not find
||| a last release or normalize an arbitrary trace. The exact remaining input
||| obligation is the displayed ordinal/action lookup-completeness callback.
export
0 catalogNormalForm :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, finalState, gapFirst, gapFinal : SystemState name key value world error} ->
  {global : Transitions first finalState} ->
  (region : Transitions gapFirst gapFinal) -> (offset : Nat) ->
  (0 catalog : (ordinal : Nat) -> (action : Action name key value world error) ->
    nativeActionAt region ordinal = Just action ->
    DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq global action (offset + ordinal)) ->
  DGamma.L2R3AttachedGap.AttachedNormalForm name key world error value nameEq keyEq global region offset
catalogNormalForm region offset catalog = DGamma.L2R3AttachedGap.MkAttachedNormalForm
  (\action, occurrence, root => catalog (locatedActionOrdinal occurrence) action (occurrenceObserved occurrence))

||| Structural catalog extension: a real head member plus tail lookup
||| completeness covers all ordinals of the cons region. One Nat elimination
||| transports action and offset equalities; no role Either adapter is used.
export
0 catalogConsObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {first, finalState, before, middle, gapFinal : SystemState name key value world error} ->
  {global : Transitions first finalState} ->
  (step : Transition before middle) -> (rest : Transitions middle gapFinal) -> (offset : Nat) ->
  (0 head : DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq global (transitionAction step) offset) ->
  (0 tail : (n : Nat) -> (action : Action name key value world error) ->
    nativeActionAt rest n = Just action ->
    DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq global action (S offset + n)) ->
  (ordinal : Nat) -> (action : Action name key value world error) ->
  nativeActionAt (MoreTransitions step rest) ordinal = Just action ->
  DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq global action (offset + ordinal)
catalogConsObserved {name} {key} {world} {error} {value} {nameEq} {keyEq} {global}
  step rest offset head tail Z action exact =
    replace {p = DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq global action}
      (sym (plusZeroRightNeutral offset))
      (replace {p = \act => DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq global act offset}
        (justInjective exact) head)
catalogConsObserved {name} {key} {world} {error} {value} {nameEq} {keyEq} {global}
  step rest offset head tail (S n) action exact =
    replace {p = DGamma.L2R3AttachedGap.AttachedBundleOccurrence name key world error value nameEq keyEq global action}
      (plusSuccRightSucc offset n) (tail n action exact)
