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
    AttachedBundleOccurrence name key world error value nameEq keyEq global action (offset + ordinal)) ->
  AttachedNormalForm name key world error value nameEq keyEq global region offset
catalogNormalForm region offset catalog = MkAttachedNormalForm
  (\action, occurrence, root => catalog (locatedActionOrdinal occurrence) action (occurrenceObserved occurrence))
