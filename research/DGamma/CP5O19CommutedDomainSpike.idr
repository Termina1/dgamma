module DGamma.CP5O19CommutedDomainSpike

import DGamma.Core
import DGamma.Coeffects
import DGamma.Unified
import Data.Maybe

%default total
%unbound_implicits off

||| Partial commutation preserves DEFINEDNESS, not just successful values.
||| This algebraic fact is not a checked control/tag applicability theorem.
export
0 o19RelatedDefined :
  {state : Type} -> {rel : state -> state -> Type} ->
  {left, right : Maybe state} ->
  PartialRelated state rel left right -> (isJust left = isJust right)
o19RelatedDefined PartialUndefined = Refl
o19RelatedDefined (PartialDefined related) = Refl

||| Observe the actual first-map result. Its relation to the actual middle
||| transfers the second-map domain; no early-right application is assumed.
export
0 o19ComposedFramesObserved :
  (state : Type) -> (rel : state -> state -> Type) ->
  (after, before : PartialMap state) ->
  ((left, right : state) -> rel left right ->
    PartialRelated state rel (after left) (after right)) ->
  (origin, middle, final : state) ->
  (observed : Maybe state) -> (before origin = observed) ->
  PartialRelated state rel observed (Just middle) ->
  PartialRelated state rel (after middle) (Just final) ->
  (isJust (partialCompose after before origin) = True)
o19ComposedFramesObserved state rel after before respects origin middle final
  Nothing exact frame finalFrame impossible
o19ComposedFramesObserved state rel after before respects origin middle final
  (Just actual) exact (PartialDefined related) finalFrame =
    rewrite exact in trans (o19RelatedDefined (respects actual middle related))
      (o19RelatedDefined finalFrame)
