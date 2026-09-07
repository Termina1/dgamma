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

||| A defined composition necessarily has a defined first-applied map.
||| The observed Maybe is passed by the producer, not a supplied witness.
export
0 o19FirstDomainObserved :
  {state : Type} -> (after, before : PartialMap state) -> (origin : state) ->
  (observed : Maybe state) -> (before origin = observed) ->
  (isJust (partialCompose after before origin) = True) ->
  (isJust (before origin) = True)
o19FirstDomainObserved after before origin Nothing exact defined =
  case trans (sym (cong isJust
    (the (partialCompose after before origin = Nothing) (rewrite exact in Refl)))) defined of
      Refl impossible
o19FirstDomainObserved after before origin (Just actual) exact defined =
  cong isJust exact

||| Infer the previously UNSUPPLIED early right-map domain from the two
||| original frames and genuine partial commutation. No early map result,
||| early checked action, target trace, or output relation is an input.
export
0 o19CommutingFramesEarlyDomain :
  (state : Type) -> (eq : Equivalence state) -> (left, right : PartialMap state) ->
  ((first, second : state) -> relation eq first second ->
    PartialRelated state (relation eq) (right first) (right second)) ->
  PartialCommute eq left right -> (origin, middle, final : state) ->
  PartialRelated state (relation eq) (left origin) (Just middle) ->
  PartialRelated state (relation eq) (right middle) (Just final) ->
  (isJust (right origin) = True)
o19CommutingFramesEarlyDomain state eq left right rightRespects commute origin middle final
  leftFrame rightFrame =
    o19FirstDomainObserved left right origin (right origin) Refl
      (trans (o19RelatedDefined (commute origin))
        (o19ComposedFramesObserved state (relation eq) right left rightRespects
          origin middle final (left origin) Refl leftFrame rightFrame))

||| Executable actual partial-map output with an erased authentication proof.
||| This is deliberately not CheckedEarlyApplication: no control/tag claim.
public export
record O19PartialRun (state : Type) (effectMap : PartialMap state) (origin : state) where
  constructor MkO19PartialRun
  partialRunFinal : state
  0 partialRunChecked : effectMap origin = Just partialRunFinal

||| Produce a run from the actual observed evaluator result; the generic
||| commutation theorem supplies its domain proof, never its destination.
export
0 o19PartialRunObserved :
  {state : Type} -> (effectMap : PartialMap state) -> (origin : state) ->
  (observed : Maybe state) -> (effectMap origin = observed) ->
  (isJust observed = True) -> O19PartialRun state effectMap origin
o19PartialRunObserved effectMap origin Nothing exact defined =
  case defined of Refl impossible
o19PartialRunObserved effectMap origin (Just afterState) exact defined =
  MkO19PartialRun afterState exact
