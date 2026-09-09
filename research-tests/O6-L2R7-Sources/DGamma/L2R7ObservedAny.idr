module DGamma.L2R7ObservedAny

import Data.List
import Data.List.Elem

%default total
%unbound_implicits off

||| A decoded successful element of the exact list/predicate scan. Runtime
||| item; erased membership and predicate equation. No seed supplied by fiat.
public export
record AnyHit {a : Type} (predicate : a -> Bool) (items : List a) where
  constructor MkAnyHit
  hitItem : a
  0 hitMember : Elem hitItem items
  0 hitAccepted : predicate hitItem = True

||| Preserve the decoded value while extending membership by one head.
public export
anyHitThere : {a : Type} -> {predicate : a -> Bool} -> {items : List a} ->
  (head : a) -> AnyHit predicate items -> AnyHit predicate (head :: items)
anyHitThere head (MkAnyHit item member accepted) = MkAnyHit item (There member) accepted

||| Eliminate only the explicitly observed head Bool. The tail decoder is a
||| structural-recursion continuation, not an assumed semantic oracle.
public export
anyHitConsObserved : {a : Type} -> (predicate : a -> Bool) ->
  (head : a) -> (items : List a) -> (seen : Bool) ->
  (0 equation : predicate head = seen) ->
  (tailHit : (0 accepted : any predicate items = True) -> AnyHit predicate items) ->
  (0 accepted : seen || any predicate items = True) -> AnyHit predicate (head :: items)
anyHitConsObserved predicate head items True equation tailHit accepted = MkAnyHit head Here equation
anyHitConsObserved predicate head items False equation tailHit accepted = anyHitThere head (tailHit accepted)

||| Prelude.any uses a left fold. A true accumulator remains true.
export
0 anyFoldTrue : {a : Type} -> (predicate : a -> Bool) -> (items : List a) ->
  foldl (\acc, item => acc || predicate item) True items = True
anyFoldTrue predicate [] = Refl
anyFoldTrue predicate (head :: items) = anyFoldTrue predicate items

||| Bridge the library left fold and observed head disjunction. No computed
||| Bool is pattern-matched without passing its value/equation to a helper.
export
0 anyFoldObserved : {a : Type} -> (predicate : a -> Bool) -> (items : List a) ->
  (seen : Bool) -> foldl (\acc, item => acc || predicate item) seen items = (seen || any predicate items)
anyFoldObserved predicate items True = anyFoldTrue predicate items
anyFoldObserved predicate items False = Refl

||| General executable decoder. The scan acceptance is passed through an
||| explicit observed Bool/equation; the chosen element is computed here.
public export
anyHitObserved : {a : Type} -> (predicate : a -> Bool) -> (items : List a) ->
  (seen : Bool) -> (0 equation : any predicate items = seen) ->
  (0 accepted : seen = True) -> AnyHit predicate items
anyHitObserved predicate [] seen equation accepted = absurd (trans equation accepted)
anyHitObserved predicate (head :: items) seen equation accepted =
  anyHitConsObserved predicate head items (predicate head) Refl
    (anyHitObserved predicate items (any predicate items) Refl)
    (trans (sym (anyFoldObserved predicate items (predicate head))) (trans equation accepted))
