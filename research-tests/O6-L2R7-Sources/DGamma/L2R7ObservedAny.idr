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
