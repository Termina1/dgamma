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
