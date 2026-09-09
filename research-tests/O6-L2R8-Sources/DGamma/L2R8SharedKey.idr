module DGamma.L2R8SharedKey

import DGamma.L2R7ObservedAny
import DGamma.L2R7ReleaseDecode
import Data.List
import Data.List.Elem
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| New observed statement, NOT elemDecConsObserved. Eliminate the actual
||| library isElem RESULT with its call-site equation; never re-case isElem.
||| Over the isElem release scan; agreement with scanReleaseOrdinals open.
public export
0 sharedKeyDecision : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (item : key) -> (0 member : Elem item left) ->
  (decision : Dec (Elem item right)) ->
  (0 equation : isElem @{keyEq} item right = decision) ->
  (0 accepted : isYes decision = True) -> SharedKey left right
sharedKeyDecision keyEq left right item member (Yes present) equation accepted =
  MkSharedKey item member present
sharedKeyDecision keyEq left right item member (No absent) equation accepted = absurd accepted

||| General AnyHit decoder over the isElem release scan; agreement with
||| scanReleaseOrdinals open. Observe the library decision ONCE at this call
||| site. The successful key and BOTH list memberships are produced, not
||| supplied as a shared-key oracle. Proof-erased constructive extraction.
public export
0 sharedKeyFromAnyHit : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) ->
  AnyHit (\item => isYes (isElem @{keyEq} item right)) left -> SharedKey left right
sharedKeyFromAnyHit keyEq left right hit =
  sharedKeyDecision keyEq left right (hitItem hit) (hitMember hit)
    (isElem @{keyEq} (hitItem hit) right) Refl (hitAccepted hit)

||| Produce zero or one shared witness from the observed overlap scan, with
||| no success premise. Over the isElem release scan; agreement with
||| scanReleaseOrdinals open. The branch is the EXPLICIT observed Bool.
public export
0 sharedKeysObserved : {key : Type} -> (keyEq : DecEq key) ->
  (left, right : List key) -> (seen : Bool) ->
  (0 equation : any (\item => isYes (isElem @{keyEq} item right)) left = seen) ->
  List (SharedKey left right)
sharedKeysObserved keyEq left right True equation =
  [sharedKeyFromAnyHit keyEq left right
    (anyHitObserved (\item => isYes (isElem @{keyEq} item right)) left True equation Refl)]
sharedKeysObserved keyEq left right False equation = []
