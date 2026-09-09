module DGamma.L2R4ReplaceCommute

import DGamma.Coeffects
import DGamma.L2R2RetireInsert
import Decidable.Equality

%default total
%unbound_implicits off

||| Second observed key decision in ordered-list replacement commutation.
||| The left key misses this head; the right key either hits or also misses.
||| The recursive equality concerns the smaller tail, not runtime certificates.
export
0 replaceCommuteRightObserved :
  {key, item : Type} -> (keyEq : DecEq key) -> (left, right, current : key) ->
  (nextLeft, nextRight, old : item) -> (rest : List (Binding key (\k => item))) ->
  (0 leftMisses : Not (left = current)) ->
  (0 tail : replaceEntries @{keyEq} left nextLeft (replaceEntries @{keyEq} right nextRight rest) =
    replaceEntries @{keyEq} right nextRight (replaceEntries @{keyEq} left nextLeft rest)) ->
  (decision : Dec (right = current)) -> (0 exact : decEq @{keyEq} right current = decision) ->
  replaceEntries @{keyEq} left nextLeft (replaceEntries @{keyEq} right nextRight (Bind current old :: rest)) =
    replaceEntries @{keyEq} right nextRight (replaceEntries @{keyEq} left nextLeft (Bind current old :: rest))
replaceCommuteRightObserved keyEq left right _ nextLeft nextRight old rest leftMisses tail (Yes Refl) exact =
  rewrite replaceOtherHeadObserved keyEq left right nextLeft old rest (decEq @{keyEq} left right) Refl leftMisses in
  rewrite exact in
  replaceOtherHeadObserved keyEq left right nextLeft nextRight rest (decEq @{keyEq} left right) Refl leftMisses
replaceCommuteRightObserved keyEq left right current nextLeft nextRight old rest leftMisses tail (No rightMisses) exact =
  rewrite exact in
  rewrite replaceOtherHeadObserved keyEq left current nextLeft old rest (decEq @{keyEq} left current) Refl leftMisses in
  rewrite replaceOtherHeadObserved keyEq left current nextLeft old (replaceEntries @{keyEq} right nextRight rest)
    (decEq @{keyEq} left current) Refl leftMisses in
  rewrite exact in cong (Bind current old ::) tail
