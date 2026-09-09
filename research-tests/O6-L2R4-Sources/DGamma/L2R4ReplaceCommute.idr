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

||| First observed key decision for distinct replacements; hitting the left
||| key forces the right key to miss, otherwise delegate to B1's single split.
export
0 replaceCommuteLeftObserved :
  {key, item : Type} -> (keyEq : DecEq key) -> (left, right, current : key) ->
  (nextLeft, nextRight, old : item) -> (rest : List (Binding key (\k => item))) ->
  (0 distinct : Not (left = right)) ->
  (0 tail : replaceEntries @{keyEq} left nextLeft (replaceEntries @{keyEq} right nextRight rest) =
    replaceEntries @{keyEq} right nextRight (replaceEntries @{keyEq} left nextLeft rest)) ->
  (decision : Dec (left = current)) -> (0 exact : decEq @{keyEq} left current = decision) ->
  replaceEntries @{keyEq} left nextLeft (replaceEntries @{keyEq} right nextRight (Bind current old :: rest)) =
    replaceEntries @{keyEq} right nextRight (replaceEntries @{keyEq} left nextLeft (Bind current old :: rest))
replaceCommuteLeftObserved keyEq left right _ nextLeft nextRight old rest distinct tail (Yes Refl) exact =
  rewrite replaceOtherHeadObserved keyEq right left nextRight old rest (decEq @{keyEq} right left) Refl
    (\same => distinct (sym same)) in
  rewrite exact in
  sym (replaceOtherHeadObserved keyEq right left nextRight nextLeft rest (decEq @{keyEq} right left) Refl
    (\same => distinct (sym same)))
replaceCommuteLeftObserved keyEq left right current nextLeft nextRight old rest distinct tail (No leftMisses) exact =
  replaceCommuteRightObserved keyEq left right current nextLeft nextRight old rest leftMisses tail
    (decEq @{keyEq} right current) Refl

||| Distinct replacements commute on the EXACT ordered runtime binding list.
||| Structural list induction, no uniqueness-proof equality or postulate.
export
0 replaceEntriesCommute :
  {key, item : Type} -> (keyEq : DecEq key) -> (left, right : key) ->
  (nextLeft, nextRight : item) -> (entries : List (Binding key (\k => item))) ->
  (0 distinct : Not (left = right)) ->
  replaceEntries @{keyEq} left nextLeft (replaceEntries @{keyEq} right nextRight entries) =
    replaceEntries @{keyEq} right nextRight (replaceEntries @{keyEq} left nextLeft entries)
replaceEntriesCommute keyEq left right nextLeft nextRight [] distinct = Refl
replaceEntriesCommute keyEq left right nextLeft nextRight (Bind current old :: rest) distinct =
  replaceCommuteLeftObserved keyEq left right current nextLeft nextRight old rest distinct
    (replaceEntriesCommute keyEq left right nextLeft nextRight rest distinct)
    (decEq @{keyEq} left current) Refl
