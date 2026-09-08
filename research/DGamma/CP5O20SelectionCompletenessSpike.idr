module DGamma.CP5O20SelectionCompletenessSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20OperationalProgressSpike
import DGamma.CP5O20OperationalDescentSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Map preserves actual Maybe success without selecting or equating payloads.
export
0 o20MapMaybePresent : {a, b : Type} -> (make : a -> b) ->
  (source : Maybe a) -> isJust source = True -> isJust (map make source) = True
o20MapMaybePresent make Nothing Refl impossible
o20MapMaybePresent make (Just value) present = Refl

||| Any strict BeforeIn on a nonempty list puts its RIGHT member in the tail.
export
0 o20BeforeRightInTail :
  {name : Type} -> {left, right, head : name} -> {rest : List name} ->
  BeforeIn left right (head :: rest) -> Elem right rest
o20BeforeRightInTail (BeforeHere member) = member
o20BeforeRightInTail (BeforeThere later) = snd (o20BeforeMembers later)

||| Distinct left/head names eliminate only the BeforeIn head constructor;
||| no flat multi-block order split or nonlinear name pattern is needed.
export
0 o20BeforeDifferentHeadTail :
  {name : Type} -> {left, right, head : name} -> {rest : List name} ->
  Not (left = head) -> BeforeIn left right (head :: rest) -> BeforeIn left right rest
o20BeforeDifferentHeadTail different (BeforeHere member) = void (different Refl)
o20BeforeDifferentHeadTail different (BeforeThere later) = later

||| COMPLETE actual target BeforeIn checker by structural order induction.
||| Distinctness and membership come from the original order witness; no
||| successful check is a caller premise and no target payload is equated.
export
0 o20CheckBeforeComplete :
  {name : Type} -> (nameEq : DecEq name) -> (left, right : name) -> (order : List name) ->
  BeforeIn left right order -> (isJust (o20CheckBefore nameEq left right order) = True)
o20CheckBeforeComplete nameEq left right [] ordered impossible
o20CheckBeforeComplete nameEq left right (head :: rest) ordered =
  o20BeforeOwnerDecisionObserved nameEq left right head rest (decEq @{nameEq} left head) Refl
    (o20BeforeRightInTail ordered)
    (\different => o20MapMaybePresent (BeforeThere {other = head}) (o20CheckBefore nameEq left right rest)
      (o20CheckBeforeComplete nameEq left right rest (o20BeforeDifferentHeadTail different ordered)))
