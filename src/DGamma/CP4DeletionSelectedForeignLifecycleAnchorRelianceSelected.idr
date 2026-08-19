module DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSelected

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 boolAndRightTrueRelianceAnchor :
  (left, right : Bool) -> left && right = True -> right = True
boolAndRightTrueRelianceAnchor False right same = case same of Refl impossible
boolAndRightTrueRelianceAnchor True False same = case same of Refl impossible
boolAndRightTrueRelianceAnchor True True same = Refl

0 memberKeyTrueElemRelianceSelected :
  (keyEq : DecEq key) -> (wanted : key) ->
  (table : CoeffectContext key value) ->
  memberKey @{keyEq} wanted table = True ->
  Elem wanted (bindingKeys (bindings table))
memberKeyTrueElemRelianceSelected keyEq wanted
  (MkCoeffectContext entries unique) present
  with (lookupEntries @{keyEq} wanted entries) proof found
  memberKeyTrueElemRelianceSelected keyEq wanted
    (MkCoeffectContext entries unique) present | Nothing =
      case present of Refl impossible
  memberKeyTrueElemRelianceSelected keyEq wanted
    (MkCoeffectContext entries unique) present | Just observed =
      lookupJustElem @{keyEq} wanted entries observed found

public export
0 selectedCandidateDeclaresRelianceAnchor :
  (keyEq : DecEq key) -> (wanted : key) ->
  (selectedFiber : Fiber name key value world error) ->
  providerCandidate @{keyEq} wanted selectedFiber = True ->
  Elem wanted (dependencies (componentProvisions
    (fiberComponent selectedFiber)))
selectedCandidateDeclaresRelianceAnchor keyEq wanted selectedFiber candidate =
  let 0 present = boolAndRightTrueRelianceAnchor
        (isActive (fiberLifecycle selectedFiber))
        (memberKey @{keyEq} wanted (ownedValues (fiberTable selectedFiber)))
        candidate
      0 tableMember = memberKeyTrueElemRelianceSelected keyEq wanted
        (ownedValues (fiberTable selectedFiber)) present
  in ownedSound (fiberTable selectedFiber) wanted tableMember
