module DGamma.CP4DeletionPostCloseUpgrade

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedBoundary
import Data.List.Elem
import Decidable.Equality

%default total

0 nothingNotJustUpgrade : Nothing = Just value -> Void
nothingNotJustUpgrade Refl impossible

0 lookupAbsentFromFreshUpgrade :
  (nameEq : DecEq name) -> (selected : name) ->
  (entries : List (Binding name value)) ->
  Not (Elem selected (bindingKeys entries)) ->
  lookupEntries @{nameEq} selected entries = Nothing
lookupAbsentFromFreshUpgrade nameEq selected [] fresh = Refl
lookupAbsentFromFreshUpgrade nameEq selected (Bind actor item :: rest) fresh
  with (decEq @{nameEq} selected actor)
  lookupAbsentFromFreshUpgrade nameEq actor (Bind actor item :: rest) fresh |
    Yes Refl = void (fresh Here)
  lookupAbsentFromFreshUpgrade nameEq selected (Bind actor item :: rest) fresh |
    No different = lookupAbsentFromFreshUpgrade nameEq selected rest
      (\later => fresh (There later))

0 staticInactiveNothingControls :
  FiberStaticRelated name key world error value
    (MkFiber component leftParent leftRetired leftTable (Inactive Nothing))
    (MkFiber component rightParent rightRetired rightTable (Inactive Nothing)) ->
  FiberControlRelated
    (MkFiber component leftParent leftRetired leftTable (Inactive Nothing))
    (MkFiber component rightParent rightRetired rightTable (Inactive Nothing))
staticInactiveNothingControls
  (FibersStaticRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable (Inactive Nothing) (Inactive Nothing) parentSame retiredSame) =
      FibersControlRelated leftParent rightParent leftRetired rightRetired
        leftTable rightTable (Inactive Nothing) (Inactive Nothing) parentSame
        retiredSame (InactiveControls Refl)

||| Once the selected raw name is absent, the selected quotient is exactly the
||| full ordered control relation: every remaining cell is foreign.
public export
0 selectedOrderedAbsentGivesOrdered :
  (nameEq : DecEq name) -> (selected : name) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} selected left = Nothing ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  OrderedRegistryControlsRelated name key world error value left right
selectedOrderedAbsentGivesOrdered nameEq selected [] [] absent
  SelectedOrderedControlsNil = OrderedControlsNil
selectedOrderedAbsentGivesOrdered nameEq selected
  (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest) absent
  (SelectedOrderedControlsCons actor relation tail)
  with (decEq @{nameEq} selected actor)
  selectedOrderedAbsentGivesOrdered nameEq actor
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest) absent
    (SelectedOrderedControlsCons actor
      (SelectedFiberControls actorSelected static) tail) | Yes Refl =
        void (nothingNotJustUpgrade (sym absent))
  selectedOrderedAbsentGivesOrdered nameEq actor
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest) absent
    (SelectedOrderedControlsCons actor
      (ForeignFiberControls distinct controls) tail) | Yes Refl =
        void (distinct Refl)
  selectedOrderedAbsentGivesOrdered nameEq selected
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest) absent
    (SelectedOrderedControlsCons actor relation tail) | No different =
      let 0 tailAbsent : (lookupEntries @{nameEq} selected leftRest = Nothing)
          tailAbsent = absent
      in case relation of
        SelectedFiberControls same static => void (different (sym same))
        ForeignFiberControls distinct controls =>
          OrderedControlsCons actor controls
            (selectedOrderedAbsentGivesOrdered nameEq selected leftRest rightRest
              tailAbsent tail)

||| A surviving selected cell also discharges the quotient when both endpoints
||| are clean `Inactive Nothing`. Tables remain on the effect side, exactly as
||| required by Equation 53; immutable component/parent/retirement data come
||| from the selected static relation.
public export
0 selectedOrderedCleanInactiveGivesOrdered :
  (nameEq : DecEq name) -> (selected : name) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftRetired, rightRetired : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  UniqueKeys (bindingKeys left) -> UniqueKeys (bindingKeys right) ->
  lookupEntries @{nameEq} selected left = Just
    (MkFiber component leftParent leftRetired leftTable (Inactive Nothing)) ->
  lookupEntries @{nameEq} selected right = Just
    (MkFiber component rightParent rightRetired rightTable (Inactive Nothing)) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  OrderedRegistryControlsRelated name key world error value left right
selectedOrderedCleanInactiveGivesOrdered nameEq selected component leftParent
  rightParent leftRetired rightRetired leftTable rightTable [] [] UniqueNil
  UniqueNil leftFound rightFound SelectedOrderedControlsNil =
    case leftFound of Refl impossible
selectedOrderedCleanInactiveGivesOrdered nameEq selected component leftParent
  rightParent leftRetired rightRetired leftTable rightTable
  (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
  (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
  leftFound rightFound (SelectedOrderedControlsCons actor relation tail)
  with (decEq @{nameEq} selected actor)
  selectedOrderedCleanInactiveGivesOrdered nameEq actor component leftParent
    rightParent leftRetired rightRetired leftTable rightTable
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
    leftFound rightFound
    (SelectedOrderedControlsCons actor
      (SelectedFiberControls actorSelected static) tail) | Yes Refl =
        let 0 leftSame = justInjective leftFound
            0 rightSame = justInjective rightFound
        in case leftSame of
          Refl => case rightSame of
            Refl => OrderedControlsCons actor
              (staticInactiveNothingControls static)
              (selectedOrderedAbsentGivesOrdered nameEq actor leftRest rightRest
                (lookupAbsentFromFreshUpgrade nameEq actor leftRest leftFresh)
                tail)
  selectedOrderedCleanInactiveGivesOrdered nameEq actor component leftParent
    rightParent leftRetired rightRetired leftTable rightTable
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
    leftFound rightFound
    (SelectedOrderedControlsCons actor
      (ForeignFiberControls distinct controls) tail) | Yes Refl =
        void (distinct Refl)
  selectedOrderedCleanInactiveGivesOrdered nameEq selected component leftParent
    rightParent leftRetired rightRetired leftTable rightTable
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (UniqueCons leftFresh leftUnique) (UniqueCons rightFresh rightUnique)
    leftFound rightFound (SelectedOrderedControlsCons actor relation tail) |
    No different =
      case relation of
        SelectedFiberControls same static => void (different (sym same))
        ForeignFiberControls distinct controls =>
          OrderedControlsCons actor controls
            (selectedOrderedCleanInactiveGivesOrdered nameEq selected component
              leftParent rightParent leftRetired rightRetired leftTable rightTable
              leftRest rightRest leftUnique rightUnique leftFound rightFound tail)
