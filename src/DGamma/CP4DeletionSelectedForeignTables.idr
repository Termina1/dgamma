module DGamma.CP4DeletionSelectedForeignTables

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4RecoveryForeignEffect
import DGamma.CP4RecoveryTrace
import Data.List.Elem
import Decidable.Equality

%default total

0 deleteEntriesMemberSource :
  (keyEq : DecEq key) -> (removed : key) ->
  (entries : List (Binding key value)) ->
  (entry : Binding key value) ->
  Elem entry (deleteEntries @{keyEq} removed entries) -> Elem entry entries
deleteEntriesMemberSource keyEq removed [] entry member impossible
deleteEntriesMemberSource keyEq removed
  (Bind current currentValue :: rest) entry member
  with (decEq @{keyEq} removed current)
  deleteEntriesMemberSource keyEq current
    (Bind current currentValue :: rest) entry member | Yes Refl = There member
  deleteEntriesMemberSource keyEq removed
    (Bind current currentValue :: rest) (Bind current currentValue) Here |
    No distinct = Here
  deleteEntriesMemberSource keyEq removed
    (Bind current currentValue :: rest) entry (There later) | No distinct =
      There (deleteEntriesMemberSource keyEq removed rest entry later)

0 inactivePlanTargetMemberSource :
  (nameEq : DecEq name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  (entry : Binding name (FiberAt name key value world error)) ->
  Elem entry (bindings target) -> Elem entry (bindings source)
inactivePlanTargetMemberSource nameEq source source NoInactiveLeafDeletion entry
  member = member
inactivePlanTargetMemberSource nameEq source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) entry member =
      let tailMember = inactivePlanTargetMemberSource nameEq
            (deleteBinding @{nameEq} removed source) target rest entry member
          runtimeBindings = deleteBindingRuntimeBindings nameEq removed source
          deletedMember : Elem entry
            (deleteEntries @{nameEq} removed (bindings source))
          deletedMember = replace {p = Elem entry} runtimeBindings tailMember
      in deleteEntriesMemberSource nameEq removed (bindings source) entry
        deletedMember

0 bindingKeyMember :
  (entry : Binding key value) -> (entries : List (Binding key value)) ->
  Elem entry entries -> Elem (bindingKey entry) (bindingKeys entries)
bindingKeyMember entry (entry :: rest) Here = Here
bindingKeyMember entry (other :: rest) (There later) =
  There (bindingKeyMember entry rest later)

0 lookupHeadSelf :
  (keyEq : DecEq key) -> (selected : key) -> (selectedValue : value selected) ->
  (rest : List (Binding key value)) ->
  lookupEntries @{keyEq} selected (Bind selected selectedValue :: rest) =
    Just selectedValue
lookupHeadSelf keyEq selected selectedValue rest
  with (decEq @{keyEq} selected selected)
  lookupHeadSelf keyEq selected selectedValue rest | Yes Refl = Refl
  lookupHeadSelf keyEq selected selectedValue rest | No contra =
    void (contra Refl)

0 lookupEntryFromUniqueMember :
  (keyEq : DecEq key) ->
  (entries : List (Binding key value)) ->
  UniqueKeys (bindingKeys entries) ->
  Elem (Bind selected selectedValue) entries ->
  lookupEntries @{keyEq} selected entries = Just selectedValue
lookupEntryFromUniqueMember keyEq
  (Bind selected selectedValue :: rest) (UniqueCons fresh uniqueRest) Here =
    lookupHeadSelf keyEq selected selectedValue rest
lookupEntryFromUniqueMember keyEq
  (Bind current currentValue :: rest) (UniqueCons fresh uniqueRest)
  (There later) with (decEq @{keyEq} selected current)
  lookupEntryFromUniqueMember keyEq
    (Bind current currentValue :: rest) (UniqueCons fresh uniqueRest)
    (There later) | Yes same = case same of
      Refl => void
        (fresh (bindingKeyMember (Bind selected selectedValue) rest later))
  lookupEntryFromUniqueMember keyEq
    (Bind current currentValue :: rest) (UniqueCons fresh uniqueRest)
    (There later) | No distinct =
      lookupEntryFromUniqueMember keyEq rest uniqueRest later

0 registryLookupFromMember :
  (nameEq : DecEq name) ->
  (registry : Registry name key value world error) ->
  Elem (Bind actor fiber) (bindings registry) ->
  lookupFiber @{nameEq} actor registry = Just fiber
registryLookupFromMember nameEq (MkCoeffectContext entries unique) member =
  lookupEntryFromUniqueMember nameEq entries unique member

||| The selected accumulator changes only the selected actor's table.  Every
||| located foreign cell in the complete-plan target therefore has exactly the
||| table observed at the quotient survivor.  Membership arguments make the
||| callback honest and stable under the ordered-source recursion.
public export
0 selectedBoundaryForeignLocatedTablesSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole original survivor) ->
  (current : name) -> Not (current = selected) ->
  {leftFiber, rightFiber : Fiber name key value world error} ->
  Elem (Bind current leftFiber)
    (bindings (planTarget
      (completePlanResult (selectedBoundaryPlan boundary)))) ->
  Elem (Bind current rightFiber) (bindings (registry survivor)) ->
  FiberControlRelated leftFiber rightFiber ->
  bindings (ownedValues (fiberTable leftFiber)) =
    bindings (ownedValues (fiberTable rightFiber))
selectedBoundaryForeignLocatedTablesSame nameEq keyEq selected
  boundary@(MkSelectedEpisodeReplayBoundary
    effects complete ordered clean originalWellFormed survivorWellFormed)
  current distinct leftMember rightMember controls =
    let plan = inactiveLeafPlan (completePlanResult complete)
        originalMember = inactivePlanTargetMemberSource nameEq
          (registry original) (planTarget (completePlanResult complete)) plan
          (Bind current leftFiber) leftMember
        originalFound = registryLookupFromMember nameEq (registry original)
          originalMember
        survivorFound = registryLookupFromMember nameEq (registry survivor)
          rightMember
        originalProjected = projectedActorTable nameEq current original leftFiber
          originalFound
        survivorProjected = projectedActorTable nameEq current survivor rightFiber
          survivorFound
    in case effects of
      MkSelectedEffectReplayBoundary model recovered runs survivorToRecovered =>
        let recoveredPreserves =
              accumulatorEffectMapForeignPreservesBindings nameEq keyEq current
                selected distinct (modelHandle model)
                (projectEffectState @{nameEq} original) recovered runs
            leftToOriginal = cong bindings (sym originalProjected)
            originalToRecovered = sym recoveredPreserves
            recoveredToSurvivor = sym (tablesExact survivorToRecovered current)
            survivorToRight = cong bindings survivorProjected
        in trans leftToOriginal
          (trans originalToRecovered
            (trans recoveredToSurvivor survivorToRight))
