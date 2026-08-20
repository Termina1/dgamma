module DGamma.CP4DeletionPostCloseFinal

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPostCloseUpgrade
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedForeignTables
import DGamma.CP4DeletionSelectedRetire
import Data.List.Elem
import Decidable.Equality

%default total

0 falseNotTruePostFinal : False = True -> Void
falseNotTruePostFinal Refl impossible

0 boolAndLeftPostFinal : (left, right : Bool) -> left && right = True ->
  left = True
boolAndLeftPostFinal False right Refl impossible
boolAndLeftPostFinal True right equation = Refl

0 boolAndRightPostFinal : (left, right : Bool) -> left && right = True ->
  right = True
boolAndRightPostFinal False right Refl impossible
boolAndRightPostFinal True False Refl impossible
boolAndRightPostFinal True True equation = Refl

0 allListElemTruePostFinal :
  (predicate : item -> Bool) -> (items : List item) -> (wanted : item) ->
  Elem wanted items -> allList predicate items = True -> predicate wanted = True
allListElemTruePostFinal predicate (wanted :: rest) wanted Here allTrue =
  boolAndLeftPostFinal (predicate wanted) (allList predicate rest) allTrue
allListElemTruePostFinal predicate (current :: rest) wanted (There later)
  allTrue = allListElemTruePostFinal predicate rest wanted later
    (boolAndRightPostFinal (predicate current) (allList predicate rest) allTrue)

0 lookupEntryElemPostFinal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (fiber : Fiber name key value world error) ->
  lookupEntries @{nameEq} actor entries = Just fiber ->
  Elem (Bind actor fiber) entries
lookupEntryElemPostFinal nameEq actor [] fiber found =
  case found of Refl impossible
lookupEntryElemPostFinal nameEq actor (Bind current observed :: rest) fiber found
  with (decEq @{nameEq} actor current)
  lookupEntryElemPostFinal nameEq current (Bind current observed :: rest) fiber
    found | Yes Refl = case justInjective found of Refl => Here
  lookupEntryElemPostFinal nameEq actor (Bind current observed :: rest) fiber
    found | No distinct = There
      (lookupEntryElemPostFinal nameEq actor rest fiber found)

0 selectedCurrentOutsidePostFinal :
  (nameEq : DecEq name) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  CurrentGenerationOutside {nameEq = nameEq} registered live selected
selectedCurrentOutsidePostFinal nameEq selected registered live stamped outside
  generation current member =
    let 0 present : Elem (selected, generation) live
        present = currentGenerationEntryFromLookup nameEq selected generation live
          current
        0 generationSelected : generationName generation = selected
        generationSelected = stamped selected generation present
    in outside generation member generationSelected

||| The final no-failure premise turns the plan-side selected Inactive outcome
||| into `Nothing`. The selected-static quotient can therefore be upgraded to
||| the ordinary ordered control relation without removing the selected cell.
public export
0 finalPostCloseGivesRelational :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (original, survivor : SystemState name key value world error) ->
  noFailedFibers original = True ->
  PostCloseSelectedBoundary name key world error value nameEq keyEq selected
    registered ordinal live original survivor ->
  RelationalNoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor
finalPostCloseGivesRelational nameEq keyEq selected registered live unique stamped
  selectedOutside original survivor noFailed boundary =
    let 0 inactive = postClosePlanSelectedInactive boundary
    in case inactive of
      MkInactiveFiberAt component leftParent leftRetired leftTable outcome
        leftFound =>
          let currentOutside = selectedCurrentOutsidePostFinal nameEq selected
                registered live stamped selectedOutside
              strongOutside = currentGenerationOutsideImpliesActorOutsidePlan
                nameEq registered live unique selected currentOutside
              planOutside = actorOutsidePlan
                (completePlanResult (postClosePlan boundary)) selected
                strongOutside
              originalFound = trans
                (sym (lookupOutsideInactivePlan nameEq selected (registry original)
                  (planTarget (completePlanResult (postClosePlan boundary)))
                  (inactiveLeafPlan (completePlanResult
                    (postClosePlan boundary))) planOutside))
                leftFound
              entriesFound = trans
                (sym (lookupFiberAsEntries nameEq selected (registry original)))
                originalFound
              originalMember = lookupEntryElemPostFinal nameEq selected
                (bindings (registry original))
                (MkFiber component leftParent leftRetired leftTable
                  (Inactive outcome)) entriesFound
              selectedNotFailed = allListElemTruePostFinal
                DGamma.CP3.notFailedEntry (bindings (registry original))
                (Bind selected (MkFiber component leftParent leftRetired
                  leftTable (Inactive outcome))) originalMember noFailed
          in case outcome of
            Nothing =>
              case selectedStaticLookupFound nameEq selected
                (planTarget (completePlanResult (postClosePlan boundary)))
                (registry survivor)
                (MkFiber component leftParent leftRetired leftTable
                  (Inactive Nothing)) leftFound (postCloseControls boundary) of
                MkSelectedStaticFiberFound rightFiber staticRightFound static =>
                  case postCloseCleanInactive boundary of
                    SelectedCleanInactiveWitness cleanComponent cleanParent
                      cleanRetired cleanTable cleanFound =>
                        let sameFiber = justInjective
                              (trans (sym staticRightFound) cleanFound)
                        in case sameFiber of
                          Refl => case static of
                            FibersStaticRelated leftParent cleanParent
                              leftRetired cleanRetired leftTable cleanTable
                              (Inactive Nothing) (Inactive Nothing) parentSame
                              retiredSame =>
                                let controls =
                                      selectedOrderedCleanInactiveGivesOrdered
                                        nameEq selected component leftParent
                                        cleanParent leftRetired cleanRetired
                                        leftTable cleanTable
                                        (bindings (planTarget
                                          (completePlanResult
                                            (postClosePlan boundary))))
                                        (bindings (registry survivor))
                                        (uniqueBindings (planTarget
                                          (completePlanResult
                                            (postClosePlan boundary))))
                                        (uniqueBindings (registry survivor))
                                        (trans (sym (lookupFiberAsEntries nameEq
                                          selected (planTarget
                                            (completePlanResult
                                              (postClosePlan boundary)))))
                                          leftFound)
                                        (trans (sym (lookupFiberAsEntries nameEq
                                          selected (registry survivor)))
                                          cleanFound)
                                        (postCloseControls boundary)
                                in MkRelationalNoEpisodeReplayBoundary
                                  (postClosePlan boundary)
                                  (postCloseEffects boundary) controls
                                  (postCloseOriginalWellFormed boundary)
                                  (postCloseSurvivorWellFormed boundary)
            Just failure => void (falseNotTruePostFinal selectedNotFailed)
