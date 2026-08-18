module DGamma.CP4DeletionBoundaryPlan

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanCommute
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| Every selected child generation was born before the current suffix
||| boundary.  The whole-suffix fold preserves this fact by weakening the bound.
public export
0 RegisteredGenerationsBornBefore :
  List (RegistrationGeneration name) -> Nat -> Type
RegisteredGenerationsBornBefore registered ordinal =
  (generation : RegistrationGeneration name) -> Elem generation registered ->
  LT (generationBirthOrdinal generation) ordinal

public export
0 registeredGenerationsBornBeforeNext :
  RegisteredGenerationsBornBefore registered ordinal ->
  RegisteredGenerationsBornBefore registered (S ordinal)
registeredGenerationsBornBeforeNext bornBefore generation member =
  lteSuccRight (bornBefore generation member)

0 ltIrreflexiveBoundary : (n : Nat) -> LT n n -> Void
ltIrreflexiveBoundary Z less impossible
ltIrreflexiveBoundary (S n) (LTESucc less) =
  ltIrreflexiveBoundary n less

public export
0 putPreservesOtherEntry :
  (nameEq : DecEq name) -> (inserted, selected : name) ->
  Not (inserted = selected) ->
  (fresh : RegistrationGeneration name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  Elem (selected, generation) live ->
  Elem (selected, generation)
    (putCurrentGeneration @{nameEq} inserted fresh live)
putPreservesOtherEntry nameEq inserted selected distinct fresh generation []
  present = case present of Here impossible; There later impossible
putPreservesOtherEntry nameEq inserted selected distinct fresh generation
  ((candidate, current) :: rest) present
  with (decEq @{nameEq} inserted candidate)
  putPreservesOtherEntry nameEq candidate selected distinct fresh generation
    ((candidate, current) :: rest) present | Yes Refl =
      case present of
        Here => void (distinct Refl)
        There later => There later
  putPreservesOtherEntry nameEq inserted selected distinct fresh generation
    ((candidate, current) :: rest) present | No insertedDifferent =
      case present of
        Here => Here
        There later => There (putPreservesOtherEntry nameEq inserted selected
          distinct fresh generation rest later)

public export
0 registeredEntryAfterPutComesFromOld :
  (nameEq : DecEq name) -> (inserted : name) ->
  (fresh : RegistrationGeneration name) ->
  (registered : List (RegistrationGeneration name)) ->
  Not (Elem fresh registered) ->
  (live : GenerationEnvironment name) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation)
    (putCurrentGeneration @{nameEq} inserted fresh live) ->
  Elem generation registered ->
  Elem (selected, generation) live
registeredEntryAfterPutComesFromOld nameEq inserted fresh registered freshOutside
  [] selected generation present member = case present of
    Here => void (freshOutside member)
    There later impossible
registeredEntryAfterPutComesFromOld nameEq inserted fresh registered freshOutside
  ((candidate, current) :: rest) selected generation present member
  with (decEq @{nameEq} inserted candidate)
  registeredEntryAfterPutComesFromOld nameEq candidate fresh registered
    freshOutside ((candidate, current) :: rest) selected generation present
    member | Yes Refl = case present of
      Here => void (freshOutside member)
      There later => There later
  registeredEntryAfterPutComesFromOld nameEq inserted fresh registered
    freshOutside ((candidate, current) :: rest) selected generation present
    member | No insertedDifferent = case present of
      Here => Here
      There later => There (registeredEntryAfterPutComesFromOld nameEq inserted
        fresh registered freshOutside rest selected generation later member)

public export
0 deletePreservesOtherEntry :
  (nameEq : DecEq name) -> (removed, selected : name) ->
  Not (removed = selected) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  Elem (selected, generation) live ->
  Elem (selected, generation) (deleteCurrentGeneration @{nameEq} removed live)
deletePreservesOtherEntry nameEq removed selected distinct generation [] present =
  case present of Here impossible; There later impossible
deletePreservesOtherEntry nameEq removed selected distinct generation
  ((candidate, current) :: rest) present
  with (decEq @{nameEq} removed candidate)
  deletePreservesOtherEntry nameEq candidate selected distinct generation
    ((candidate, current) :: rest) present | Yes Refl = case present of
      Here => void (distinct Refl)
      There later => later
  deletePreservesOtherEntry nameEq removed selected distinct generation
    ((candidate, current) :: rest) present | No removedDifferent = case present of
      Here => Here
      There later => There (deletePreservesOtherEntry nameEq removed selected
        distinct generation rest later)

public export
0 entryAfterDeleteComesFromOld :
  (nameEq : DecEq name) -> (removed : name) ->
  (live : GenerationEnvironment name) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (deleteCurrentGeneration @{nameEq} removed live) ->
  Elem (selected, generation) live
entryAfterDeleteComesFromOld nameEq removed [] selected generation present =
  case present of Here impossible; There later impossible
entryAfterDeleteComesFromOld nameEq removed
  ((candidate, current) :: rest) selected generation present
  with (decEq @{nameEq} removed candidate)
  entryAfterDeleteComesFromOld nameEq candidate
    ((candidate, current) :: rest) selected generation present | Yes Refl =
      There present
  entryAfterDeleteComesFromOld nameEq removed
    ((candidate, current) :: rest) selected generation present |
    No removedDifferent = case present of
      Here => Here
      There later => There (entryAfterDeleteComesFromOld nameEq removed rest
        selected generation later)

public export
0 entryAfterDeleteActorDistinct :
  (nameEq : DecEq name) -> (removed : name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (deleteCurrentGeneration @{nameEq} removed live) ->
  Not (selected = removed)
entryAfterDeleteActorDistinct nameEq removed [] UniqueNil selected generation
  present same = case present of Here impossible; There later impossible
entryAfterDeleteActorDistinct nameEq removed
  ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique)
  selected generation present same with (decEq @{nameEq} removed candidate)
  entryAfterDeleteActorDistinct nameEq candidate
    ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique)
    selected generation present same | Yes Refl =
      candidateFresh (replace {p = \observed =>
        Elem observed (generationEnvironmentNames rest)} same
        (environmentElemName present))
  entryAfterDeleteActorDistinct nameEq removed
    ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique)
    selected generation present same | No removedDifferent = case present of
      Here => removedDifferent (sym same)
      There later => entryAfterDeleteActorDistinct nameEq removed rest restUnique
        selected generation later same

public export
0 currentGenerationEntryFromLookup :
  (nameEq : DecEq name) -> (selected : name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  lookupCurrentGeneration @{nameEq} selected live = Just generation ->
  Elem (selected, generation) live
currentGenerationEntryFromLookup nameEq selected generation [] found =
  case found of Refl impossible
currentGenerationEntryFromLookup nameEq selected generation
  ((candidate, current) :: rest) found with (decEq @{nameEq} selected candidate)
  currentGenerationEntryFromLookup nameEq candidate generation
    ((candidate, current) :: rest) found | Yes Refl =
      case justInjective found of Refl => Here
  currentGenerationEntryFromLookup nameEq selected generation
    ((candidate, current) :: rest) found | No distinct =
      There (currentGenerationEntryFromLookup nameEq selected generation rest
        found)

0 outsidePlanDistinctFromMember :
  {source, target : Registry name key value world error} ->
  {nameEq : DecEq name} ->
  {plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target} ->
  ActorOutsideDeletionPlan actor plan ->
  Elem selected (inactivePlanActors plan) ->
  Not (actor = selected)
outsidePlanDistinctFromMember ActorOutsideDeletionEnd present =
  case present of Here impossible; There later impossible
outsidePlanDistinctFromMember
  (ActorOutsideDeletionStep rest distinct outsideRest) Here = distinct
outsidePlanDistinctFromMember
  (ActorOutsideDeletionStep rest distinct outsideRest) (There later) =
    outsidePlanDistinctFromMember outsideRest later

public export
0 actorOutsideCurrentFromCompletePlan :
  (planResult : CurrentRegisteredPlanResult name key world error value nameEq
    registered live source) ->
  CurrentRegisteredPlanComplete name key world error value nameEq registered live
    planResult ->
  (actor : name) ->
  ActorOutsideDeletionPlan actor (inactiveLeafPlan planResult) ->
  ActorOutsideCurrentRegistered actor registered live
actorOutsideCurrentFromCompletePlan planResult complete actor outside selected
  generation present member =
    outsidePlanDistinctFromMember outside
      (complete selected generation present member)

||| Package a plan-preserving registry commutation as a complete plan at a new
||| generation environment.  The two callbacks isolate the purely finite
||| generation-environment bookkeeping from the dependent registry transport.
public export
0 completePlanAcrossPreservingCommute :
  (registered : List (RegistrationGeneration name)) ->
  (oldLive, newLive : GenerationEnvironment name) ->
  (oldComplete : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered oldLive oldSource) ->
  (commuted : InactivePlanPreservingUpdateCommute name key world error value
    nameEq (inactiveLeafPlan (completePlanResult oldComplete)) newSource
    expectedTargetBindings) ->
  ((actor : name) -> ActorOutsideCurrentRegistered actor registered newLive ->
    ActorOutsideCurrentRegistered actor registered oldLive) ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) newLive -> Elem generation registered ->
    Elem (selected, generation) oldLive) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered newLive newSource
completePlanAcrossPreservingCommute registered oldLive newLive
  (MkCompleteCurrentRegisteredPlanResult oldPlan oldCompleteProof)
  (MkInactivePlanPreservingUpdateCommute base actorsSame)
  outsideBack presentBack =
    let 0 outsideNew : (actor : name) ->
          ActorOutsideCurrentRegistered actor registered newLive ->
          ActorOutsideDeletionPlan actor (commutedInactivePlan base)
        outsideNew actor outside = commutedActorOutside base actor
          (actorOutsidePlan oldPlan actor (outsideBack actor outside))
        newPlan = MkCurrentRegisteredPlanResult (commutedPlanTarget base)
          (commutedInactivePlan base) outsideNew
        0 completeNew : CurrentRegisteredPlanComplete name key world error value
          nameEq registered newLive
          (MkCurrentRegisteredPlanResult (commutedPlanTarget base)
            (commutedInactivePlan base) outsideNew)
        completeNew selected generation present member =
          replace {p = Elem selected} (sym actorsSame)
            (oldCompleteProof selected generation
              (presentBack selected generation present member) member)
    in MkCompleteCurrentRegisteredPlanResult newPlan completeNew

||| Same packaging for exact O-Remove.  The removed actor is handled directly;
||| every other outside/current actor is transported through the old complete
||| plan and the exact-removal actor relation.
public export
0 completePlanAcrossRemovingCommute :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (oldLive, newLive : GenerationEnvironment name) ->
  (removed : name) ->
  (oldComplete : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered oldLive oldSource) ->
  (commuted : InactivePlanRemovingUpdateCommute name key world error value nameEq
    removed (inactiveLeafPlan (completePlanResult oldComplete)) newSource
    expectedTargetBindings) ->
  ((actor : name) -> Not (actor = removed) ->
    ActorOutsideCurrentRegistered actor registered newLive ->
    ActorOutsideCurrentRegistered actor registered oldLive) ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) newLive -> Elem generation registered ->
    (Elem (selected, generation) oldLive, Not (selected = removed))) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered newLive newSource
completePlanAcrossRemovingCommute nameEq registered oldLive newLive removed
  (MkCompleteCurrentRegisteredPlanResult oldPlan oldCompleteProof)
  (MkInactivePlanRemovingUpdateCommute base removedOutside retainedOther)
  outsideBack presentBack =
    let 0 outsideNew : (actor : name) ->
          ActorOutsideCurrentRegistered actor registered newLive ->
          ActorOutsideDeletionPlan actor (commutedInactivePlan base)
        outsideNew actor outside with (decEq @{nameEq} actor removed)
          outsideNew _ outside | Yes Refl = removedOutside
          outsideNew actor outside | No distinct =
            commutedActorOutside base actor
              (actorOutsidePlan oldPlan actor
                (outsideBack actor distinct outside))
        newPlan = MkCurrentRegisteredPlanResult (commutedPlanTarget base)
          (commutedInactivePlan base) outsideNew
        0 completeNew : CurrentRegisteredPlanComplete name key world error value
          nameEq registered newLive
          (MkCurrentRegisteredPlanResult (commutedPlanTarget base)
            (commutedInactivePlan base) outsideNew)
        completeNew selected generation present member =
          case presentBack selected generation present member of
            (oldPresent, selectedDistinct) =>
              retainedOther selected selectedDistinct
                (oldCompleteProof selected generation oldPresent member)
    in MkCompleteCurrentRegisteredPlanResult newPlan completeNew

||| Retained fresh insertion preserves the complete current-R plan.  The fresh
||| generation is outside R, while completeness plus owner exclusion rules out
||| overwriting any old current R generation.
public export
0 completePlanAfterRetainedInsert :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (inserted : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (oldComplete : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live oldSource) ->
  (ownerOutside : ActorOutsideDeletionPlan inserted
    (inactiveLeafPlan (completePlanResult oldComplete))) ->
  (retained : Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error)
      (OInsert inserted parent component)))) ->
  (commuted : InactivePlanPreservingUpdateCommute name key world error value
    nameEq (inactiveLeafPlan (completePlanResult oldComplete)) newSource
    expectedTargetBindings) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered
    (advanceGenerationEnvironment @{nameEq} ordinal
      (OInsert inserted parent component) live)
    newSource
completePlanAfterRetainedInsert nameEq registered ordinal live inserted parent
  component oldComplete ownerOutside retained commuted =
    let 0 freshOutside : Not
          (Elem (MkRegistrationGeneration inserted ordinal) registered)
        freshOutside member = retained
          (MkRegistrationGeneration inserted ordinal ** (Refl, member))
        0 insertedOutsideCurrent : ActorOutsideCurrentRegistered inserted
          registered live
        insertedOutsideCurrent = actorOutsideCurrentFromCompletePlan
          (completePlanResult oldComplete) (currentPlanComplete oldComplete)
          inserted ownerOutside
        0 outsideBack : (actor : name) ->
          ActorOutsideCurrentRegistered actor registered
            (putCurrentGeneration @{nameEq} inserted
              (MkRegistrationGeneration inserted ordinal) live) ->
          ActorOutsideCurrentRegistered actor registered live
        outsideBack actor outside selected generation present member =
          outside selected generation
            (putPreservesOtherEntry nameEq inserted selected
              (insertedOutsideCurrent selected generation present member)
              (MkRegistrationGeneration inserted ordinal) generation live
              present) member
        0 presentBack : (selected : name) ->
          (generation : RegistrationGeneration name) ->
          Elem (selected, generation)
            (putCurrentGeneration @{nameEq} inserted
              (MkRegistrationGeneration inserted ordinal) live) ->
          Elem generation registered -> Elem (selected, generation) live
        presentBack selected generation present member =
          registeredEntryAfterPutComesFromOld nameEq inserted
            (MkRegistrationGeneration inserted ordinal) registered freshOutside
            live selected generation present member
    in completePlanAcrossPreservingCommute registered live
      (putCurrentGeneration @{nameEq} inserted
        (MkRegistrationGeneration inserted ordinal) live) oldComplete commuted
      outsideBack presentBack

||| Any preserving local replacement leaves the generation environment fixed.
public export
0 completePlanAfterPreservingReplacement :
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (oldComplete : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live oldSource) ->
  (commuted : InactivePlanPreservingUpdateCommute name key world error value
    nameEq (inactiveLeafPlan (completePlanResult oldComplete)) newSource
    expectedTargetBindings) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live newSource
completePlanAfterPreservingReplacement registered live oldComplete commuted =
  completePlanAcrossPreservingCommute registered live live oldComplete commuted
    (\actor, outside => outside)
    (\selected, generation, present, member => present)

||| A retained O-Remove erases only an actor outside the old current-R plan, so
||| deleting its non-R generation preserves complete coverage.
public export
0 completePlanAfterRetainedRemove :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (removed : name) ->
  (oldComplete : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live oldSource) ->
  (ownerOutside : ActorOutsideDeletionPlan removed
    (inactiveLeafPlan (completePlanResult oldComplete))) ->
  (commuted : InactivePlanPreservingUpdateCommute name key world error value
    nameEq (inactiveLeafPlan (completePlanResult oldComplete)) newSource
    expectedTargetBindings) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered (deleteCurrentGeneration @{nameEq} removed live) newSource
completePlanAfterRetainedRemove nameEq registered live removed oldComplete
  ownerOutside commuted =
    let 0 removedOutsideCurrent : ActorOutsideCurrentRegistered removed
          registered live
        removedOutsideCurrent = actorOutsideCurrentFromCompletePlan
          (completePlanResult oldComplete) (currentPlanComplete oldComplete)
          removed ownerOutside
        0 outsideBack : (actor : name) ->
          ActorOutsideCurrentRegistered actor registered
            (deleteCurrentGeneration @{nameEq} removed live) ->
          ActorOutsideCurrentRegistered actor registered live
        outsideBack actor outside selected generation present member =
          outside selected generation
            (deletePreservesOtherEntry nameEq removed selected
              (removedOutsideCurrent selected generation present member)
              generation live present) member
        0 presentBack : (selected : name) ->
          (generation : RegistrationGeneration name) ->
          Elem (selected, generation)
            (deleteCurrentGeneration @{nameEq} removed live) ->
          Elem generation registered -> Elem (selected, generation) live
        presentBack selected generation present member =
          entryAfterDeleteComesFromOld nameEq removed live selected generation
            present
    in completePlanAcrossPreservingCommute registered live
      (deleteCurrentGeneration @{nameEq} removed live) oldComplete commuted
      outsideBack presentBack

||| Exact deletion of a current R actor updates both the generation environment
||| and the complete plan in lockstep.
public export
0 completePlanAfterDeletedRemove :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (removed : name) ->
  (oldComplete : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live oldSource) ->
  (commuted : InactivePlanRemovingUpdateCommute name key world error value nameEq
    removed (inactiveLeafPlan (completePlanResult oldComplete)) newSource
    expectedTargetBindings) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered (deleteCurrentGeneration @{nameEq} removed live) newSource
completePlanAfterDeletedRemove nameEq registered live unique removed oldComplete
  commuted =
    let 0 outsideBack : (actor : name) -> Not (actor = removed) ->
          ActorOutsideCurrentRegistered actor registered
            (deleteCurrentGeneration @{nameEq} removed live) ->
          ActorOutsideCurrentRegistered actor registered live
        outsideBack actor actorDistinct outside selected generation present member
          with (decEq @{nameEq} removed selected)
          outsideBack actor actorDistinct outside _ generation present
            member | Yes Refl = \same => actorDistinct same
          outsideBack actor actorDistinct outside selected generation present
            member | No removedDistinct =
              outside selected generation
                (deletePreservesOtherEntry nameEq removed selected
                  removedDistinct generation live present) member
        0 presentBack : (selected : name) ->
          (generation : RegistrationGeneration name) ->
          Elem (selected, generation)
            (deleteCurrentGeneration @{nameEq} removed live) ->
          Elem generation registered ->
          (Elem (selected, generation) live, Not (selected = removed))
        presentBack selected generation present member =
          (entryAfterDeleteComesFromOld nameEq removed live selected generation
            present,
           entryAfterDeleteActorDistinct nameEq removed live unique selected
            generation present)
    in completePlanAcrossRemovingCommute nameEq registered live
      (deleteCurrentGeneration @{nameEq} removed live) removed oldComplete
      commuted outsideBack presentBack
