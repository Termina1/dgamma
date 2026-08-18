module DGamma.CP4DeletionPlanComplete

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanSuccess
import DGamma.CP4DeletionPlanBoundary
import DGamma.CP4DeletionChildlessInvariant
import Data.List.Elem
import Decidable.Equality

%default total

0 elemNilVoid : Elem item [] -> Void
elemNilVoid Here impossible
elemNilVoid (There later) impossible

||| Runtime list of the exact leaves erased by an indexed plan.
public export
inactivePlanActors :
  InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target -> List name
inactivePlanActors NoInactiveLeafDeletion = []
inactivePlanActors
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) = removed :: inactivePlanActors rest

||| Exact membership of one actor in an ordered Inactive-leaf deletion plan.
public export
ActorDeletedByInactivePlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> (actor : name) ->
  {source, target : Registry name key value world error} ->
  InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target -> Type
ActorDeletedByInactivePlan actor plan = Elem actor (inactivePlanActors plan)

||| Completeness of a plan relative to the exact current registered-generation
||| environment: every current generation in R occurs as a deleted plan leaf.
public export
CurrentRegisteredPlanComplete :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  {source : Registry name key value world error} ->
  CurrentRegisteredPlanResult name key world error value nameEq registered live
    source -> Type
CurrentRegisteredPlanComplete name key world error value nameEq registered live
  planResult =
    (selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> Elem generation registered ->
    ActorDeletedByInactivePlan selected (inactiveLeafPlan planResult)

0 tailEnvironmentActorDistinct :
  (head : name) -> (headGeneration : RegistrationGeneration name) ->
  (rest : GenerationEnvironment name) ->
  Not (Elem head (generationEnvironmentNames rest)) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) rest -> Not (selected = head)
tailEnvironmentActorDistinct head headGeneration rest fresh selected generation
  present same = fresh (replace {p = \candidate =>
    Elem candidate (generationEnvironmentNames rest)} same
    (environmentElemName present))

||| Complete variant of `CurrentRegisteredPlanResult`.  It retains the existing
||| runtime plan and outside projection and adds the erased converse: every
||| current exact R generation is actually deleted.
public export
record CompleteCurrentRegisteredPlanResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (registered : List (RegistrationGeneration name))
  (live : GenerationEnvironment name)
  (source : Registry name key value world error) where
  constructor MkCompleteCurrentRegisteredPlanResult
  completePlanResult : CurrentRegisteredPlanResult name key world error value
    nameEq registered live source
  0 currentPlanComplete : CurrentRegisteredPlanComplete name key world error value
    nameEq registered live completePlanResult

||| The proof-producing leaf builder is complete, not merely sound for actors
||| outside R.  The old builder remains unchanged; this record-saturated variant
||| is used by the whole-suffix invariant.
public export
0 currentRegisteredLeavesGiveCompletePlan :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (source : Registry name key value world error) ->
  CurrentRegisteredInactiveLeaves name key world error value nameEq registered
    live source ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live source
currentRegisteredLeavesGiveCompletePlan nameEq registered [] UniqueNil source
  leaves = MkCompleteCurrentRegisteredPlanResult
    (MkCurrentRegisteredPlanResult source NoInactiveLeafDeletion
      (\actor, outside => ActorOutsideDeletionEnd))
    (\selected, generation, present, member => void (elemNilVoid present))
currentRegisteredLeavesGiveCompletePlan nameEq registered
  ((head, headGeneration) :: rest) (UniqueCons headFresh restUnique) source
  leaves with (isElem headGeneration registered)
  currentRegisteredLeavesGiveCompletePlan nameEq registered
    ((head, headGeneration) :: rest) (UniqueCons headFresh restUnique) source
    leaves | No headAbsent =
      case currentRegisteredLeavesGiveCompletePlan nameEq registered rest
        restUnique source
        (\selected, generation, present, member =>
          leaves selected generation (There present) member) of
        MkCompleteCurrentRegisteredPlanResult
          (MkCurrentRegisteredPlanResult target tailPlan tailOutside)
          tailComplete =>
            let 0 outsideWhole : (actor : name) ->
                  ActorOutsideCurrentRegistered actor registered
                    ((head, headGeneration) :: rest) ->
                  ActorOutsideDeletionPlan actor tailPlan
                outsideWhole actor outside = tailOutside actor
                  (\selected, generation, present, member =>
                    outside selected generation (There present) member)
                0 completeWhole : (selected : name) ->
                  (generation : RegistrationGeneration name) ->
                  Elem (selected, generation) ((head, headGeneration) :: rest) ->
                  Elem generation registered ->
                  Elem selected (inactivePlanActors tailPlan)
                completeWhole _ _ Here member =
                  void (headAbsent member)
                completeWhole selected generation (There later) member =
                  tailComplete selected generation later member
            in MkCompleteCurrentRegisteredPlanResult
              (MkCurrentRegisteredPlanResult target tailPlan outsideWhole)
              completeWhole
  currentRegisteredLeavesGiveCompletePlan nameEq registered
    ((head, headGeneration) :: rest) (UniqueCons headFresh restUnique) source
    leaves | Yes headMember =
      case leaves head headGeneration Here headMember of
        MkInactiveLeafAt component parent retiredFlag table outcome found
          noChild =>
            case currentRegisteredLeavesGiveCompletePlan nameEq registered rest
              restUnique (deleteBinding @{nameEq} head source)
              (inactiveLeavesAfterDelete nameEq registered head headGeneration
                rest headFresh source leaves) of
              MkCompleteCurrentRegisteredPlanResult
                (MkCurrentRegisteredPlanResult target tailPlan tailOutside)
                tailComplete =>
                  let fullPlan : InactiveLeafDeletionPlan {name = name}
                        {key = key} {value = value} {world = world}
                        {error = error} nameEq source target
                      fullPlan = DeleteInactiveLeaf {fibers = source}
                        {target = target} head component parent retiredFlag table
                        outcome found noChild tailPlan
                      0 outsideWhole : (actor : name) ->
                        ActorOutsideCurrentRegistered actor registered
                          ((head, headGeneration) :: rest) ->
                        ActorOutsideDeletionPlan actor fullPlan
                      outsideWhole actor outside = ActorOutsideDeletionStep
                        tailPlan (outside head headGeneration Here headMember)
                        (tailOutside actor
                          (\selected, generation, present, member =>
                            outside selected generation (There present) member))
                      0 completeWhole : (selected : name) ->
                        (generation : RegistrationGeneration name) ->
                        Elem (selected, generation)
                          ((head, headGeneration) :: rest) ->
                        Elem generation registered ->
                        Elem selected (head :: inactivePlanActors tailPlan)
                      completeWhole _ _ Here member = Here
                      completeWhole selected generation (There later) member =
                        There (tailComplete selected generation later member)
                  in MkCompleteCurrentRegisteredPlanResult
                    (MkCurrentRegisteredPlanResult target fullPlan outsideWhole)
                    completeWhole

||| Public-premise construction of the complete boundary plan.  This is the
||| exact plan source used to initialize and re-establish the whole-suffix
||| replay invariant.
public export
0 reachedDisciplinedBoundaryGivesCompleteDeletionPlan :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (scan : GenerationTraceScan nameEq 0 [] trace finalOrdinal finalLive) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  (discipline : RegistrationDiscipline protocol nameEq trace) ->
  (initialWellFormed : registryWellFormed @{nameEq} @{keyEq} initial = True) ->
  (noEpisodes : NoRegisteredEpisode nameEq registered 0 [] trace) ->
  CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered finalLive (registry finalState)
reachedDisciplinedBoundaryGivesCompleteDeletionPlan protocol nameEq keyEq
  registered trace finalOrdinal finalLive scan aligned discipline
  initialWellFormed noEpisodes =
    let 0 unique = generationTraceScanPreservesUnique nameEq scan UniqueNil
        0 inactive = reachedCurrentRegisteredInactive nameEq keyEq registered
          trace finalOrdinal finalLive scan aligned noEpisodes
        0 childless = reachedCurrentRegisteredChildless protocol nameEq keyEq
          registered trace finalOrdinal finalLive scan aligned discipline
          initialWellFormed noEpisodes
        0 leaves = inactiveAndChildlessGiveLeaves nameEq registered finalLive
          unique finalState inactive childless
    in currentRegisteredLeavesGiveCompletePlan nameEq registered finalLive
      unique (registry finalState) leaves
