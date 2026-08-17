module DGamma.CP4DeletionPlanSuccess

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionGenerationUnique
import Data.List.Elem
import Decidable.Equality

%default total

0 boolOrFalseRight : (left, right : Bool) -> left || right = False -> right = False
boolOrFalseRight False False equation = Refl
boolOrFalseRight False True equation = case equation of Refl impossible
boolOrFalseRight True False equation = case equation of Refl impossible
boolOrFalseRight True True equation = case equation of Refl impossible

0 boolOrFalseLeft : (left, right : Bool) -> left || right = False -> left = False
boolOrFalseLeft False False equation = Refl
boolOrFalseLeft False True equation = case equation of Refl impossible
boolOrFalseLeft True False equation = case equation of Refl impossible
boolOrFalseLeft True True equation = case equation of Refl impossible

0 hasChildInDeleteFalse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent, removed : name) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent entries = False ->
  hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent (deleteEntries @{nameEq} {key = name} {value = FiberAt name key value world error} removed entries) = False
hasChildInDeleteFalse nameEq parent removed [] noChild = Refl
hasChildInDeleteFalse nameEq parent removed (Bind selected fiber :: rest)
  noChild with (decEq @{nameEq} removed selected)
  hasChildInDeleteFalse {name} {key} {world} {error} {value} nameEq parent selected (Bind selected fiber :: rest)
    noChild | Yes Refl =
      boolOrFalseRight (isChildOf @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent (Bind selected fiber))
        (hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent rest) noChild
  hasChildInDeleteFalse nameEq parent removed (Bind selected fiber :: rest)
    noChild | No different =
      let headFalse = boolOrFalseLeft
            (isChildOf @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent (Bind selected fiber))
            (hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent rest) noChild
          tailFalse = hasChildInDeleteFalse {name} {key} {world} {error} {value} nameEq parent removed rest
            (boolOrFalseRight
              (isChildOf @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent (Bind selected fiber))
              (hasChildIn @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent rest) noChild)
      in rewrite headFalse in rewrite tailFalse in Refl

||| Removing any entry cannot create a child pointer.
public export
0 hasChildDeleteFalse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (parent, removed : name) ->
  (source : Registry name key value world error) ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent source = False ->
  hasChild @{nameEq} {name = name} {key = key} {value = value} {world = world} {error = error} parent (deleteBinding @{nameEq} removed source) = False
hasChildDeleteFalse nameEq parent removed (MkCoeffectContext entries unique)
  noChild = hasChildInDeleteFalse {name} {key} {world} {error} {value} nameEq parent removed entries noChild

||| Runtime data needed for one current R entry to inhabit the indexed deletion
||| plan. Retirement and empty-table evidence are intentionally not included:
||| they belong to endpoint withdrawal, while control replay needs only an
||| Inactive leaf.
public export
record InactiveLeafAt
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  (source : Registry name key value world error) where
  constructor MkInactiveLeafAt
  leafComponent : Component key value world error
  leafParent : Parent name
  leafRetired : Bool
  leafTable : OwnedTable key value (componentProvisions leafComponent)
  leafOutcome : Maybe error
  0 leafFound : lookupFiber @{nameEq}
    {name = name} {key = key} {value = value} {world = world} {error = error}
    selected source = Just
      (MkFiber leafComponent leafParent leafRetired leafTable
        (Inactive leafOutcome))
  0 leafHasNoChild : hasChild @{nameEq}
    {name = name} {key = key} {value = value} {world = world} {error = error}
    selected source = False

||| Exact boundary invariant whose derivation remains from registration
||| discipline/no-episode provenance. It is generation-indexed and therefore
||| does not classify a later raw-name reissue as an R residue.
public export
CurrentRegisteredInactiveLeaves :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  List (RegistrationGeneration name) -> GenerationEnvironment name ->
  Registry name key value world error -> Type
CurrentRegisteredInactiveLeaves name key world error value nameEq registered live
  source =
    (selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> Elem generation registered ->
    InactiveLeafAt name key world error value nameEq selected source

0 tailNameDistinct :
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (rest : GenerationEnvironment name) ->
  Not (Elem selected (generationEnvironmentNames rest)) ->
  (tailSelected : name) -> (tailGeneration : RegistrationGeneration name) ->
  Elem (tailSelected, tailGeneration) rest ->
  Not (tailSelected = selected)
tailNameDistinct selected generation rest selectedFresh tailSelected
  tailGeneration present same =
    selectedFresh (replace {p = \name => Elem name (generationEnvironmentNames rest)}
      same (environmentElemName present))

0 inactiveLeavesAfterDelete :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (rest : GenerationEnvironment name) ->
  Not (Elem selected (generationEnvironmentNames rest)) ->
  (source : Registry name key value world error) ->
  CurrentRegisteredInactiveLeaves name key world error value nameEq registered
    ((selected, generation) :: rest) source ->
  CurrentRegisteredInactiveLeaves name key world error value nameEq registered
    rest (deleteBinding @{nameEq} selected source)
inactiveLeavesAfterDelete nameEq registered selected generation rest fresh source
  leaves tailSelected tailGeneration present member =
    case leaves tailSelected tailGeneration (There present) member of
      MkInactiveLeafAt component parent retiredFlag table outcome found noChild =>
        let distinct = tailNameDistinct selected generation rest fresh tailSelected
              tailGeneration present
            targetFound = trans
              (lookupDeleteOther tailSelected selected distinct source) found
            targetNoChild = hasChildDeleteFalse nameEq tailSelected selected source
              noChild
        in MkInactiveLeafAt component parent retiredFlag table outcome targetFound
          targetNoChild

||| Construct the exact multi-leaf plan from the boundary invariant. This is the
||| proof-producing counterpart of `buildCurrentRegisteredDeletionPlan`; it
||| cannot fail because every checked branch is supplied propositionally.
public export
0 currentRegisteredLeavesGivePlan :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (source : Registry name key value world error) ->
  CurrentRegisteredInactiveLeaves name key world error value nameEq registered
    live source ->
  CurrentRegisteredPlanResult name key world error value nameEq registered live
    source
currentRegisteredLeavesGivePlan nameEq registered [] UniqueNil source leaves =
  MkCurrentRegisteredPlanResult source NoInactiveLeafDeletion
    (\actor, outside => ActorOutsideDeletionEnd)
currentRegisteredLeavesGivePlan nameEq registered
  ((selected, generation) :: rest) (UniqueCons selectedFresh restUnique) source
  leaves with (isElem generation registered)
  currentRegisteredLeavesGivePlan nameEq registered
    ((selected, generation) :: rest) (UniqueCons selectedFresh restUnique) source
    leaves | No absent =
      case currentRegisteredLeavesGivePlan nameEq registered rest restUnique source
        (\tailSelected, tailGeneration, present, member =>
          leaves tailSelected tailGeneration (There present) member) of
        MkCurrentRegisteredPlanResult target tailPlan tailOutside =>
          let 0 outsideWhole : (actor : name) ->
                ActorOutsideCurrentRegistered actor registered
                  ((selected, generation) :: rest) ->
                ActorOutsideDeletionPlan actor tailPlan
              outsideWhole actor outside = tailOutside actor
                (\tailSelected, tailGeneration, present, member =>
                  outside tailSelected tailGeneration (There present) member)
          in MkCurrentRegisteredPlanResult target tailPlan outsideWhole
  currentRegisteredLeavesGivePlan nameEq registered
    ((selected, generation) :: rest) (UniqueCons selectedFresh restUnique) source
    leaves | Yes member =
      case leaves selected generation Here member of
        MkInactiveLeafAt component parent retiredFlag table outcome found noChild =>
          case currentRegisteredLeavesGivePlan nameEq registered rest restUnique
            (deleteBinding @{nameEq} selected source)
            (inactiveLeavesAfterDelete nameEq registered selected generation rest
              selectedFresh source leaves) of
            MkCurrentRegisteredPlanResult target tailPlan tailOutside =>
              let 0 outsideWhole : (actor : name) ->
                    ActorOutsideCurrentRegistered actor registered
                      ((selected, generation) :: rest) ->
                    ActorOutsideDeletionPlan actor
                      (DeleteInactiveLeaf {fibers = source} {target = target}
                        selected component parent retiredFlag table outcome found
                        noChild tailPlan)
                  outsideWhole actor outside =
                    ActorOutsideDeletionStep tailPlan
                      (outside selected generation Here member)
                      (tailOutside actor
                        (\tailSelected, tailGeneration, present, tailMember =>
                          outside tailSelected tailGeneration (There present)
                            tailMember))
              in MkCurrentRegisteredPlanResult target
                (DeleteInactiveLeaf {fibers = source} {target = target} selected
                  component parent retiredFlag table outcome found noChild
                  tailPlan)
                outsideWhole
