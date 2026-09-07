module DGamma.CP5RetirementHistorySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Needed to exclude closing classifications for supported endpoint births.
||| This is same-trace operational monotonicity, not cross-trace A9 agreement.
export
0 retirementUpdateFalseBackward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (old, updated : Fiber name key value world error) ->
  RetirementUpdate old updated -> (retired updated = False) -> (retired old = False)
retirementUpdateFalseBackward name key world error value old updated (RetirementStable same) finalFalse =
  trans (sym same) finalFalse
retirementUpdateFalseBackward name key world error value old updated (RetirementApplied finalTrue) finalFalse =
  case trans (sym finalTrue) finalFalse of Refl impossible

||| Nonretired target fibers inherit any source property, except at a genuine
||| fresh insertion. Actual local updates—not a flag equality assumption—own it.
export
0 rawUnretiredPropertyUpdate :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (property : name -> Type) -> (actor : name) -> (source, target : Registry name key value world error) ->
  RegistryLocalUpdate name key world error value nameEq actor source target ->
  ((lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} actor source = Nothing) -> property actor) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected source = Just fiber) -> (retired fiber = False) -> property selected) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected target = Just observed) -> (retired observed = False) -> property selected
rawUnretiredPropertyUpdate name key world error value nameEq property actor source _
  (LocalInsert next absent) inserted previous selected observed found finalFalse =
    case decEq @{nameEq} selected actor of
      Yes same => case same of Refl => inserted absent
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source (LocalInsert next absent))) found) finalFalse
rawUnretiredPropertyUpdate name key world error value nameEq property actor source _
  (LocalReplace {oldFiber} {oldFound} {retirementUpdate} next) inserted previous selected observed found finalFalse =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => previous actor oldFiber oldFound
          (retirementUpdateFalseBackward name key world error value oldFiber next retirementUpdate
            (trans (cong retired (justInjective (trans (sym (lookupReplacedFiber actor oldFiber next source oldFound)) found))) finalFalse))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source (LocalReplace {oldFiber} {oldFound} {retirementUpdate} next))) found) finalFalse
rawUnretiredPropertyUpdate name key world error value nameEq property actor source _
  LocalDelete inserted previous selected observed found finalFalse =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => void (nothingIsNotJust (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source)) found))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source LocalDelete)) found) finalFalse
