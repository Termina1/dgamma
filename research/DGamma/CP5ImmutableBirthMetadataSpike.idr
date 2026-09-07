module DGamma.CP5ImmutableBirthMetadataSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Parent and component are immutable through actual non-birth updates.
||| Retirement is deliberately excluded: the frozen evaluator may change it.
public export
0 rawImmutableMetadataUpdate :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (property : name -> (Parent name, Component key value world error) -> Type) ->
  (actor : name) -> (source, target : Registry name key value world error) ->
  (update : RegistryLocalUpdate name key world error value nameEq actor source target) ->
  ((next : Fiber name key value world error) ->
    (absent : lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} actor source = Nothing) ->
    target = insertBinding @{nameEq} actor next source absent -> property actor (fiberParent next, fiberComponent next)) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected source = Just fiber -> property selected (fiberParent fiber, fiberComponent fiber)) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected target = Just observed -> property selected (fiberParent observed, fiberComponent observed)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  (LocalInsert next absent) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (cong (\fiber => (fiberParent fiber, fiberComponent fiber)) (justInjective (trans (sym (lookupInserted actor next source absent)) found)))
          (inserted next absent Refl)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalInsert next absent))) found)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  (LocalReplace {oldFiber} {oldFound} {staticComponent} {staticParent} next) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (trans (sym (cong2 MkPair staticParent staticComponent)) (cong (\fiber => (fiberParent fiber, fiberComponent fiber))
            (justInjective (trans (sym (lookupReplacedFiber actor oldFiber next source oldFound)) found))))
          (previous actor oldFiber oldFound)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalReplace {oldFiber} {oldFound} {staticComponent} {staticParent} next))) found)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  LocalDelete inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => void (nothingIsNotJust
          (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source)) found))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source LocalDelete)) found)
