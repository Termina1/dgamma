module DGamma.CP5O20SupportedReferenceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5AllSupportedMetadataSpike
import DGamma.CP5AcceptedSupportTruthSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A single supported name's image, authenticated by the accepted birth
||| scanner. No metadata is asserted for a withdrawn unsupported intermediate.
public export
record O20SupportedFiberImage
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (renaming : name -> name) (selected : name)
  (sourceFiber : Fiber name key value world error)
  (target : SystemState name key value world error) where
  constructor MkO20SupportedFiberImage
  0 imageFiber : Fiber name key value world error
  0 imageFound : (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    (renaming selected) (registry target) = Just imageFiber)
  0 imageComponent : (fiberComponent imageFiber = fiberComponent sourceFiber)
  0 imageParent : (fiberParent imageFiber = supportMapParent name renaming (fiberParent sourceFiber))

||| Eliminate one explicitly supplied scanner result, never a local case on a
||| computed existential and never a caller assertion about target metadata.
export
0 o20SupportedImageObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : name -> name} -> {selected : name} ->
  {sourceFiber : Fiber name key value world error} ->
  {target : SystemState name key value world error} ->
  (targetFiber : Fiber name key value world error **
    ((lookupFiber {name} {key} {value} {world} {error} @{nameEq}
      (renaming selected) (registry target) = Just targetFiber),
     (fiberComponent targetFiber = fiberComponent sourceFiber),
     (fiberParent targetFiber = supportMapParent name renaming (fiberParent sourceFiber)))) ->
  O20SupportedFiberImage name key world error value nameEq renaming selected sourceFiber target
o20SupportedImageObserved (targetFiber ** (found, component, parent)) =
  MkO20SupportedFiberImage targetFiber found component parent
