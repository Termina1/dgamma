module DGamma.CP5O20SupportedReferenceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceDeletionChainSpike
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

||| Forward image of EVERY supported original actor, from accepted scanner
||| capital and both original uniqueness arguments, not an endpoint oracle.
export
0 o20OriginalSupportedImageForward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) -> (rightTrace : Transitions initial rightFinal) ->
  (inputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (selected : name) -> (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry leftFinal) = Just sourceFiber) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  O20SupportedFiberImage name key world error value nameEq
    (renameForward (currentNameBijection (endpointRenaming inputs))) selected sourceFiber rightFinal
o20OriginalSupportedImageForward {name} {key} {world} {error} {value} nameEq keyEq protocol
  leftTrace rightTrace inputs leftCapital rightCapital leftUnique rightUnique selected sourceFiber found supported =
    o20SupportedImageObserved
      (acceptedAllSupportedMetadataForward name key world error value nameEq keyEq protocol leftTrace rightTrace inputs
        (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
        (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
        (replayDiscipline (chainReplayCapital (capitalPremises leftCapital)))
        (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital)))
        leftUnique rightUnique selected sourceFiber found supported)

||| Backward image of EVERY supported original actor, from accepted scanner
||| capital and both original uniqueness arguments, not an endpoint oracle.
export
0 o20OriginalSupportedImageBackward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) -> (rightTrace : Transitions initial rightFinal) ->
  (inputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (selected : name) -> (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry rightFinal) = Just sourceFiber) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected rightFinal = True) ->
  O20SupportedFiberImage name key world error value nameEq
    (renameBackward (currentNameBijection (endpointRenaming inputs))) selected sourceFiber leftFinal
o20OriginalSupportedImageBackward {name} {key} {world} {error} {value} nameEq keyEq protocol
  leftTrace rightTrace inputs leftCapital rightCapital leftUnique rightUnique selected sourceFiber found supported =
    o20SupportedImageObserved
      (acceptedAllSupportedMetadataBackward name key world error value nameEq keyEq protocol leftTrace rightTrace inputs
        (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
        (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
        (replayDiscipline (chainReplayCapital (capitalPremises rightCapital)))
        (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital)))
        leftUnique rightUnique selected sourceFiber found supported)

||| Transport a genuine provision/dependency edge using the two scanner-owned
||| images. Both declaration memberships are transported at the same key.
export
0 o20PrecedenceImage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : name -> name} -> {lower, upper : name} ->
  {source, target : SystemState name key value world error} ->
  (edge : PrecedenceEdge nameEq lower upper source) ->
  (lowerImage : O20SupportedFiberImage name key world error value nameEq renaming lower (providerFiber edge) target) ->
  (upperImage : O20SupportedFiberImage name key world error value nameEq renaming upper (consumerFiber edge) target) ->
  PrecedenceEdge nameEq (renaming lower) (renaming upper) target
o20PrecedenceImage edge lowerImage upperImage =
  MkPrecedenceEdge (edgeKey edge) (imageFiber lowerImage) (imageFiber upperImage)
    (imageFound lowerImage) (imageFound upperImage)
    (replace {p = \component => Elem (edgeKey edge) (dependencies (componentProvisions component))}
      (sym (imageComponent lowerImage)) (providerDeclares edge))
    (replace {p = \component => Elem (edgeKey edge) (dependencies (componentDependencies component))}
      (sym (imageComponent upperImage)) (consumerDeclares edge))

||| The parent half of Equation62 uses the SAME image's exact parent equation.
export
0 o20ParentImage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {renaming : name -> name} -> {lower, upper : name} ->
  {source, target : SystemState name key value world error} ->
  (edge : ParentSupportEdge nameEq lower upper source) ->
  (upperImage : O20SupportedFiberImage name key world error value nameEq renaming upper (childFiber edge) target) ->
  ParentSupportEdge nameEq (renaming lower) (renaming upper) target
o20ParentImage {name} {renaming} edge upperImage =
  MkParentSupportEdge (imageFiber upperImage) (imageFound upperImage)
    (trans (imageParent upperImage) (cong (supportMapParent name renaming) (childParent edge)))

||| Restricted Equation62 edge transport. Supportedness is required at BOTH
||| endpoints; no assertion is made about a deleted unsupported intermediate.
export
0 o20SupportedEdgeImage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {renaming : name -> name} ->
  {source, target : SystemState name key value world error} ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry source) = Just fiber) ->
    (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected source = True) ->
    O20SupportedFiberImage name key world error value nameEq renaming selected fiber target) ->
  {lower, upper : name} ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} lower source = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} upper source = True) ->
  SupportEdge nameEq source lower upper -> SupportEdge nameEq target (renaming lower) (renaming upper)
o20SupportedEdgeImage images {lower} {upper} lowerSupported upperSupported (SupportPrecedence edge) =
  SupportPrecedence (o20PrecedenceImage edge
    (images lower (providerFiber edge) (providerFound edge) lowerSupported)
    (images upper (consumerFiber edge) (consumerFound edge) upperSupported))
o20SupportedEdgeImage images {upper} lowerSupported upperSupported (SupportParent edge) =
  SupportParent (o20ParentImage edge (images upper (childFiber edge) (childFound edge) upperSupported))

||| The common reference is the transitive closure of Equation62 restricted
||| to supported vertices, NOT all paths whose two endpoints happen to survive.
public export
data O20SupportedPath :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> name -> name -> Type where
  O20SupportedOne :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {state : SystemState name key value world error} -> {lower, upper : name} ->
    (0 lowerSupported : (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} lower state = True)) ->
    (0 upperSupported : (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} upper state = True)) ->
    (0 edge : SupportEdge nameEq state lower upper) ->
    O20SupportedPath name key world error value nameEq keyEq state lower upper
  O20SupportedMore :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {state : SystemState name key value world error} -> {lower, middle, upper : name} ->
    (0 lowerSupported : (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} lower state = True)) ->
    (0 middleSupported : (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} middle state = True)) ->
    (0 edge : SupportEdge nameEq state lower middle) ->
    (0 rest : O20SupportedPath name key world error value nameEq keyEq state middle upper) ->
    O20SupportedPath name key world error value nameEq keyEq state lower upper

||| Forget only the support annotations, retaining every exact Equation62 edge.
export
0 o20SupportedPathRaw :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {state : SystemState name key value world error} -> {lower, upper : name} ->
  O20SupportedPath name key world error value nameEq keyEq state lower upper ->
  SupportPath nameEq state lower upper
o20SupportedPathRaw (O20SupportedOne lowerSupported upperSupported edge) = SupportPathOne edge
o20SupportedPathRaw (O20SupportedMore lowerSupported middleSupported edge rest) =
  SupportPathMore edge (o20SupportedPathRaw rest)

||| Structural common-reference path transport. The induction traverses only
||| authenticated supported vertices, so a vestigial middle cannot enter it.
export
0 o20SupportedPathImage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {renaming : name -> name} ->
  {source, target : SystemState name key value world error} ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry source) = Just fiber) ->
    (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} selected source = True) ->
    O20SupportedFiberImage name key world error value nameEq renaming selected fiber target) ->
  {lower, upper : name} ->
  O20SupportedPath name key world error value nameEq keyEq source lower upper ->
  SupportPath nameEq target (renaming lower) (renaming upper)
o20SupportedPathImage images (O20SupportedOne lowerSupported upperSupported edge) =
  SupportPathOne (o20SupportedEdgeImage images lowerSupported upperSupported edge)
o20SupportedPathImage images (O20SupportedMore lowerSupported middleSupported edge rest) =
  SupportPathMore (o20SupportedEdgeImage images lowerSupported middleSupported edge)
    (o20SupportedPathImage images rest)
