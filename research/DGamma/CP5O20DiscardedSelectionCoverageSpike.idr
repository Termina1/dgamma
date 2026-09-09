module DGamma.CP5O20DiscardedSelectionCoverageSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DeletionDisappearanceSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The native Begin index update retains its discarded list at the observed
||| current-generation lookup. This is a scanner equation, not coverage.
export
0 o20BeginDiscardedObserved :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (actor : name) -> (live : GenerationEnvironment name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) -> (discarded : List (RegistrationGeneration name)) ->
  (observed : Maybe (RegistrationGeneration name)) ->
  (lookupCurrentGeneration @{nameEq} actor live = observed) ->
  (indexedDeletedGenerations (advanceRegistrationIndex @{nameEq} ordinal
    (the (Action name key value world error) (LBegin actor))
    (MkRegistrationIndexState live activations counts discarded)) = discarded)
o20BeginDiscardedObserved name key world error value nameEq ordinal actor live activations counts discarded Nothing exact =
  rewrite exact in Refl
o20BeginDiscardedObserved name key world error value nameEq ordinal actor live activations counts discarded (Just generation) exact =
  rewrite exact in Refl

||| Every ordinary native index update retains its discarded history.
export
0 o20IndexDiscardedAdvance :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (action : Action name key value world error) -> (index : RegistrationIndexState name) ->
  (indexedDeletedGenerations (advanceRegistrationIndex @{nameEq} ordinal action index) =
    indexedDeletedGenerations index)
o20IndexDiscardedAdvance name key world error value nameEq ordinal (OInsert child Root component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (OInsert child (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (ORetire actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (ORemove actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LBegin actor)
  (MkRegistrationIndexState live activations counts deleted) =
    o20BeginDiscardedObserved name key world error value nameEq ordinal actor live activations counts deleted
      (lookupCurrentGeneration @{nameEq} actor live) Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LAdvance actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LDivert actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LLeave actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LUnload actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
