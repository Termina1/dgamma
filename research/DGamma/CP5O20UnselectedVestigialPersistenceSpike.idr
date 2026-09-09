module DGamma.CP5O20UnselectedVestigialPersistenceSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DeletionDisappearanceSpike
import DGamma.CP5O20OwnCutSafetySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A full accepted current vestigial packet NOT selected at this deletion
||| has native endpoint controls preserved. Both current tables are reconciled
||| from their own scans. This does not assert target discarded membership.
export
0 o20UnselectedVestigialControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq left) ->
  (result : DeletionResult name key world error value nameEq keyEq left
    (selectedActor candidate) (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->
  (selected : name) ->
  (packet : VestigialEndpointGeneration name key world error value nameEq keyEq
    (leftFinalGenerations registrations) (leftDeletedGenerations registrations) selected leftFinal) ->
  Not (Elem (vestigialGeneration packet) (selectedRegistrations candidate)) ->
  FiberControlMaybeRelated
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry leftFinal))
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (survivingFinal result)))
o20UnselectedVestigialControls nameEq keyEq left right mapping registrations candidate result selected packet outside =
  controlsPreservedOutside result selected
    (\generation, found, member => outside
      (replace {p = \stamp => Elem stamp (selectedRegistrations candidate)}
        (justInjective (trans (sym found)
          (trans (cong (lookupCurrentGeneration @{nameEq} selected)
            (sym (o20DeletionAcceptedOriginalLive nameEq keyEq left right mapping registrations candidate result)))
            (vestigialGenerationCurrent packet)))) member))
