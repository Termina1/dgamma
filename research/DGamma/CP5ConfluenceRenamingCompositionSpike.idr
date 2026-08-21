module DGamma.CP5ConfluenceRenamingCompositionSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality

%default total

||| Generation renamings compose without any statement repair.  The hard part
||| is transporting the two trace scanners and their deleted-generation lists.
public export
composeGenerationBijection : RegistrationGenerationBijection name ->
  RegistrationGenerationBijection name -> RegistrationGenerationBijection name
composeGenerationBijection left right =
  MkRegistrationGenerationBijection
    (generationForward right . generationForward left)
    (generationBackward left . generationBackward right)
    (\generation =>
      trans
        (cong (generationBackward left)
          (generationLeftInverse right (generationForward left generation)))
        (generationLeftInverse left generation))
    (\generation =>
      trans
        (cong (generationForward right)
          (generationRightInverse left (generationBackward right generation)))
        (generationRightInverse right generation))

||| Current raw-name renamings compose pointwise as ordinary bijections.
public export
composeNameBijection : NameBijection name -> NameBijection name ->
  NameBijection name
composeNameBijection left right =
  MkNameBijection
    (renameForward right . renameForward left)
    (renameBackward left . renameBackward right)
    (\n => trans
      (cong (renameBackward left)
        (renameLeftInverse right (renameForward left n)))
      (renameLeftInverse left n))
    (\n => trans
      (cong (renameForward right)
        (renameRightInverse left (renameBackward right n)))
      (renameRightInverse right n))

||| Desired closure of the CP3 endpoint machinery under two consecutive
||| reduction/matching phases.  The output scanner must classify as vestigial
||| every current generation discarded by either input scanner; this is the
||| precise "vestigial-set union" obligation even though CP3 stores the sets in
||| `RegistrationIndexState` rather than as an explicit record parameter.
public export
record ComposedModuloVestigialEndpoint
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, middleFinal, rightFinal :
    SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (middleTrace : Transitions initial middleFinal)
  (rightTrace : Transitions initial rightFinal)
  (leftGenerationRenaming : RegistrationGenerationBijection name)
  (rightGenerationRenaming : RegistrationGenerationBijection name)
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftGenerationRenaming leftTrace middleTrace)
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightGenerationRenaming middleTrace rightTrace)
  (leftCurrentRenaming : NameBijection name)
  (rightCurrentRenaming : NameBijection name) where
  constructor MkComposedModuloVestigialEndpoint
  composedRegistrations : RegistrationCorrespondenceByGeneration nameEq
    (composeGenerationBijection leftGenerationRenaming rightGenerationRenaming)
    leftTrace rightTrace
  composedCurrentEndpoint : CurrentEndpointRenaming nameEq keyEq
    (composeGenerationBijection leftGenerationRenaming rightGenerationRenaming)
    leftTrace rightTrace composedRegistrations
  composedEndpointRelation : SystemEquivalentByRenamingModuloVestigial
    name key world error value nameEq keyEq composedRegistrations
    (composeNameBijection leftCurrentRenaming rightCurrentRenaming)

||| Candidate transitivity theorem.  Ambient equality and renamed table lookup
||| equality compose directly.  The XL proof debt is scanner composition plus
||| the four-way endpoint disposition: related/related, vestigial/absent,
||| absent/vestigial, and vestigial/vestigial, transported through both raw-name
||| and generation bijections.
public export
0 composeModuloVestigialEndpointSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftFinal, middleFinal, rightFinal :
    SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (middleTrace : Transitions initial middleFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (leftGenerationRenaming : RegistrationGenerationBijection name) ->
  (rightGenerationRenaming : RegistrationGenerationBijection name) ->
  (leftRegistrations : RegistrationCorrespondenceByGeneration nameEq
    leftGenerationRenaming leftTrace middleTrace) ->
  (rightRegistrations : RegistrationCorrespondenceByGeneration nameEq
    rightGenerationRenaming middleTrace rightTrace) ->
  (leftCurrent : CurrentEndpointRenaming nameEq keyEq leftGenerationRenaming
    leftTrace middleTrace leftRegistrations) ->
  (rightCurrent : CurrentEndpointRenaming nameEq keyEq rightGenerationRenaming
    middleTrace rightTrace rightRegistrations) ->
  (leftRelation : SystemEquivalentByRenamingModuloVestigial name key world error
    value nameEq keyEq leftRegistrations (currentNameBijection leftCurrent)) ->
  (rightRelation : SystemEquivalentByRenamingModuloVestigial name key world error
    value nameEq keyEq rightRegistrations (currentNameBijection rightCurrent)) ->
  ComposedModuloVestigialEndpoint name key world error value nameEq keyEq
    leftTrace middleTrace rightTrace leftGenerationRenaming
    rightGenerationRenaming leftRegistrations rightRegistrations
    (currentNameBijection leftCurrent) (currentNameBijection rightCurrent)
composeModuloVestigialEndpointSpike = ?composeModuloVestigialEndpointSpike_rhs
