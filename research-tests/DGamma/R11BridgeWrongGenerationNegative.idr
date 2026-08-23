module DGamma.R11BridgeWrongGenerationNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total

||| Expected failure specifically at the bridge's accepted original-generation
||| equation for an arbitrary right birth.
public export
0 arbitraryRightBirthCannotSatisfyBridgeGeneration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  {child, parent : name} ->
  {component : Component key value world error} ->
  (leftBirth : LocatedGeneratedRegistration child parent component
    (canonicalTrace (canonicalSchedule leftCapital))) ->
  (rightBirth : LocatedGeneratedRegistration
    (renameForward (currentNameBijection (endpointRenaming sameInputs)) child)
    (renameForward (currentNameBijection (endpointRenaming sameInputs)) parent)
    component (canonicalTrace (canonicalSchedule rightCapital))) ->
  generationForward (generatedGenerationBijection sameInputs)
    (registrationGeneration (replayGeneratedRegistrationOrigin
      (canonicalOccurrenceCorrespondence leftCapital) leftBirth)) =
  registrationGeneration (replayGeneratedRegistrationOrigin
    (canonicalOccurrenceCorrespondence rightCapital) rightBirth)
arbitraryRightBirthCannotSatisfyBridgeGeneration sameInputs leftCapital rightCapital
  leftBirth rightBirth = Refl
