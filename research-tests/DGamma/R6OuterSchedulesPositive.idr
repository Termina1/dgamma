module DGamma.R6OuterSchedulesPositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceCrossTraceSpike
import Decidable.Equality

%default total

public export
0 outerUsesOriginalScheduleValues :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq keyEq rightTrace) ->
  (equivalent : SystemEquivalentByRenamingModuloVestigial name key world error value nameEq keyEq
    (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))) ->
  let result = confluenceResultFromCanonicalCapital nameEq keyEq protocol leftTrace rightTrace
        sameInputs leftSchedule rightSchedule equivalent in
  (leftCanonical result = leftSchedule, rightCanonical result = rightSchedule)
outerUsesOriginalScheduleValues sameInputs leftSchedule rightSchedule equivalent =
  (Refl, Refl)
