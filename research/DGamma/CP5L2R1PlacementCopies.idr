module DGamma.CP5L2R1PlacementCopies

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.CP5AvailabilityAwarePlacement
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Research copy of CP3 CanonicalSchedule (3240-3270).
||| Only the extended block/order types and R178 placement field differ.
||| This is a statement package, NOT an O17 producer or old-schedule adapter.
public export
record AvailabilityCanonicalSchedule
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkAvailabilityCanonicalSchedule
  canonicalFinal : SystemState name key value world error
  canonicalTrace : Transitions initial canonicalFinal
  sameInputs : SameExternalOrchestration nameEq original canonicalTrace
  originalRegistrationDiscipline : RegistrationDiscipline protocol nameEq original
  canonicalRegistrationDiscipline : RegistrationDiscipline protocol nameEq
    canonicalTrace
  supportOrder : List name
  supportLinearization : LinearizesSupport name key world error value nameEq keyEq
    originalFinal supportOrder
  canonicalBlock : (n : name) -> Elem n supportOrder ->
    LocatedOpenEpisodeBlockExtended name key world error value nameEq keyEq n canonicalTrace
  blocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier supportOrder) ->
    (laterIn : Elem later supportOrder) ->
    BeforeIn earlier later supportOrder ->
    BlockBeforeExtended name key world error value nameEq keyEq canonicalTrace
      earlier later (canonicalBlock earlier earlierIn) (canonicalBlock later laterIn)
  lifecycleCoverage : LifecycleActorsCovered supportOrder canonicalTrace
  inputPlacement : AvailabilityAwareCanonicalInputPlacement name key world error value nameEq keyEq
    originalFinal supportOrder original canonicalTrace
  canonicalEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal canonicalFinal
  canonicalRegistrationTree : CanonicalRegistrationCorrespondence original
    canonicalTrace (endpointWithdrawnGenerations canonicalEndpoint)

