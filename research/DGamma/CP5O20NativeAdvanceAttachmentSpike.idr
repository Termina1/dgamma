module DGamma.CP5O20NativeAdvanceAttachmentSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP5O19AdvanceObservationSpike
import DGamma.CP5O20SingleRoleAdvanceExtractionSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Capability and callback observations at the exact PROJECTED runtime source
||| used by the history successor. The primitive equations belong to these
||| values, including the successful callback equation; no successor relation
||| is stored. Native producers below must authenticate the success packet.
public export
record O20EffectStepValues
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (actor : name)
  (before : SystemState name key value world error)
  (component : Component key value world error)
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))
  (view : View name (dependencies (componentDependencies component))) where
  constructor MkO20EffectStepValues
  effectStepCapability : DepValues key value (dependencies (componentDependencies component))
  0 effectStepResolved :
    (resolveEffectValues {name} {key} {value} {world} @{keyEq}
      (dependencies (componentDependencies component)) view
      (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before) = Just effectStepCapability)
  effectStepCallback : O19StepObservation key world error value (dependencies (componentDependencies component))
    (componentProvisions component) step effectStepCapability
    (MkLocalState (effectAmbient (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before))
      (restrictOwnedPreservingOrder {key} {value} @{keyEq} (componentProvisions component)
        (effectTables (projectEffectState {name} {key} {value} {world} {error} @{nameEq} before) actor)))
