module DGamma.CP5O19InsertObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19OpeningPropagationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| R184 supervisor-authorized cure: own the actual observed resolver VALUE
||| and both exact equations. This is neither a targetFiber equation nor the
||| exhausted insertion-target declaration. A checked insertion produces it.
public export
record O19ResolutionObservation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (deps : List key)
  (before, afterState : Registry name key value world error) where
  constructor MkO19ResolutionObservation
  resolutionObserved : Maybe (View name deps)
  0 resolutionBefore : resolveView @{nameEq} @{keyEq} {value} {world} {error} deps before = resolutionObserved
  0 resolutionAfter : resolveView @{nameEq} @{keyEq} {value} {world} {error} deps afterState = resolutionObserved
