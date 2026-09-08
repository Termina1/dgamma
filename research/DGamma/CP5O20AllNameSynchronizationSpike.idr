module DGamma.CP5O20AllNameSynchronizationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| The genuine paired-cut invariant for the first THREE bridge clauses.
||| ALL raw names, including unsupported/absent/retired names, are quantified.
||| Its type does not assert that accepted canonical endpoints satisfy it.
||| Production at actual intermediate cuts starts from the empty origin and
||| derives successor fields; callers do not supply endpoint conclusions.
public export
record O20AllNameCut
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (renaming : NameBijection name)
  (left, right : SystemState name key value world error) where
  constructor MkO20AllNameCut
  0 allNameEffects : RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} left)
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} right)
  0 allNameControls : (selected : name) ->
    MaybeFiberRelatedBy {name} {key} {value} {world} {error} renaming
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left))
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (renameForward renaming selected) (registry right))
