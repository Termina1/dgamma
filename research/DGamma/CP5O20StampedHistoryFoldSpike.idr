module DGamma.CP5O20StampedHistoryFoldSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20PairedExecutionSpike
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5O20PairedRemovalSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20HistoryExecutionSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP4DeletionGenerationUnique
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Internal history cut at a FIXED live-name bijection, with the same runtime
||| and bidirectional generation fields as O20HistoryCut. The fixed index lets
||| a structural fold retain the map without equating projected observations.
||| This capital is conditional on a supplied stage synchronization; not universal pairing.
public export
record O20StampedCut
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (mapping : RegistrationGenerationBijection name)
  (renaming : NameBijection name)
  (leftLive, rightLive : GenerationEnvironment name)
  (left, right : SystemState name key value world error) where
  constructor MkO20StampedCut
  0 stampedRuntime : O20AllNameCut name key world error value nameEq renaming left right
  0 stampedForward : (selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected leftLive = Just stamp) ->
    (renameForward renaming selected = o20HistoricalTarget mapping stamp)
  0 stampedBackward : (selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected rightLive = Just stamp) ->
    (renameBackward renaming selected = generationName (generationBackward mapping stamp))
