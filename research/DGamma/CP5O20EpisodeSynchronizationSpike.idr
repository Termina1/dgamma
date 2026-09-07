module DGamma.CP5O20EpisodeSynchronizationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import DGamma.CP5O20SupportedEndpointCapitalSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Internal paired-cut invariant: ambient is GLOBAL, tables retain full ordered
||| bindings. This specification does not assert that canonical cuts satisfy it.
||| A canonical producer must instantiate the accepted fixed bijection itself.
public export
record RenamedRuntimeEffects
  (name, key, world : Type) (value : key -> Type)
  (renaming : NameBijection name)
  (left, right : EffectState name key value world) where
  constructor MkRenamedRuntimeEffects
  0 synchronizedAmbient : (effectAmbient left = effectAmbient right)
  0 synchronizedTables : (selected : name) ->
    (bindings (effectTables left selected) =
      bindings (effectTables right (renameForward renaming selected)))
