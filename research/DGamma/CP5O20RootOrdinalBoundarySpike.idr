module DGamma.CP5O20RootOrdinalBoundarySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike

%default total
%unbound_implicits off

||| Exact missing root law for ONE supplied replay correspondence. The field
||| concerns physical occurrence counts, not generated-child ordinals. This
||| is a specification packet, not a producer from arbitrary correspondences.
public export
record O20RootReplayOrdinals
  (name, key, world, error : Type) (value : key -> Type)
  {sourceFirst, sourceFinal, replayedFirst, replayedFinal : SystemState name key value world error}
  {source : Transitions sourceFirst sourceFinal}
  {replayed : Transitions replayedFirst replayedFinal}
  (correspondence : ActionRegistrationReplayCorrespondence name key world error value source replayed) where
  constructor MkO20RootReplayOrdinals
  0 rootReplayOrdinal :
    {root : name} -> {component : Component key value world error} ->
    (occurrence : LocatedActionOccurrence (OInsert root Root component) replayed) ->
    (generationForward (replayGenerationRenaming correspondence)
      (MkRegistrationGeneration root (locatedActionOrdinal (replayActionOrigin correspondence occurrence))) =
      MkRegistrationGeneration root (locatedActionOrdinal occurrence))
