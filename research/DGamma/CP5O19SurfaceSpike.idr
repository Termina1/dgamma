module DGamma.CP5O19SurfaceSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5AcceptedSupportTruthSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| Pure finite-list transposition.  This remains useful matching capital, but
||| revision 6 deliberately prevents a value of this type from flowing directly
||| into O20: actor distinctness alone cannot justify a local diamond.
public export
record AdjacentActorOrderSwap (name : Type)
  (before, after : List name) where
  constructor MkAdjacentActorOrderSwap
  actorPrefix : List name
  actorLeft : name
  actorRight : name
  actorSuffix : List name
  0 actorBeforeExact : before = actorPrefix ++
    (actorLeft :: actorRight :: actorSuffix)
  0 actorAfterExact : after = actorPrefix ++
    (actorRight :: actorLeft :: actorSuffix)
  0 actorDistinct : Not (actorLeft = actorRight)

