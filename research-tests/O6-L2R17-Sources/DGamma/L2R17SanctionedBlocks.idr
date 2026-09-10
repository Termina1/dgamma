module DGamma.L2R17SanctionedBlocks

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.L2R17SanctionedStates
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5UniqueRawNameInsertions
import DGamma.L2R2SmallStates
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import Data.DPair
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| TYPE only: the inhabitant must supply native source/target executions,
||| both FULL production located blocks, their physical order, and actual
||| root births INSIDE both bodies. Every block wrapper uses empty history.
public export
record SanctionedBlocks where
  constructor MkSanctionedBlocks
  sourceTrace : Transitions (sanctionedState 0) (sanctionedState 10)
  targetTrace : Transitions (sanctionedState 0) (sanctionedState 20)
  0 initialValid : registryWellFormed @{fst fixtureDictionaries} @{snd fixtureDictionaries} (sanctionedState 0) = True
  0 firstBlock : LocatedOpenEpisodeBlock Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) (snd fixtureDictionaries) 0 sourceTrace
  0 secondBlock : LocatedOpenEpisodeBlock Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) (snd fixtureDictionaries) 2 sourceTrace
  0 sourceBlockOrder : BlockBefore Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) (snd fixtureDictionaries) sourceTrace 0 2 firstBlock secondBlock
  0 firstRootInside : LocatedActionOccurrence (OInsert 4 Root (anchorComponent True)) (blockBody firstBlock)
  0 secondRootInside : LocatedActionOccurrence (OInsert 5 Root (anchorComponent False)) (blockBody secondBlock)
  0 blockSizes : (transitionCount (blockBody firstBlock), transitionCount (blockBody secondBlock)) = (4, 4)
