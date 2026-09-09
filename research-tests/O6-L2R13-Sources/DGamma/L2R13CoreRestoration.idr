module DGamma.L2R13CoreRestoration

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R5Extensional
import DGamma.L2R6Iteration
import DGamma.L2R8ContiguityStates
import DGamma.L2R8NativeWords
import DGamma.L2R8CoreContract
import DGamma.L2R9ContiguityPackets
import DGamma.L2R9RestoredPackets
import DGamma.L2R9CoreRestoration
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R11CorePackets
import DGamma.L2R12PacketContiguity
import DGamma.L2R12PacketFixture
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R13PacketEndpointTransport
import DGamma.L2R13PacketEndpointFixture
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| Unconditional FIXED CoreRestorationFixture through the GENERAL local-
||| square/native-frame route. Local6~16 is proved, the actual S frame is
||| discharged, and whole7~17 is DERIVED. No old whole endpoint witness or
||| old CoreRestorationFixture projection, and no native split Remove.
export
0 coreRestorationViaNativeEndpointFrames : CoreRestorationFixture
coreRestorationViaNativeEndpointFrames = MkCoreRestorationFixture
  (packetOriginalRun (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetRestoredRun (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetOriginalTrail (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetRestoredTrail (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetOriginalCore (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetRestoredCore (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetOriginValid (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetRootForeign (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetOriginalSuffix (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetRestoredWord (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetCoreWord (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetCorePosition (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
  (packetWholeEndpoints (coreContiguityFromLocalSquareFrames contiguityState (\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage fixturePacketEndpointHypotheses))
