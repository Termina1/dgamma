module DGamma.L2R13PacketEndpointFixture

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
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

||| Checked LOCAL core/root square 6~16. Only state snapshots compute here;
||| no native split Remove and no previously proved WHOLE7~17 equality.
export
0 fixtureLocalCoreRootSquare : RegistryExtensional Nat Bool Unit String (\key => Unit)
  (fst fixtureDictionaries) (contiguityState 6) (contiguityState 16)
fixtureLocalCoreRootSquare = snapshotIntoExtensional (fst fixtureDictionaries)
  (contiguityState 6) (contiguityState 16) Refl
