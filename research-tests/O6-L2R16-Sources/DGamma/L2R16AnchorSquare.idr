module DGamma.L2R16AnchorSquare

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R3ForcedClosure
import DGamma.L2R5Extensional
import DGamma.L2R5RootCatalog
import DGamma.L2R6Iteration
import DGamma.L2R8NativeWords
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| An actual classified native square; deliberately NOT AdmittedDistanceMove.
||| The endpoint relation is proved from these explicit checked snapshots,
||| not passed as an oracle. Parent0 is foreign to moved root4.
public export
0 anchorSquare : ClassifierSquare Nat Bool Unit String (\key => Unit)
  (fst fixtureDictionaries) (snd fixtureDictionaries) 4 (anchorComponent True)
  (anchorState 6) (ORetire 3) ORetireTag (anchorState 8)
anchorSquare = MkClassifierSquare (anchorState 10) (anchorState 11)
  (aEarlyRoot4 anchorNative) (aLateRetire3 anchorNative)
  (CrossChildRetire (freshFiber (smallComponent False) (ChildOf 0)) Refl Refl (\same => uninhabited same))
  Refl (MkRegistryExtensional Refl (\wanted => Refl))
