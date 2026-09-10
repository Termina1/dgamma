module DGamma.L2R16AnchorDistance

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
import DGamma.L2R5RootCatalog
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

||| Executable omega-style observation: two individual distances, their
||| ACTUAL whole-trace total, and the second root's external-order target.
||| Scans consume production snapshots through the checked native-data bridge.
||| No expected numeral is an input, and no result is yet claimed here.
public export
anchorDistanceData : Bool -> (Nat, Nat, Nat, Nat)
anchorDistanceData crossed =
  (rootDistance (fst fixtureDictionaries) (snd fixtureDictionaries)
     (researchAvailability (anchorTrail crossed)) (if crossed then 6 else 7),
   rootDistance (fst fixtureDictionaries) (snd fixtureDictionaries)
     (researchAvailability (anchorTrail crossed)) 8,
   totalDistance (fst fixtureDictionaries) (snd fixtureDictionaries)
     (researchAvailability (anchorTrail crossed)),
   targetPosition (fst fixtureDictionaries) (snd fixtureDictionaries)
     (researchAvailability (anchorTrail crossed)) 8)

||| CHECKED DATA AGREEMENT, not an assumed scalar frame: the native Retire
||| crossing reduces root4's distance but increases root5's. Total stays 3.
||| Full phase/domain witnesses are a separate obligation; this equality
||| alone does not refute the more strongly indexed global-frame TYPE.
export
0 anchorDistanceAgreement :
  (anchorDistanceData False, anchorDistanceData True) =
  ((3, 0, 3, 8), (2, 1, 3, 7))
anchorDistanceAgreement = Refl
