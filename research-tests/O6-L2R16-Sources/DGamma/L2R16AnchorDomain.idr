module DGamma.L2R16AnchorDomain

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
import DGamma.L2R6FrontNormal
import DGamma.L2R6Phase
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import DGamma.L2R16AnchorPhases
import Data.Bool
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The actual front and never-retired scans accept both native words.
||| This does NOT include the T12 uniqueness consumer, fully reverted at 3/3.
public export
0 anchorFrontNever : (crossed : Bool) ->
  (FrontNormal Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) (snd fixtureDictionaries) (researchAvailability (anchorTrail crossed)),
   ForcedRootNeverRetired Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) (snd fixtureDictionaries) (researchAvailability (anchorTrail crossed)))
anchorFrontNever False = (MkFrontNormal True Refl Refl, MkForcedRootNeverRetired True Refl Refl)
anchorFrontNever True = (MkFrontNormal True Refl Refl, MkForcedRootNeverRetired True Refl Refl)

||| Authenticate the ACTUAL whole catalog using explicit All data instead
||| of a dependent case-elimination consumer. Each entry has its native
||| phase and is not earlier than the moved root at ordinal7. Generic
||| indexAll supplies the two quantified antecedents without re-casing the
||| opaque dependent entry. No uniqueness premise is assembled here.
public export
0 anchorCatalogCoverage :
  All (\entry => (ForcedRootPhase Nat Bool Unit String (\key => Unit)
      (fst fixtureDictionaries) (snd fixtureDictionaries)
      (researchAvailability (anchorTrail False)) entry,
    LT (catalogOrdinal entry) 7 -> Void))
    (scanRootCatalog 0 (researchAvailability (anchorTrail False)))
anchorCatalogCoverage =
  [(anchorPhase False True, \earlier => absurd earlier),
   (anchorPhase False False, \earlier => absurd earlier)]
