module DGamma.L2R11R191Inventory

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import DGamma.L2R11WordInventory
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Inventory of the ACTUAL eleven-edge R191 native trace, not a supplied
||| representative word. Exactly Begin/Advance/Insert/Retire occur; Remove
||| is permitted by the proposed domain but is absent in this fixture.
||| Inventory acceptance alone does not produce its relocated replay.
export
0 r191ActualInventory :
  (map (inventory (observeWordActionInventory (replayActionWord r191ChildGapTrace)))
      [0, 1, 2, 3, 4, 5, 6, 7] = [True, True, True, True, False, False, False, False],
   restrictedObserved (observeWordActionInventory (replayActionWord r191ChildGapTrace)) = True)
r191ActualInventory = (Refl, Refl)
