module DGamma.L2R16AnchorUnique

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
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Every ACTUAL raw insertion is at its name's unique position. The
||| non-insertion cases are discharged by the native action scan itself.
||| This is finite fixture evidence, not a general unique-name producer.
export
0 anchorInsertionAt : (crossed : Bool) -> (selected, position : Nat) ->
  (0 observed : rawInsertionNameAt Nat Bool Unit String (\key => Unit) position (anchorTrace crossed) = Just selected) ->
  position = (if selected == 4 then (if crossed then 6 else 7) else 8)
anchorInsertionAt False selected 0 observed = absurd observed
anchorInsertionAt False selected 1 observed = absurd observed
anchorInsertionAt False selected 2 observed = absurd observed
anchorInsertionAt False selected 3 observed = absurd observed
anchorInsertionAt False selected 4 observed = absurd observed
anchorInsertionAt False selected 5 observed = absurd observed
anchorInsertionAt False selected 6 observed = absurd observed
anchorInsertionAt False selected 7 observed = rewrite sym (justInjective observed) in Refl
anchorInsertionAt False selected 8 observed = rewrite sym (justInjective observed) in Refl
anchorInsertionAt False selected (S (S (S (S (S (S (S (S (S later))))))))) observed = absurd observed
anchorInsertionAt True selected 0 observed = absurd observed
anchorInsertionAt True selected 1 observed = absurd observed
anchorInsertionAt True selected 2 observed = absurd observed
anchorInsertionAt True selected 3 observed = absurd observed
anchorInsertionAt True selected 4 observed = absurd observed
anchorInsertionAt True selected 5 observed = absurd observed
anchorInsertionAt True selected 6 observed = rewrite sym (justInjective observed) in Refl
anchorInsertionAt True selected 7 observed = absurd observed
anchorInsertionAt True selected 8 observed = rewrite sym (justInjective observed) in Refl
anchorInsertionAt True selected (S (S (S (S (S (S (S (S (S later))))))))) observed = absurd observed
