module DGamma.L2R10PhaseScan

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7CatalogBirth
import DGamma.L2R9OrdinalScan
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Own-child actor observation. Root controls never count as actor core.
public export
phaseParentOwner : {name : Type} -> Parent name -> Maybe name
phaseParentOwner Root = Nothing
phaseParentOwner (ChildOf actor) = Just actor
