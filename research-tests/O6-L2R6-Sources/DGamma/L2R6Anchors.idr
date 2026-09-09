module DGamma.L2R6Anchors

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Observed maximum removal-ending cut; Nothing means no release. Ordinals
||| remain current-trace positions, NOT stable identities across a swap.
public export
lastReleaseCut : List Nat -> Maybe Nat
lastReleaseCut [] = Nothing
lastReleaseCut (ordinal :: later) = Just (S (foldl max ordinal later))
