module DGamma.R193CandidateEnumerationPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20SelectionCompletenessSpike
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

public export
r193SelectionNameEq : DecEq Nat
r193SelectionNameEq = %search
