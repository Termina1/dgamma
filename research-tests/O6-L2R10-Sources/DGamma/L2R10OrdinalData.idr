module DGamma.L2R10OrdinalData

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R6ForcedScan
import DGamma.L2R9OrdinalScan
import DGamma.L2R9OrdinalTrails
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Concrete transparent dictionary DATA. Search is resolved once at these
||| fully monomorphic types, never at a fixture scan application. Consumers
||| pass these values explicitly; no symbolic dictionary indices remain.
public export
fixtureDictionaries : (DecEq Nat, DecEq Bool)
fixtureDictionaries = (the (DecEq Nat) %search, the (DecEq Bool) %search)
