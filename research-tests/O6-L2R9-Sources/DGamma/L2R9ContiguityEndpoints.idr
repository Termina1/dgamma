module DGamma.L2R9ContiguityEndpoints

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP4RuntimeBindings
import DGamma.L2R2SmallStates
import DGamma.L2R8ContiguityStates
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Ordered runtime endpoints agree for the original/split/restored state
||| recipes. This does NOT assert native split-path execution (B4 stopped).
||| Native original/restored edges have separate checked per-path packets.
export
0 contiguityEndpoints :
  (runtimeSnapshot (contiguityState 7) = runtimeSnapshot (contiguityState 10),
   runtimeSnapshot (contiguityState 7) = runtimeSnapshot (contiguityState 17))
contiguityEndpoints = (Refl, Refl)
