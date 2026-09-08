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

||| The desired pair is LAST, after an equal-name head that must be skipped
||| and two other real candidates. This is a finite enumeration regression,
||| not an assertion that duplicate actor orders are accepted canonical input.
public export
0 r193LastPairEnumerated : O20EnumeratedPair Nat [4, 4, 2, 3, 1]
  (o20AdjacentCandidates r193SelectionNameEq [4, 4, 2, 3, 1] [] [4, 4, 2, 3, 1] Refl) 3 1
r193LastPairEnumerated = o20AdjacentCandidatesComplete r193SelectionNameEq
  [4, 4, 2, 3, 1] [] [4, 4, 2, 3, 1] Refl 3 1 (\same => absurd same)
  (O20NeighboursLater (O20NeighboursLater (O20NeighboursLater O20NeighboursHere)))

||| Orientation uses the exact actors of the REAL returned candidate, not a
||| scalar Refl observation of the nested candidate builder.
public export
0 r193EnumeratedReverseOrder :
  BeforeIn (actorRight (enumeratedSwap r193LastPairEnumerated))
    (actorLeft (enumeratedSwap r193LastPairEnumerated)) [1, 3]
r193EnumeratedReverseOrder =
  rewrite enumeratedRightExact r193LastPairEnumerated in
  rewrite enumeratedLeftExact r193LastPairEnumerated in BeforeHere Here
