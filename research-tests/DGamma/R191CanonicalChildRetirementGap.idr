module DGamma.R191CanonicalChildRetirementGap

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Candidate cuts 0..11 are the ACTUAL checked evaluator observations. The
||| following exact trace proof must exclude every fallback before these cuts
||| may be claimed as an execution. Parent0 yields child3 in its body; child3
||| is retired between completed root1 and root2 blocks, after ALL root births.
public export
r191ChildGapState : Nat -> SystemState Nat R45Key R45Value Unit String
r191ChildGapState Z = r45Initial
r191ChildGapState (S n) = maybe (r191ChildGapState n) snd
  (checkedApplyAction @{r45NameEq} @{r45KeyEq}
    (case n of
      Z => OInsert 0 Root r45Parent
      S Z => OInsert 1 Root r45Child
      S (S Z) => OInsert 2 Root r45Child
      S (S (S Z)) => LBegin 0
      S (S (S (S Z))) => OInsert 3 (ChildOf 0) r45Child
      S (S (S (S (S Z)))) => LAdvance 0
      S (S (S (S (S (S Z))))) => LBegin 1
      S (S (S (S (S (S (S Z)))))) => LAdvance 1
      S (S (S (S (S (S (S (S Z))))))) => ORetire 3
      S (S (S (S (S (S (S (S (S Z)))))))) => LBegin 2
      _ => LAdvance 2)
    (r191ChildGapState n))
