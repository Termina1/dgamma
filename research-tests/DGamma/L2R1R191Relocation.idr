module DGamma.L2R1R191Relocation

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ChildRelocation
import DGamma.CP5L2R1RetireExchange
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| The actual adjacent Finish1/Retire3 pair is transposed. Only this local
||| two-edge square is constructed; the original eleven-edge trace is reused.
||| Child3's source parent is0, and the distinct foreign actor is1.
public export
0 r191FinishRetireExchange :
  ExactChildRetireExchange Nat R45Key Unit String R45Value r45NameEq r45KeyEq 3 0
    (Fired {before = r191ChildGapState 7} {afterState = r191ChildGapState 8}
      r45NameEq r45KeyEq (LAdvance 1) LFinishTag (nativeCheckedAt 7 r191ChildGapTrace))
    (Fired {before = r191ChildGapState 8} {afterState = r191ChildGapState 9}
      r45NameEq r45KeyEq (ORetire 3) ORetireTag (nativeCheckedAt 8 r191ChildGapTrace))
r191FinishRetireExchange = MkExactChildRetireExchange
  r45ChildFresh Refl Refl (\same => case same of Refl impossible) Refl
  (MkSystemState () (replaceBinding @{r45NameEq} 3 (retireFiber r45ChildFresh)
    (registry (r191ChildGapState 7))))
  (childRetireAtFound r45NameEq r45KeyEq 3 r45ChildFresh (r191ChildGapState 7) Refl
    (checkedActionTargetValid r45NameEq r45KeyEq (LBegin 1)
      (r191ChildGapState 6) (r191ChildGapState 7) LBeginTag (nativeCheckedAt 6 r191ChildGapTrace)))
  (rewrite checkedActionTargetValid r45NameEq r45KeyEq (ORetire 3)
    (r191ChildGapState 8) (r191ChildGapState 9) ORetireTag
    (nativeCheckedAt 8 r191ChildGapTrace) in Refl)
