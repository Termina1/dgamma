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

||| Transpose Begin1 with the early Retire3 PRODUCED by the preceding square.
||| Together the two adjacent squares move ordinal8 retirement to ordinal6.
public export
0 r191BeginRetireExchange :
  ExactChildRetireExchange Nat R45Key Unit String R45Value r45NameEq r45KeyEq 3 0
    (Fired {before = r191ChildGapState 6} {afterState = r191ChildGapState 7}
      r45NameEq r45KeyEq (LBegin 1) LBeginTag (nativeCheckedAt 6 r191ChildGapTrace))
    (Fired {before = r191ChildGapState 7} {afterState = exchangeMiddle r191FinishRetireExchange}
      r45NameEq r45KeyEq (ORetire 3) ORetireTag (exchangeEarlyChecked r191FinishRetireExchange))
r191BeginRetireExchange = MkExactChildRetireExchange
  r45ChildFresh Refl Refl (\same => case same of Refl impossible) Refl
  (MkSystemState () (replaceBinding @{r45NameEq} 3 (retireFiber r45ChildFresh)
    (registry (r191ChildGapState 6))))
  (childRetireAtFound r45NameEq r45KeyEq 3 r45ChildFresh (r191ChildGapState 6) Refl
    (checkedActionTargetValid r45NameEq r45KeyEq (LAdvance 0)
      (r191ChildGapState 5) (r191ChildGapState 6) LFinishTag (nativeCheckedAt 5 r191ChildGapTrace)))
  (rewrite checkedActionTargetValid r45NameEq r45KeyEq (ORetire 3)
    (r191ChildGapState 7) (exchangeMiddle r191FinishRetireExchange) ORetireTag
    (exchangeEarlyChecked r191FinishRetireExchange) in Refl)

||| Eleven native edges obtained by splicing the TWO local exchange proofs.
||| The untouched prefix is the actual old parent block; the untouched suffix
||| is the actual old actor2 block. The endpoint is literally the old state11.
public export
0 r191RelocatedTrace : Transitions (r191ChildGapState 0) (r191ChildGapState 11)
r191RelocatedTrace = retireExchangeInContext
  (prefixThroughBlock (r191ChildGapBlocks 0 Here))
  (Fired {before = r191ChildGapState 6} {afterState = r191ChildGapState 7}
    r45NameEq r45KeyEq (LBegin 1) LBeginTag (nativeCheckedAt 6 r191ChildGapTrace))
  (Fired {before = r191ChildGapState 7} {afterState = exchangeMiddle r191FinishRetireExchange}
    r45NameEq r45KeyEq (ORetire 3) ORetireTag (exchangeEarlyChecked r191FinishRetireExchange))
  (MoreTransitions
    (Fired {before = exchangeMiddle r191FinishRetireExchange} {afterState = r191ChildGapState 9}
      r45NameEq r45KeyEq (LAdvance 1) LFinishTag (exchangeLaterChecked r191FinishRetireExchange))
    (MoreTransitions (beginTransition (blockOpening (r191ChildGapBlocks 2 (There (There Here)))))
      (blockBody (r191ChildGapBlocks 2 (There (There Here))))))
  r191BeginRetireExchange

||| The actual relocated parent block has physical range [3,7): its old
||| Insert3/Finish0 body is extended by the derived checked Retire3 edge.
||| Installedness, no-other-lifecycle, endpoint activity and exact global
||| factorization are retained; the old eleven-edge trace is not rebuilt.
public export
0 r191RelocatedParentBlock :
  LocatedOpenEpisodeBlockExtended Nat R45Key Unit String R45Value
    r45NameEq r45KeyEq 0 r191RelocatedTrace
r191RelocatedParentBlock = MkLocatedOpenEpisodeBlockExtended
  (r191ChildGapState 3) (r191ChildGapState 4) (exchangeMiddle r191BeginRetireExchange)
  (traceBeforeBlock (r191ChildGapBlocks 0 Here))
  (blockOpening (r191ChildGapBlocks 0 Here))
  (appendTransitions (blockBody (r191ChildGapBlocks 0 Here))
    (MoreTransitions
      (Fired {before = r191ChildGapState 6} {afterState = exchangeMiddle r191BeginRetireExchange}
        r45NameEq r45KeyEq (ORetire 3) ORetireTag (exchangeEarlyChecked r191BeginRetireExchange))
      NoTransitions))
  (appendInstalledTrace _ _ (blockBodyInstalled (r191ChildGapBlocks 0 Here))
    (InstalledStep (ORetire 3) ORetireTag (exchangeEarlyChecked r191BeginRetireExchange) _
      Refl (InstalledEnd Refl)))
  (appendActorLifecycleOnlyExtended _ _
    (actorLifecycleOnlyIntoExtended r45NameEq (blockActorOnly (r191ChildGapBlocks 0 Here)))
    (ExtendedChildRetireStep _ _ 3 r45ChildFresh Refl Refl Refl ExtendedLifecycleEnd))
  (MoreTransitions
    (Fired {before = exchangeMiddle r191BeginRetireExchange} {afterState = exchangeMiddle r191FinishRetireExchange}
      r45NameEq r45KeyEq (LBegin 1) LBeginTag (exchangeLaterChecked r191BeginRetireExchange))
    (MoreTransitions
      (Fired {before = exchangeMiddle r191FinishRetireExchange} {afterState = r191ChildGapState 9}
        r45NameEq r45KeyEq (LAdvance 1) LFinishTag (exchangeLaterChecked r191FinishRetireExchange))
      (MoreTransitions (beginTransition (blockOpening (r191ChildGapBlocks 2 (There (There Here)))))
        (blockBody (r191ChildGapBlocks 2 (There (There Here)))))))
  (noEarlierLifecycle (r191ChildGapBlocks 0 Here))
  (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible)
    (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible)
      (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible)
        (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible) NoLifecycleByEnd))))
  (blockActiveAtFinal (r191ChildGapBlocks 0 Here)) Refl

||| A located occurrence INSIDE the extended parent body, not merely in the
||| same global trace or at a guessed ordinal. Its prefix is the old body.
public export
0 r191RetireInsideParent : LocatedActionOccurrence (ORetire 3)
  (extendedBody r191RelocatedParentBlock)
r191RetireInsideParent = MkLocatedActionOccurrence
  (r191ChildGapState 6) (exchangeMiddle r191BeginRetireExchange)
  (blockBody (r191ChildGapBlocks 0 Here))
  (Fired {before = r191ChildGapState 6} {afterState = exchangeMiddle r191BeginRetireExchange}
    r45NameEq r45KeyEq (ORetire 3) ORetireTag (exchangeEarlyChecked r191BeginRetireExchange))
  NoTransitions Refl Refl
