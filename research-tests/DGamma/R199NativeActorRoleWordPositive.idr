module DGamma.R199NativeActorRoleWordPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import DGamma.CP5O20ProgramRoleWordSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R191CanonicalChildRetirementGap
import DGamma.R193VestigialHistoryTransportPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Two NATIVE parent-body fold instances, using unchanged cuts from the
||| eleven-edge R191 pair and the eight-edge R193/R195 closing/vestigial pair.
||| Each actual yielded Insert is retained in the physical trace while the
||| lifecycle-only projection consumes Finish. These are body-fold fixtures,
||| NOT instances of the still-open universal canonical modulo synchronizer.
export
0 r199NativeParentRoleWords :
  ((o20FiberRoleRemainder (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq} 0 (registry (r191ChildGapState 4))) =
     [LFinishTag] ++ o20FiberRoleRemainder (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq} 0 (registry (r191ChildGapState 6)))),
   (o20FiberRoleRemainder (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq} 0 (registry r45AfterBegin)) =
     [LFinishTag] ++ o20FiberRoleRemainder (lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} @{r45NameEq} 0 (registry r178ParentDoneState))))
r199NativeParentRoleWords =
  (o20ActorRoleWordInvariant {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} r45NameEq r45KeyEq 0
    (MoreTransitions
      (Fired {before = r191ChildGapState 4} {afterState = r191ChildGapState 5}
        r45NameEq r45KeyEq (OInsert 3 (ChildOf 0) r45Child) OInsertTag Refl)
      (MoreTransitions
        (Fired {before = r191ChildGapState 5} {afterState = r191ChildGapState 6}
          r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) NoTransitions))
    (ActorYieldedRegistrationStep _ _ Refl (ActorLifecycleStep _ _ Refl Refl ActorLifecycleEnd))
    (O20RolesStep (Right (PaperInsertStep Refl)) (O20RolesStep (Left (PaperFinishStep Refl Refl)) O20RolesEnd))
    (InstalledStep (OInsert 3 (ChildOf 0) r45Child) OInsertTag Refl _ Refl
      (InstalledStep (LAdvance 0) LFinishTag Refl _ Refl (InstalledEnd Refl))),
   o20ActorRoleWordInvariant {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String} r45NameEq r45KeyEq 0
    (MoreTransitions r45ChildInsert (MoreTransitions r178ParentFinish NoTransitions))
    (ActorYieldedRegistrationStep _ _ Refl (ActorLifecycleStep _ _ Refl Refl ActorLifecycleEnd))
    (O20RolesStep (Right (PaperInsertStep Refl)) (O20RolesStep (Left (PaperFinishStep Refl Refl)) O20RolesEnd))
    (InstalledStep (OInsert 1 (ChildOf 0) r45Child) OInsertTag r45ChildInsertChecked _ Refl
      (InstalledStep (LAdvance 0) LFinishTag
        (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
          (LAdvance 0) r45SourcePairFinal r178ParentDoneState LFinishTag
          (checkedTransitionTargetValid r45ChildInsert) Refl)
        _ Refl (InstalledEnd Refl))))
