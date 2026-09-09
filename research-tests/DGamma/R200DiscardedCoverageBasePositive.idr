module DGamma.R200DiscardedCoverageBasePositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DiscardedSelectionCoverageSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R193VestigialHistoryTransportPositive
import DGamma.R195EndpointRebaseBoundaryPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The unchanged eight native R193 edges have the exact fixture dictionaries.
||| The checked equations are taken verbatim from those actual transitions.
public export
0 r200HistoricalAligned :
  AlignedTransitions Nat R45Key Unit String R45Value r45NameEq r45KeyEq r193HistoricalClosedTrace
r200HistoricalAligned =
  AlignedStep (OInsert 0 Root r45Parent) OInsertTag
    r45ParentInsertChecked _ (
  AlignedStep (LBegin 0) LBeginTag
    r45BeginChecked _ (
  AlignedStep (OInsert 1 (ChildOf 0) r45Child) OInsertTag
    r45ChildInsertChecked _ (
  AlignedStep (LAdvance 0) LFinishTag
    (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LAdvance 0) r45SourcePairFinal r178ParentDoneState LFinishTag
    (checkedTransitionTargetValid r45ChildInsert) Refl) _ (
  AlignedStep (ORetire 1) ORetireTag
    (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (ORetire 1) r178ParentDoneState r178RightFinal ORetireTag
    (checkedTransitionTargetValid r178ParentFinish) Refl) _ (
  AlignedStep (ORetire 0) ORetireTag
    (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (ORetire 0) r178RightFinal r193HistoricalParentRetired ORetireTag
    (checkedTransitionTargetValid r178ChildRetire) Refl) _ (
  AlignedStep (LLeave 0) LLeaveTag
    (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LLeave 0) r193HistoricalParentRetired r193HistoricalLeaving LLeaveTag
    (checkedTransitionTargetValid r193HistoricalRetire) Refl) _ (
  AlignedStep (LUnload 0) LUnloadTag
    (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LUnload 0) r193HistoricalLeaving r193HistoricalClosed LUnloadTag
    (checkedTransitionTargetValid r193HistoricalLeave) Refl) _ (
  AlignedEnd))))))))

||| The actual R193/R195 present-vestigial history cannot inhabit the empty
||| closing-free base. Both alignment and the FULL accepted packet are owned;
||| no canonical schedule is fabricated by this negative boundary control.
export
0 r200HistoricalNotClosingFree :
  (NoClosingEpisodes Nat R45Key Unit String R45Value r45NameEq r45KeyEq r193HistoricalClosedTrace -> Void)
r200HistoricalNotClosingFree noClosing =
  o20ClosingFreeNoPresentVestigial Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    r193HistoricalClosedTrace r193HistoricalClosedTrace identityRegistrationGenerationBijection
    r193HistoricalTree r200HistoricalAligned Refl noClosing 1 r195MismatchOwnsVestigialRemainder
