module DGamma.R137O8RawNameReuseCountershapeTrace

import DGamma.R137O8RawNameReuseCountershape
import DGamma.Calculus
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP5ConfluenceDeletionChainSpike
import Decidable.Equality

%default total
%unbound_implicits off

0 r137Checked :
  (action : Action R137Name R137Key R137Value Unit Unit) ->
  (before, afterState : SystemState R137Name R137Key R137Value Unit Unit) ->
  (tag : RuleTag) ->
  applyAction @{r137NameEq} @{r137KeyEq} action before = Just (tag, afterState) ->
  registryWellFormed @{r137NameEq} @{r137KeyEq} afterState = True ->
  checkedApplyAction @{r137NameEq} @{r137KeyEq} action before =
    Just (tag, afterState)
r137Checked action before afterState tag raw targetWellFormed =
  rewrite raw in rewrite targetWellFormed in Refl

public export
0 r137C0 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (OInsert Anchor Root r137AnchorComponent) r137S0 = Just (OInsertTag, r137S1)
r137C0 = r137Checked _ _ _ _ r137E0 r137W1
public export
0 r137C1 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LBegin Anchor) r137S1 = Just (LBeginTag, r137S2)
r137C1 = r137Checked _ _ _ _ r137E1 r137W2
public export
0 r137C2 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LAdvance Anchor) r137S2 = Just (LFinishTag, r137S3)
r137C2 = r137Checked _ _ _ _ r137E2 r137W3
public export
0 r137C3 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (OInsert ActorA Root r137FirstAComponent) r137S3 = Just (OInsertTag, r137S4)
r137C3 = r137Checked _ _ _ _ r137E3 r137W4
public export
0 r137C4 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorA) r137S4 = Just (LBeginTag, r137S5)
r137C4 = r137Checked _ _ _ _ r137E4 r137W5
public export
0 r137C5 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorA) r137S5 = Just (LFinishTag, r137S6)
r137C5 = r137Checked _ _ _ _ r137E5 r137W6
public export
0 r137C6 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (OInsert ActorB Root r137ConsumerComponent) r137S6 = Just (OInsertTag, r137S7)
r137C6 = r137Checked _ _ _ _ r137E6 r137W7
public export
0 r137C7 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorB) r137S7 = Just (LBeginTag, r137S8)
r137C7 = r137Checked _ _ _ _ r137E7 r137W8
public export
0 r137C8 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorB) r137S8 = Just (LRaiseTag, r137S9)
r137C8 = r137Checked _ _ _ _ r137E8 r137W9
public export
0 r137C9 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LUnload ActorB) r137S9 = Just (LUnloadTag, r137S10)
r137C9 = r137Checked _ _ _ _ r137E9 r137W10
public export
0 r137C10 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (ORetire ActorB) r137S10 = Just (ORetireTag, r137S11)
r137C10 = r137Checked _ _ _ _ r137E10 r137W11
public export
0 r137C11 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (ORemove ActorB) r137S11 = Just (ORemoveTag, r137S12)
r137C11 = r137Checked _ _ _ _ r137E11 r137W12
public export
0 r137C12 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (ORetire Anchor) r137S12 = Just (ORetireTag, r137S13)
r137C12 = r137Checked _ _ _ _ r137E12 r137W13
public export
0 r137C13 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (ORetire ActorA) r137S13 = Just (ORetireTag, r137S14)
r137C13 = r137Checked _ _ _ _ r137E13 r137W14
public export
0 r137C14 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LLeave ActorA) r137S14 = Just (LLeaveTag, r137S15)
r137C14 = r137Checked _ _ _ _ r137E14 r137W15
public export
0 r137C15 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LUnload ActorA) r137S15 = Just (LUnloadTag, r137S16)
r137C15 = r137Checked _ _ _ _ r137E15 r137W16
public export
0 r137C16 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (ORemove ActorA) r137S16 = Just (ORemoveTag, r137S17)
r137C16 = r137Checked _ _ _ _ r137E16 r137W17
public export
0 r137C17 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (OInsert ActorB Root r137SecondBComponent) r137S17 = Just (OInsertTag, r137S18)
r137C17 = r137Checked _ _ _ _ r137E17 r137W18
public export
0 r137C18 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorB) r137S18 = Just (LBeginTag, r137S19)
r137C18 = r137Checked _ _ _ _ r137E18 r137W19
public export
0 r137C19 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorB) r137S19 = Just (LFinishTag, r137S20)
r137C19 = r137Checked _ _ _ _ r137E19 r137W20
public export
0 r137C20 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (OInsert ActorA Root r137ConsumerComponent) r137S20 = Just (OInsertTag, r137S21)
r137C20 = r137Checked _ _ _ _ r137E20 r137W21
public export
0 r137C21 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LBegin ActorA) r137S21 = Just (LBeginTag, r137S22)
r137C21 = r137Checked _ _ _ _ r137E21 r137W22
public export
0 r137C22 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LAdvance ActorA) r137S22 = Just (LRaiseTag, r137S23)
r137C22 = r137Checked _ _ _ _ r137E22 r137W23
public export
0 r137C23 : checkedApplyAction @{r137NameEq} @{r137KeyEq} (LUnload ActorA) r137S23 = Just (LUnloadTag, r137S24)
r137C23 = r137Checked _ _ _ _ r137E23 r137W24

public export
r137T0 : Transition r137S0 r137S1
r137T0 = Fired r137NameEq r137KeyEq (OInsert Anchor Root r137AnchorComponent) OInsertTag r137C0
public export
r137T1 : Transition r137S1 r137S2
r137T1 = Fired r137NameEq r137KeyEq (LBegin Anchor) LBeginTag r137C1
public export
r137T2 : Transition r137S2 r137S3
r137T2 = Fired r137NameEq r137KeyEq (LAdvance Anchor) LFinishTag r137C2
public export
r137T3 : Transition r137S3 r137S4
r137T3 = Fired r137NameEq r137KeyEq (OInsert ActorA Root r137FirstAComponent) OInsertTag r137C3
public export
r137T4 : Transition r137S4 r137S5
r137T4 = Fired r137NameEq r137KeyEq (LBegin ActorA) LBeginTag r137C4
public export
r137T5 : Transition r137S5 r137S6
r137T5 = Fired r137NameEq r137KeyEq (LAdvance ActorA) LFinishTag r137C5
public export
r137T6 : Transition r137S6 r137S7
r137T6 = Fired r137NameEq r137KeyEq (OInsert ActorB Root r137ConsumerComponent) OInsertTag r137C6
public export
r137T7 : Transition r137S7 r137S8
r137T7 = Fired r137NameEq r137KeyEq (LBegin ActorB) LBeginTag r137C7
public export
r137T8 : Transition r137S8 r137S9
r137T8 = Fired r137NameEq r137KeyEq (LAdvance ActorB) LRaiseTag r137C8
public export
r137T9 : Transition r137S9 r137S10
r137T9 = Fired r137NameEq r137KeyEq (LUnload ActorB) LUnloadTag r137C9
public export
r137T10 : Transition r137S10 r137S11
r137T10 = Fired r137NameEq r137KeyEq (ORetire ActorB) ORetireTag r137C10
public export
r137T11 : Transition r137S11 r137S12
r137T11 = Fired r137NameEq r137KeyEq (ORemove ActorB) ORemoveTag r137C11
public export
r137T12 : Transition r137S12 r137S13
r137T12 = Fired r137NameEq r137KeyEq (ORetire Anchor) ORetireTag r137C12
public export
r137T13 : Transition r137S13 r137S14
r137T13 = Fired r137NameEq r137KeyEq (ORetire ActorA) ORetireTag r137C13
public export
r137T14 : Transition r137S14 r137S15
r137T14 = Fired r137NameEq r137KeyEq (LLeave ActorA) LLeaveTag r137C14
public export
r137T15 : Transition r137S15 r137S16
r137T15 = Fired r137NameEq r137KeyEq (LUnload ActorA) LUnloadTag r137C15
public export
r137T16 : Transition r137S16 r137S17
r137T16 = Fired r137NameEq r137KeyEq (ORemove ActorA) ORemoveTag r137C16
public export
r137T17 : Transition r137S17 r137S18
r137T17 = Fired r137NameEq r137KeyEq (OInsert ActorB Root r137SecondBComponent) OInsertTag r137C17
public export
r137T18 : Transition r137S18 r137S19
r137T18 = Fired r137NameEq r137KeyEq (LBegin ActorB) LBeginTag r137C18
public export
r137T19 : Transition r137S19 r137S20
r137T19 = Fired r137NameEq r137KeyEq (LAdvance ActorB) LFinishTag r137C19
public export
r137T20 : Transition r137S20 r137S21
r137T20 = Fired r137NameEq r137KeyEq (OInsert ActorA Root r137ConsumerComponent) OInsertTag r137C20
public export
r137T21 : Transition r137S21 r137S22
r137T21 = Fired r137NameEq r137KeyEq (LBegin ActorA) LBeginTag r137C21
public export
r137T22 : Transition r137S22 r137S23
r137T22 = Fired r137NameEq r137KeyEq (LAdvance ActorA) LRaiseTag r137C22
public export
r137T23 : Transition r137S23 r137S24
r137T23 = Fired r137NameEq r137KeyEq (LUnload ActorA) LUnloadTag r137C23

public export
r137Trace : Transitions r137S0 r137S24
r137Trace =
  MoreTransitions r137T0 (MoreTransitions r137T1
  (MoreTransitions r137T2 (MoreTransitions r137T3
  (MoreTransitions r137T4 (MoreTransitions r137T5
  (MoreTransitions r137T6 (MoreTransitions r137T7
  (MoreTransitions r137T8 (MoreTransitions r137T9
  (MoreTransitions r137T10 (MoreTransitions r137T11
  (MoreTransitions r137T12 (MoreTransitions r137T13
  (MoreTransitions r137T14 (MoreTransitions r137T15
  (MoreTransitions r137T16 (MoreTransitions r137T17
  (MoreTransitions r137T18 (MoreTransitions r137T19
  (MoreTransitions r137T20 (MoreTransitions r137T21
  (MoreTransitions r137T22 (MoreTransitions r137T23 NoTransitions)))))))))))))))))))))))

public export
0 r137Action5 : transitionAction r137T5 = LAdvance ActorA
r137Action5 = Refl
public export
0 r137Action6 : transitionAction r137T6 = OInsert ActorB Root r137ConsumerComponent
r137Action6 = Refl
public export
0 r137Action7 : transitionAction r137T7 = LBegin ActorB
r137Action7 = Refl
public export
0 r137Action8 : transitionAction r137T8 = LAdvance ActorB
r137Action8 = Refl
public export
0 r137Action9 : transitionAction r137T9 = LUnload ActorB
r137Action9 = Refl
