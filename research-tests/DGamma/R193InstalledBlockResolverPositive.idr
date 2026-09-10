module DGamma.R193InstalledBlockResolverPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Section3Example
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20BlockResolverFrameSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Concrete provider-backed host cut: a live ServiceA provider and two
||| dependent, provision-empty siblings. This is an executable well-formed
||| INITIAL CUT for a native physical-frame regression, not an asserted
||| original/canonical history or tagged-child registration discipline.
||| The prior callback-driven setup remains in the rejected E66-1 snapshot;
||| it did not normalize across the imported callback boundary. No claim that
||| its runtime computation fails follows from that elaboration rejection.
public export
r193FrameBefore : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameBefore = MkSystemState (MkToyRuntime True False)
  (insertBinding 1 (freshFiber emptyConsumerComponent Root)
    (insertBinding 2 (freshFiber emptyConsumerComponent Root)
      (insertBinding 0 (MkFiber DGamma.CalculusChecks.providerComponent Root False (ownedA True)
        (Active id EmptyView)) emptyContext Refl) Refl) Refl)

public export
r193FrameStart : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameStart = fromMaybe r193FrameBefore (applyTagged LBeginTag (LBegin 2) r193FrameBefore)

public export
r193FrameChild : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameChild = fromMaybe r193FrameStart (applyTagged OInsertTag (OInsert 3 (ChildOf 2) emptyConsumerComponent) r193FrameStart)

public export
r193FrameEnd : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameEnd = fromMaybe r193FrameChild (applyTagged LFinishTag (LAdvance 2) r193FrameChild)

public export
r193FrameRightStart : SystemState Nat ToyKey ToyValue ToyRuntime String
r193FrameRightStart = fromMaybe r193FrameEnd (applyTagged LBeginTag (LBegin 1) r193FrameEnd)

||| Actual checked Begin authenticates the concrete provider-backed host cut.
public export
0 r193FrameLeftOpening : BeginStep %search %search 2 r193FrameBefore r193FrameStart
r193FrameLeftOpening = MkBeginStep Refl

||| Both real body edges: native inactive child insertion followed by Finish.
public export
0 r193FrameBody : Transitions r193FrameStart r193FrameEnd
r193FrameBody =
  MoreTransitions (Fired {before = r193FrameStart} {afterState = r193FrameChild} %search %search
    (OInsert 3 (ChildOf 2) emptyConsumerComponent) OInsertTag Refl)
    (MoreTransitions (Fired {before = r193FrameChild} {afterState = r193FrameEnd} %search %search
      (LAdvance 2) LFinishTag Refl) NoTransitions)

public export
0 r193FrameRightOpening : BeginStep %search %search 1 r193FrameEnd r193FrameRightStart
r193FrameRightOpening = MkBeginStep Refl

public export
0 r193FrameInstalled : InstalledTrace Nat ToyKey ToyRuntime String ToyValue %search %search 2 r193FrameBody
r193FrameInstalled =
  InstalledStep (OInsert 3 (ChildOf 2) emptyConsumerComponent) OInsertTag Refl
    (MoreTransitions (Fired {before = r193FrameChild} {afterState = r193FrameEnd} %search %search
      (LAdvance 2) LFinishTag Refl) NoTransitions) Refl
    (InstalledStep (LAdvance 2) LFinishTag Refl NoTransitions Refl (InstalledEnd Refl))

public export
0 r193FrameActorOnly : ActorLifecycleOnly 2 r193FrameBody
r193FrameActorOnly = ActorYieldedRegistrationStep _ _ Refl
  (ActorLifecycleStep _ _ Refl Refl ActorLifecycleEnd)

public export
0 r193FrameNoRightChild : NoGeneratedChild 1 r193FrameBody
r193FrameNoRightChild =
  NoGeneratedChildStep _ _ (\parent, component, same => case same of Refl impossible)
    (NoGeneratedChildStep _ _ (\parent, component, same => case same of Refl impossible) NoGeneratedChildEnd)

public export
r193FrameLastFiber : Fiber Nat ToyKey ToyValue ToyRuntime String
r193FrameLastFiber = fromMaybe (freshFiber emptyConsumerComponent Root)
  (lookupFiber 2 (registry r193FrameEnd))

||| Apply the WHOLE native transport theorem: no owner/resolver frame or
||| pre-left right-Begin success was supplied. The concrete physical gap is
||| empty; this does not derive a zero gap for arbitrary canonical schedules.
public export
0 r193FrameEarlierRightBegin :
  CheckedEarlyApplication Nat ToyKey ToyRuntime String ToyValue %search %search r193FrameBefore (LBegin 1) LBeginTag
r193FrameEarlierRightBegin =
  o20DisjointBlockActualEarlierBegin %search %search 2 1 (\Refl impossible)
    r193FrameBefore r193FrameStart r193FrameEnd r193FrameEnd r193FrameRightStart
    r193FrameLeftOpening r193FrameRightOpening r193FrameBody r193FrameInstalled r193FrameActorOnly r193FrameNoRightChild
    NoTransitions Refl Refl r193FrameLastFiber Refl (\wanted, needed, provided => absurd provided)

||| Nonempty coeffect query really resolves to live provider0 on BOTH sides;
||| this is not merely the vacuous resolver frame for an empty dependency list.
public export
0 r193FrameNonemptyResolution :
  ((resolveView {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime} {error = String}
      [ServiceA] (registry r193FrameBefore),
    resolveView {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime} {error = String}
      [ServiceA] (registry r193FrameEnd)) =
   (Just (ProviderView 0 EmptyView), Just (ProviderView 0 EmptyView)))
r193FrameNonemptyResolution = Refl

||| The same concrete nonempty query is related by the generic whole-block
||| theorem, rather than accepting the desired resolver equality as an input.
public export
0 r193FrameWholeResolverEquality :
  (resolveView {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime} {error = String}
      [ServiceA] (registry r193FrameEnd) =
   resolveView {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime} {error = String}
      [ServiceA] (registry r193FrameBefore))
r193FrameWholeResolverEquality =
  o20WholeInstalledBlockResolver %search %search 2 [ServiceA] r193FrameBefore r193FrameStart r193FrameEnd
    r193FrameLeftOpening r193FrameBody r193FrameInstalled r193FrameActorOnly r193FrameLastFiber Refl
    (\wanted, needed, provided => absurd provided)
