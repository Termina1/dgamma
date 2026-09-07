module DGamma.R181O19LocatedBlocks

import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.CP5ObservedInstalledLifecycleSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.R179O19ObservedExecution
import DGamma.R180O19ObservedCompletion
import DGamma.R181O19SafetyCompletion
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| E1: the two actual post-Begin provider edges already in the count7 trace.
||| Exact checked witnesses are preserved, including the stored dictionaries.
public export
0 r181ProviderBlockBody : Transitions r179ObservedProviderBegin r179ObservedProviderFinished
r181ProviderBlockBody =
  MoreTransitions
    (Fired {before = r179ObservedProviderBegin} {afterState = r179ObservedProviderCut}
      %search %search (LAdvance 0) LIterTag (Builtin.fst (Builtin.snd r179ObservedProviderEdges)))
    (MoreTransitions
      (Fired {before = r179ObservedProviderCut} {afterState = r179ObservedProviderFinished}
        %search %search (LAdvance 0) LFinishTag
        (Builtin.fst (Builtin.snd (Builtin.snd r179ObservedProviderEdges)))) NoTransitions)

||| E2: exact consumer Finish witness from the actual whole trace, not a
||| propositionally equal replacement checked proof at the same endpoint.
public export
0 r181ConsumerBlockBody : Transitions r180ObservedConsumerBegun r180ObservedConsumerFinished
r181ConsumerBlockBody = MoreTransitions
  (Fired {before = r180ObservedConsumerBegun} {afterState = r180ObservedConsumerFinished}
    %search %search (LAdvance 1) LFinishTag
    (r180CheckedFromPrerequisites (LAdvance 1) r180ObservedConsumerBegun
      r180ObservedConsumerFinished LFinishTag r180ConsumerFinishRaw
      (Builtin.snd r180ObservedLifecycleSuffix))) NoTransitions

||| E3: full installed traces, including BOTH body endpoints, obtained by
||| projecting the five ACTUAL lifecycle observations from A16. No callback
||| conversion, endpoint-only substitution or assumed InstalledTrace remains.
public export
0 r181BlockBodiesInstalled :
  (InstalledTrace Nat ToyKey ToyRuntime String ToyValue (the (DecEq Nat) %search)
    (the (DecEq ToyKey) %search) 0 r181ProviderBlockBody,
   InstalledTrace Nat ToyKey ToyRuntime String ToyValue (the (DecEq Nat) %search)
    (the (DecEq ToyKey) %search) 1 r181ConsumerBlockBody)
r181BlockBodiesInstalled =
  (InstalledStep (LAdvance 0) LIterTag
    (Builtin.fst (Builtin.snd r179ObservedProviderEdges)) _
    (installedFromCutObservation Nat ToyKey ToyRuntime String ToyValue %search 0
      r179ObservedProviderBegin (Builtin.fst r181LifecycleCutObservations))
    (InstalledStep (LAdvance 0) LFinishTag
      (Builtin.fst (Builtin.snd (Builtin.snd r179ObservedProviderEdges))) _
      (installedFromCutObservation Nat ToyKey ToyRuntime String ToyValue %search 0
        r179ObservedProviderCut (Builtin.fst (Builtin.snd r181LifecycleCutObservations)))
      (InstalledEnd (installedFromCutObservation Nat ToyKey ToyRuntime String ToyValue %search 0
        r179ObservedProviderFinished
        (Builtin.fst (Builtin.snd (Builtin.snd r181LifecycleCutObservations)))))),
   InstalledStep (LAdvance 1) LFinishTag
    (r180CheckedFromPrerequisites (LAdvance 1) r180ObservedConsumerBegun
      r180ObservedConsumerFinished LFinishTag r180ConsumerFinishRaw
      (Builtin.snd r180ObservedLifecycleSuffix)) _
    (installedFromCutObservation Nat ToyKey ToyRuntime String ToyValue %search 1
      r180ObservedConsumerBegun
      (Builtin.fst (Builtin.snd (Builtin.snd (Builtin.snd r181LifecycleCutObservations)))))
    (InstalledEnd (installedFromCutObservation Nat ToyKey ToyRuntime String ToyValue %search 1
      r180ObservedConsumerFinished
      (Builtin.snd (Builtin.snd (Builtin.snd (Builtin.snd r181LifecycleCutObservations)))))))

||| E4: exact root prefix before the provider's located block. This is the
||| same two-node checked constructor spine used by r181WholeTrace.
public export
0 r181BeforeProviderBlock : Transitions
  (MkSystemState (MkToyRuntime False False)
    (emptyContext {key = Nat} {value = \n => Fiber Nat ToyKey ToyValue ToyRuntime String}))
  r179ObservedRootSource
r181BeforeProviderBlock =
  MoreTransitions
    (Fired {before = MkSystemState (MkToyRuntime False False) emptyContext}
      {afterState = MkSystemState (MkToyRuntime False False)
        (insertBinding 0 (freshFiber DGamma.CalculusChecks.providerComponent Root) emptyContext Refl)}
      %search %search (OInsert 0 Root DGamma.CalculusChecks.providerComponent) OInsertTag Refl)
    (MoreTransitions
      (Fired {before = MkSystemState (MkToyRuntime False False)
          (insertBinding 0 (freshFiber DGamma.CalculusChecks.providerComponent Root) emptyContext Refl)}
        {afterState = r179ObservedRootSource}
        %search %search (OInsert 1 Root DGamma.CalculusChecks.emptyConsumerComponent) OInsertTag Refl)
      NoTransitions)

||| E5: authentic THREE-edge provider block located in the SAME count7 trace.
||| All installed, actor-only, exclusion, final Active and decomposition fields
||| are constructed; no block is received as an input or guessed from an endpoint.
public export
0 r181ProviderLocatedBlock : LocatedOpenEpisodeBlock Nat ToyKey ToyRuntime String
  ToyValue (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) 0 r181WholeTrace
r181ProviderLocatedBlock = MkLocatedOpenEpisodeBlock
  r179ObservedRootSource r179ObservedProviderBegin r179ObservedProviderFinished
  r181BeforeProviderBlock (MkBeginStep (Builtin.fst r179ObservedProviderEdges))
  r181ProviderBlockBody (Builtin.fst r181BlockBodiesInstalled)
  (ActorLifecycleStep _ _ Refl Refl
    (ActorLifecycleStep _ _ Refl Refl ActorLifecycleEnd))
  (MoreTransitions (beginTransition r180ConsumerBeginFromPrerequisites) r181ConsumerBlockBody)
  (NoLifecycleByStep _ _ (\life => case life of Refl impossible)
    (NoLifecycleByStep _ _ (\life => case life of Refl impossible) NoLifecycleByEnd))
  (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible)
    (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible) NoLifecycleByEnd))
  (Builtin.fst (Builtin.snd (Builtin.snd r181EndpointReady))) Refl

||| E6: authentic TWO-edge consumer block in the SAME whole trace. Its exact
||| prefix includes the provider's completed block; only orchestration of actor1
||| precedes its Begin, and no lifecycle of actor1 occurs earlier or later.
public export
0 r181ConsumerLocatedBlock : LocatedOpenEpisodeBlock Nat ToyKey ToyRuntime String
  ToyValue (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) 1 r181WholeTrace
r181ConsumerLocatedBlock = MkLocatedOpenEpisodeBlock
  r179ObservedProviderFinished r180ObservedConsumerBegun r180ObservedConsumerFinished
  (appendTransitions r181BeforeProviderBlock
    (MoreTransitions (beginTransition (MkBeginStep (Builtin.fst r179ObservedProviderEdges)))
      r181ProviderBlockBody))
  r180ConsumerBeginFromPrerequisites r181ConsumerBlockBody
  (Builtin.snd r181BlockBodiesInstalled)
  (ActorLifecycleStep _ _ Refl Refl ActorLifecycleEnd) NoTransitions
  (NoLifecycleByStep _ _ (\life => case life of Refl impossible)
    (NoLifecycleByStep _ _ (\life => case life of Refl impossible)
      (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible)
        (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible)
          (NoLifecycleByStep _ _ (\life, same => case same of Refl impossible)
            NoLifecycleByEnd))))) NoLifecycleByEnd
  (Builtin.snd (Builtin.snd (Builtin.snd r181EndpointReady))) Refl

||| E7: exact same-trace block ordering, with zero intervening transitions.
||| This is a structural constructor-spine identity, not a numeric observer
||| over a nested certified execution builder.
public export
0 r181ProviderBeforeConsumer : BlockBefore Nat ToyKey ToyRuntime String ToyValue
  (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) r181WholeTrace 0 1
  r181ProviderLocatedBlock r181ConsumerLocatedBlock
r181ProviderBeforeConsumer = MkBlockBefore NoTransitions Refl

||| E8: complete lifecycle coverage for all seven ACTUAL transitions. The two
||| root insertions are orchestration; the five lifecycle actors are exactly0/1.
||| This does not assert the remaining numeric disjoint-range/decomposition law.
public export
0 r181BlockLifecycleCoverage : LifecycleActorsCovered [0, 1] r181WholeTrace
r181BlockLifecycleCoverage =
  CoveredOrchestrationStep _ _ Refl
    (CoveredOrchestrationStep _ _ Refl
      (CoveredLifecycleStep _ _ Refl Here
        (CoveredLifecycleStep _ _ Refl Here
          (CoveredLifecycleStep _ _ Refl Here
            (CoveredLifecycleStep _ _ Refl (There Here)
              (CoveredLifecycleStep _ _ Refl (There Here) LifecycleActorsCoveredEnd))))))
