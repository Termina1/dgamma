module DGamma.R181O19LocatedBlocks

import DGamma.Calculus
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
