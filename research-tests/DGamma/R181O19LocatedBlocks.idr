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
