module DGamma.R181O19SafetyCompletion

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import DGamma.R179O19ObservedExecution
import DGamma.R180O19ObservedCompletion
import Data.Maybe
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The ACTUAL two root insertions and five already-proved lifecycle edges,
||| at the same named endpoints. No certified Maybe builder/fallback is used.
||| The transparent constructor spine owns all later source coordinates.
public export
0 r181WholeTrace : Transitions
  (MkSystemState (MkToyRuntime False False)
    (emptyContext {key = Nat} {value = \n => Fiber Nat ToyKey ToyValue ToyRuntime String}))
  r180ObservedConsumerFinished
r181WholeTrace =
  MoreTransitions
    (Fired {before = MkSystemState (MkToyRuntime False False) emptyContext}
      {afterState = MkSystemState (MkToyRuntime False False)
        (insertBinding 0 (freshFiber providerComponent Root) emptyContext Refl)}
      %search %search (OInsert 0 Root providerComponent) OInsertTag Refl)
    (MoreTransitions
      (Fired {before = MkSystemState (MkToyRuntime False False)
          (insertBinding 0 (freshFiber providerComponent Root) emptyContext Refl)}
        {afterState = r179ObservedRootSource}
        %search %search (OInsert 1 Root emptyConsumerComponent) OInsertTag Refl)
      (MoreTransitions
        (Fired {before = r179ObservedRootSource} {afterState = r179ObservedProviderBegin}
          %search %search (LBegin 0) LBeginTag (fst r179ObservedProviderEdges))
        (MoreTransitions
          (Fired {before = r179ObservedProviderBegin} {afterState = r179ObservedProviderCut}
            %search %search (LAdvance 0) LIterTag (fst (snd r179ObservedProviderEdges)))
          (MoreTransitions
            (Fired {before = r179ObservedProviderCut} {afterState = r179ObservedProviderFinished}
              %search %search (LAdvance 0) LFinishTag (fst (snd (snd r179ObservedProviderEdges))))
            (MoreTransitions (beginTransition r180ConsumerBeginFromPrerequisites)
              (MoreTransitions
                (Fired {before = r180ObservedConsumerBegun} {afterState = r180ObservedConsumerFinished}
                  %search %search (LAdvance 1) LFinishTag
                  (r180CheckedFromPrerequisites (LAdvance 1) r180ObservedConsumerBegun
                    r180ObservedConsumerFinished LFinishTag r180ConsumerFinishRaw
                    (snd r180ObservedLifecycleSuffix)))
                NoTransitions))))))
