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

||| Designated dictionaries for all seven actual checked nodes.
export
0 r181TraceAligned : AlignedTransitions Nat ToyKey ToyRuntime String ToyValue
  (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) r181WholeTrace
r181TraceAligned =
  AlignedStep (OInsert 0 Root providerComponent) OInsertTag Refl _
    (AlignedStep (OInsert 1 Root emptyConsumerComponent) OInsertTag Refl _
      (AlignedStep (LBegin 0) LBeginTag (fst r179ObservedProviderEdges) _
        (AlignedStep (LAdvance 0) LIterTag (fst (snd r179ObservedProviderEdges)) _
          (AlignedStep (LAdvance 0) LFinishTag (fst (snd (snd r179ObservedProviderEdges))) _
            (AlignedStep (LBegin 1) LBeginTag
              (beginEquation r180ConsumerBeginFromPrerequisites) _
              (AlignedStep (LAdvance 1) LFinishTag
                (r180CheckedFromPrerequisites (LAdvance 1) r180ObservedConsumerBegun
                  r180ObservedConsumerFinished LFinishTag r180ConsumerFinishRaw
                  (snd r180ObservedLifecycleSuffix)) _ AlignedEnd))))))

||| Observe the ACTUAL provider table at the final endpoint before reducing
||| its quietness guard. The presence equation is closed by the next producer.
export
0 r181EndpointObserved :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (0 tableObserved : (restrictOwnedPreservingOrder @{%search}
    DGamma.Section3Example.toySpecA (ownedValues (ownedA True)) = table)) ->
  (binding : Maybe Bool) ->
  (0 bindingObserved : (lookupBinding @{%search} ServiceA (ownedValues table) = binding)) ->
  (0 present : (isJust binding = True)) ->
  ((quiet {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime}
      {error = String} @{%search} @{%search} r180ObservedConsumerFinished = True),
   (noFailedFibers r180ObservedConsumerFinished = True),
   (supportedActiveAt {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} @{%search} 0 r180ObservedConsumerFinished = True),
   (supportedActiveAt {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} @{%search} 1 r180ObservedConsumerFinished = True))
r181EndpointObserved table tableObserved Nothing bindingObserved present =
  case present of Refl impossible
r181EndpointObserved table tableObserved (Just service) bindingObserved present =
  rewrite tableObserved in rewrite bindingObserved in (Refl, Refl, Refl, Refl)
