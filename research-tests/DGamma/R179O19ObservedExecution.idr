module DGamma.R179O19ObservedExecution

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import Data.Maybe
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Explicit root-insertion source. No certified Maybe builder is unfolded.
||| Subsequent exact checked equations must authenticate all runtime outputs.
public export
r179ObservedRootSource : SystemState Nat ToyKey ToyValue ToyRuntime String
r179ObservedRootSource = MkSystemState (MkToyRuntime False False)
  (insertBinding 1 (freshFiber emptyConsumerComponent Root)
    (insertBinding 0 (freshFiber providerComponent Root) emptyContext Refl) Refl)

||| Explicit L-Begin output for the provider; exact input/output equation later.
public export
r179ObservedProviderBegin : SystemState Nat ToyKey ToyValue ToyRuntime String
r179ObservedProviderBegin = MkSystemState (MkToyRuntime False False)
  (replaceBinding 0
    (MkFiber providerComponent Root False emptyOwned
      (Reloading [providerInstall, providerFinish] id EmptyView))
    (registry r179ObservedRootSource))

||| Observe the actual iterator output, including its real accumulator/table.
||| A later exact equation excludes this one-step observer's default branch.
public export
r179ObservedProviderCut : SystemState Nat ToyKey ToyValue ToyRuntime String
r179ObservedProviderCut = maybe r179ObservedProviderBegin snd
  (applyAction (LAdvance 0) r179ObservedProviderBegin)

||| Observe the real provider Finish payload rather than invent its accumulator.
||| The next packet authenticates this target and its consumer resolution.
public export
r179ObservedProviderFinished : SystemState Nat ToyKey ToyValue ToyRuntime String
r179ObservedProviderFinished = maybe r179ObservedProviderCut snd
  (applyAction (LAdvance 0) r179ObservedProviderCut)

||| Single-purpose provider edges/WF capital after A11's composite stop.
||| This excludes every consumer target or consumer-transition claim.
export
0 r179ObservedProviderEdges :
  ((checkedApplyAction (LBegin 0) r179ObservedRootSource = Just (LBeginTag, r179ObservedProviderBegin)),
   (checkedApplyAction (LAdvance 0) r179ObservedProviderBegin = Just (LIterTag, r179ObservedProviderCut)),
   (checkedApplyAction (LAdvance 0) r179ObservedProviderCut = Just (LFinishTag, r179ObservedProviderFinished)),
   (registryWellFormed r179ObservedProviderCut = True),
   (registryWellFormed r179ObservedProviderFinished = True))
r179ObservedProviderEdges = (Refl, Refl, Refl, Refl, Refl)
