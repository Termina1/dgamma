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
