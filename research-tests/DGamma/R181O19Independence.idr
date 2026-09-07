module DGamma.R181O19Independence

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import DGamma.R179O19ObservedExecution
import DGamma.R180O19ObservedCompletion
import DGamma.R181O19SafetyCompletion
import DGamma.R181O19UniquenessAndBundle
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| G1: the consumer's ACTUAL explicit Begin payload is authenticated through
||| all three checked foreign provider steps and lookupReplacedFiber. No scalar
||| Refl observation of nested provider builders/accumulators is used. The only
||| base observation is the original explicit two-root registry.
public export
0 r181ConsumerLookupAfterBegin :
  lookupFiber @{the (DecEq Nat) %search} 1 (registry r180ObservedConsumerBegun) =
    Just (MkFiber DGamma.CalculusChecks.emptyConsumerComponent Root False emptyOwned
      (Reloading [] id (ProviderView 0 EmptyView)))
r181ConsumerLookupAfterBegin = lookupReplacedFiber @{the (DecEq Nat) %search} 1
  (freshFiber DGamma.CalculusChecks.emptyConsumerComponent Root)
  (MkFiber DGamma.CalculusChecks.emptyConsumerComponent Root False emptyOwned
    (Reloading [] id (ProviderView 0 EmptyView)))
  (registry r179ObservedProviderFinished)
  (trans (systemLocalUpdateForeign (the (DecEq Nat) %search) 1 0
    (\same => case same of Refl impossible) r179ObservedProviderCut r179ObservedProviderFinished
    (applyActionLocalUpdate (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
      (LAdvance 0) r179ObservedProviderCut r179ObservedProviderFinished LFinishTag
      (checkedActionProjects (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
        (LAdvance 0) r179ObservedProviderCut r179ObservedProviderFinished LFinishTag
        (Builtin.fst (Builtin.snd (Builtin.snd r179ObservedProviderEdges))))))
    (trans (systemLocalUpdateForeign (the (DecEq Nat) %search) 1 0
      (\same => case same of Refl impossible) r179ObservedProviderBegin r179ObservedProviderCut
      (applyActionLocalUpdate (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
        (LAdvance 0) r179ObservedProviderBegin r179ObservedProviderCut LIterTag
        (checkedActionProjects (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
          (LAdvance 0) r179ObservedProviderBegin r179ObservedProviderCut LIterTag
          (Builtin.fst (Builtin.snd r179ObservedProviderEdges)))))
      (trans (systemLocalUpdateForeign (the (DecEq Nat) %search) 1 0
        (\same => case same of Refl impossible) r179ObservedRootSource r179ObservedProviderBegin
        (applyActionLocalUpdate (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
          (LBegin 0) r179ObservedRootSource r179ObservedProviderBegin LBeginTag
          (checkedActionProjects (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
            (LBegin 0) r179ObservedRootSource r179ObservedProviderBegin LBeginTag
            (Builtin.fst r179ObservedProviderEdges)))) Refl)))
