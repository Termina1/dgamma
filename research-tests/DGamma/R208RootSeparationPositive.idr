module DGamma.R208RootSeparationPositive

import DGamma.Core
import DGamma.Effects
import DGamma.Unified
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.Section3Example
import DGamma.CP5O19AttachedPairsSpike
import DGamma.CP5O19RootInputSeparationSpike
import DGamma.R206AttachedGrammarPositive
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| All six mixed root products fail to match external heads, even though
||| every action here names the SAME root2. Each input is a native transition.
export
0 r208SixMixedRootProducts :
  (Not (SameExternalOrchestration (the (DecEq Nat) %search)
    (MoreTransitions r206RootInsertEdge NoTransitions) (MoreTransitions r206RootRetireEdge NoTransitions)),
   Not (SameExternalOrchestration (the (DecEq Nat) %search)
    (MoreTransitions r206RootInsertEdge NoTransitions) (MoreTransitions r206RootRemoveEdge NoTransitions)),
   Not (SameExternalOrchestration (the (DecEq Nat) %search)
    (MoreTransitions r206RootRetireEdge NoTransitions) (MoreTransitions r206RootInsertEdge NoTransitions)),
   Not (SameExternalOrchestration (the (DecEq Nat) %search)
    (MoreTransitions r206RootRetireEdge NoTransitions) (MoreTransitions r206RootRemoveEdge NoTransitions)),
   Not (SameExternalOrchestration (the (DecEq Nat) %search)
    (MoreTransitions r206RootRemoveEdge NoTransitions) (MoreTransitions r206RootInsertEdge NoTransitions)),
   Not (SameExternalOrchestration (the (DecEq Nat) %search)
    (MoreTransitions r206RootRemoveEdge NoTransitions) (MoreTransitions r206RootRetireEdge NoTransitions)))
r208SixMixedRootProducts =
  (\same => case o19RootInputProductAgreement r206RootInsertEdge r206RootRetireEdge NoTransitions NoTransitions
    (RootInsertStep Refl) (RootRetireStep (freshFiber DGamma.CalculusChecks.providerComponent Root) Refl Refl Refl) same of
      RootInsertAgreement impossible,
   \same => case o19RootInputProductAgreement r206RootInsertEdge r206RootRemoveEdge NoTransitions NoTransitions
    (RootInsertStep Refl) (RootRemoveStep (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent Root)) Refl Refl Refl) same of
      RootInsertAgreement impossible,
   \same => case o19RootInputProductAgreement r206RootRetireEdge r206RootInsertEdge NoTransitions NoTransitions
    (RootRetireStep (freshFiber DGamma.CalculusChecks.providerComponent Root) Refl Refl Refl) (RootInsertStep Refl) same of
      RootRetireAgreement impossible,
   \same => case o19RootInputProductAgreement r206RootRetireEdge r206RootRemoveEdge NoTransitions NoTransitions
    (RootRetireStep (freshFiber DGamma.CalculusChecks.providerComponent Root) Refl Refl Refl)
    (RootRemoveStep (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent Root)) Refl Refl Refl) same of
      RootRetireAgreement impossible,
   \same => case o19RootInputProductAgreement r206RootRemoveEdge r206RootInsertEdge NoTransitions NoTransitions
    (RootRemoveStep (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent Root)) Refl Refl Refl) (RootInsertStep Refl) same of
      RootRemoveAgreement impossible,
   \same => case o19RootInputProductAgreement r206RootRemoveEdge r206RootRetireEdge NoTransitions NoTransitions
    (RootRemoveStep (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent Root)) Refl Refl Refl)
    (RootRetireStep (freshFiber DGamma.CalculusChecks.providerComponent Root) Refl Refl Refl) same of
      RootRemoveAgreement impossible)

||| The named structural premise admits a genuinely non-legacy child-control
||| core beside a nonempty root Insert/Retire/Remove bundle. Not a claim that
||| these fixture fragments form a complete sanctioned adjacent block pair.
export
0 r208OneExternalBlockWithControls :
  O19AtMostOneExternalBlock (the (DecEq Nat) %search)
    (MoreTransitions r206ReleaseEdge NoTransitions)
    (MoreTransitions r206RootInsertEdge (MoreTransitions r206RootRetireEdge
      (MoreTransitions r206RootRemoveEdge NoTransitions)))
r208OneExternalBlockWithControls = Left (o19ExpandedCoreNoRoot
  (CoreChildRemoveStep r206ReleaseEdge NoTransitions 1
    (retireFiber (freshFiber DGamma.CalculusChecks.providerComponent (ChildOf 0)))
    Refl Refl Refl CoreLifecycleEnd))
