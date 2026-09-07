module DGamma.R180O19ObservedCompletion

import DGamma.Core
import DGamma.Calculus
import DGamma.CalculusChecks
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.Section3Example
import DGamma.Unified
import DGamma.R179O19ObservedExecution
import Data.Maybe
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Observe the actual normalization VALUE before projecting its binding.
||| This is not a consumer-target claim: the result retains the observed Boolean
||| and neither assumes nor concludes that the service is available.
export
0 r180ProviderResolutionObserved :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (0 tableObserved : (restrictOwnedPreservingOrder @{%search}
    DGamma.Section3Example.toySpecA (ownedValues (ownedA True)) = table)) ->
  (present : Bool) ->
  (0 bindingObserved : (memberKey @{%search} ServiceA (ownedValues table) = present)) ->
  (providerOf {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search} ServiceA
    (registry {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} r179ObservedProviderFinished) =
    (if present then Just 0 else Nothing))
r180ProviderResolutionObserved table tableObserved True bindingObserved =
  rewrite tableObserved in rewrite bindingObserved in Refl
r180ProviderResolutionObserved table tableObserved False bindingObserved =
  rewrite tableObserved in rewrite bindingObserved in Refl

||| Binding truth comes from the checked provider program's actual normalized
||| output table. The observation only names that value; it cannot choose data.
export
0 r180NormalizedServiceMemberObserved :
  (table : CoeffectContext ToyKey ToyValue) ->
  (0 observed : (bindings table = bindings (ownedValues
    (restrictOwnedPreservingOrder @{%search} DGamma.Section3Example.toySpecA
      (ownedValues (ownedA True)))))) ->
  (memberKey @{%search} ServiceA table = True)
r180NormalizedServiceMemberObserved (MkCoeffectContext entries unique) observed =
  cong (\items => isJust (lookupEntries {key = ToyKey} {value = ToyValue}
    @{%search} ServiceA items))
    (trans observed (restrictOwnedPreservingOrderBindings @{%search}
      DGamma.Section3Example.toySpecA (ownedA True)))

||| Close the observation using its producer-owned normalization witness.
||| The state is the ACTUAL output authenticated by r179ObservedProviderEdges.
export
0 r180FinishedProviderResolution :
  (providerOf {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search} ServiceA
    (registry {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} r179ObservedProviderFinished) = Just 0)
r180FinishedProviderResolution =
  r180ProviderResolutionObserved
    (restrictOwnedPreservingOrder @{%search} DGamma.Section3Example.toySpecA
      (ownedValues (ownedA True))) Refl True
    (r180NormalizedServiceMemberObserved
      (ownedValues (restrictOwnedPreservingOrder @{%search}
        DGamma.Section3Example.toySpecA (ownedValues (ownedA True)))) Refl)

||| Explicit consumer Begin output, sharing the ACTUAL provider registry.
||| This definition alone is not a transition or an execution proof.
public export
r180ObservedConsumerBegun : SystemState Nat ToyKey ToyValue ToyRuntime String
r180ObservedConsumerBegun = MkSystemState (worldState r179ObservedProviderFinished)
  (replaceBinding 1
    (MkFiber emptyConsumerComponent Root False emptyOwned
      (Reloading [] id (ProviderView 0 EmptyView)))
    (registry r179ObservedProviderFinished))

||| A6, supervisor-authorized DISTINCT raw-edge prerequisite. This is not the
||| exhausted A5 checked-edge statement: there is no registry-WF guard here.
export
0 r180ConsumerBeginRawObserved :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (0 tableObserved : (restrictOwnedPreservingOrder @{%search}
    DGamma.Section3Example.toySpecA (ownedValues (ownedA True)) = table)) ->
  (binding : Maybe Bool) ->
  (0 bindingObserved : (lookupBinding @{%search} ServiceA (ownedValues table) = binding)) ->
  (0 present : (isJust binding = True)) ->
  (applyAction {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search} (LBegin 1)
    r179ObservedProviderFinished = Just (LBeginTag, r180ObservedConsumerBegun))
r180ConsumerBeginRawObserved table tableObserved Nothing bindingObserved present =
  case present of Refl impossible
r180ConsumerBeginRawObserved table tableObserved (Just service) bindingObserved present =
  rewrite tableObserved in rewrite bindingObserved in Refl

||| Close ALL observations using the actual normalized provider table and the
||| producer-owned A2 binding theorem; no provider-availability premise remains.
export
0 r180ConsumerBeginRaw :
  (applyAction {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search} (LBegin 1)
    r179ObservedProviderFinished = Just (LBeginTag, r180ObservedConsumerBegun))
r180ConsumerBeginRaw = r180ConsumerBeginRawObserved
  (restrictOwnedPreservingOrder @{%search} DGamma.Section3Example.toySpecA
    (ownedValues (ownedA True))) Refl
  (lookupBinding @{%search} ServiceA (ownedValues (restrictOwnedPreservingOrder
    @{%search} DGamma.Section3Example.toySpecA (ownedValues (ownedA True))))) Refl
  (r180NormalizedServiceMemberObserved (ownedValues (restrictOwnedPreservingOrder
    @{%search} DGamma.Section3Example.toySpecA (ownedValues (ownedA True)))) Refl)

||| A8 DISTINCT exact-output WF/domain prerequisite. Raw Theorem59 PRODUCES the
||| output validity from R179's authenticated source WF and A7's raw edge; its
||| committed-view conjunct includes every actual per-view provider/value domain.
||| Neither output WF nor any individual view domain is assumed.
export
0 r180ConsumerBeginOutputDomains :
  (registryWellFormed {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search}
    r180ObservedConsumerBegun = True,
   viewsInvariant {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search}
    (registryFibers {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} (registry r180ObservedConsumerBegun))
    (registry r180ObservedConsumerBegun) = True)
r180ConsumerBeginOutputDomains =
  (preservationTheoremProof {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} %search %search (LBegin 1)
    r179ObservedProviderFinished r180ObservedConsumerBegun LBeginTag
    (snd (snd (snd (snd r179ObservedProviderEdges)))) r180ConsumerBeginRaw,
   wellFormedViewsInvariant {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} %search %search
    (worldState r180ObservedConsumerBegun) (registry r180ObservedConsumerBegun)
    (preservationTheoremProof {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} %search %search (LBegin 1)
      r179ObservedProviderFinished r180ObservedConsumerBegun LBeginTag
      (snd (snd (snd (snd r179ObservedProviderEdges)))) r180ConsumerBeginRaw))

||| Named generic projection of an observed raw edge AND its produced target
||| domains. No particular consumer checked equation is retried here.
export
0 r180CheckedFromPrerequisites :
  (action : Action Nat ToyKey ToyValue ToyRuntime String) ->
  (before, afterState : SystemState Nat ToyKey ToyValue ToyRuntime String) ->
  (tag : RuleTag) ->
  (applyAction @{%search} @{%search} action before = Just (tag, afterState)) ->
  (registryWellFormed @{%search} @{%search} afterState = True) ->
  (checkedApplyAction @{%search} @{%search} action before = Just (tag, afterState))
r180CheckedFromPrerequisites action before afterState tag raw domains =
  rewrite raw in rewrite domains in Refl

||| Constructor projection of the COMMITTED A7 raw equation and A8 exact output
||| domains through A9. This is not a fourth direct A5 checked-edge attempt.
export
0 r180ConsumerBeginFromPrerequisites :
  BeginStep (the (DecEq Nat) %search) (the (DecEq ToyKey) %search) 1
    r179ObservedProviderFinished r180ObservedConsumerBegun
r180ConsumerBeginFromPrerequisites = MkBeginStep
  (r180CheckedFromPrerequisites (LBegin 1) r179ObservedProviderFinished
    r180ObservedConsumerBegun LBeginTag r180ConsumerBeginRaw
    (fst r180ConsumerBeginOutputDomains))

||| Exact intended consumer Finish payload; the next raw observation must
||| authenticate this definition before it may be used as a checked endpoint.
public export
r180ObservedConsumerFinished : SystemState Nat ToyKey ToyValue ToyRuntime String
r180ObservedConsumerFinished = MkSystemState (worldState r180ObservedConsumerBegun)
  (replaceBinding 1
    (MkFiber emptyConsumerComponent Root False emptyOwned
      (Active id (ProviderView 0 EmptyView)))
    (registry r180ObservedConsumerBegun))

||| Observe the same actual normalized provider VALUE inside consumer Finish.
||| This raw result separately authenticates the intended Active payload.
export
0 r180ConsumerFinishRawObserved :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (0 tableObserved : (restrictOwnedPreservingOrder @{%search}
    DGamma.Section3Example.toySpecA (ownedValues (ownedA True)) = table)) ->
  (binding : Maybe Bool) ->
  (0 bindingObserved : (lookupBinding @{%search} ServiceA (ownedValues table) = binding)) ->
  (0 present : (isJust binding = True)) ->
  (applyAction {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} @{%search} @{%search} (LAdvance 1)
    r180ObservedConsumerBegun = Just (LFinishTag, r180ObservedConsumerFinished))
r180ConsumerFinishRawObserved table tableObserved Nothing bindingObserved present =
  case present of Refl impossible
r180ConsumerFinishRawObserved table tableObserved (Just service) bindingObserved present =
  rewrite tableObserved in rewrite bindingObserved in Refl
