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

||| Producer-owned closure: quiet, failure-free and BOTH Active endpoint facts
||| now hold without a premise. The actual whole trace, not a Maybe fallback,
||| already authenticates this named final state.
export
0 r181EndpointReady :
  ((quiet {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime}
      {error = String} @{%search} @{%search} r180ObservedConsumerFinished = True),
   (noFailedFibers r180ObservedConsumerFinished = True),
   (supportedActiveAt {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} @{%search} 0 r180ObservedConsumerFinished = True),
   (supportedActiveAt {name = Nat} {key = ToyKey} {value = ToyValue}
      {world = ToyRuntime} {error = String} @{%search} 1 r180ObservedConsumerFinished = True))
r181EndpointReady = r181EndpointObserved
  (restrictOwnedPreservingOrder @{%search} DGamma.Section3Example.toySpecA
    (ownedValues (ownedA True))) Refl
  (lookupBinding @{%search} ServiceA (ownedValues (restrictOwnedPreservingOrder
    @{%search} DGamma.Section3Example.toySpecA (ownedValues (ownedA True))))) Refl
  (r180NormalizedServiceMemberObserved (ownedValues (restrictOwnedPreservingOrder
    @{%search} DGamma.Section3Example.toySpecA (ownedValues (ownedA True)))) Refl)

||| Admit dependency-free providers at rank0, and genuine consumers ONLY if
||| they declare no provisions, at rank1. No function equality is inspected.
public export
r181ProtocolRank : Component ToyKey ToyValue ToyRuntime String -> Maybe Nat
r181ProtocolRank (MkComponent (MkCoeffectSpec [] unique) provision program) = Just 0
r181ProtocolRank (MkComponent (MkCoeffectSpec (wanted :: rest) unique)
  (MkCoeffectSpec [] provisionUnique) program) = Just 1
r181ProtocolRank (MkComponent (MkCoeffectSpec (wanted :: rest) unique)
  (MkCoeffectSpec (provided :: more) provisionUnique) program) = Nothing

||| Genuine provision/dependency edges increase rank. A rank1 component cannot
||| itself be a provider: its provision list is empty by construction.
export
0 r181PrecedenceRanks :
  (provider, consumer : Component ToyKey ToyValue ToyRuntime String) ->
  (providerRank, consumerRank : Nat) ->
  (r181ProtocolRank provider = Just providerRank) ->
  (r181ProtocolRank consumer = Just consumerRank) ->
  (wanted : ToyKey) ->
  Elem wanted (dependencies (componentProvisions provider)) ->
  Elem wanted (dependencies (componentDependencies consumer)) ->
  LT providerRank consumerRank
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec [] sourceUnique) sourceProvision sourceProgram)
  (MkComponent (MkCoeffectSpec [] targetUnique) targetProvision targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case depends of Here impossible; There later impossible
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec [] sourceUnique) sourceProvision sourceProgram)
  (MkComponent (MkCoeffectSpec (targetHead :: targetRest) targetUnique) (MkCoeffectSpec [] targetProvisionUnique) targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    rewrite sym (justInjective providerRanked) in
      rewrite sym (justInjective consumerRanked) in LTESucc LTEZero
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec [] sourceUnique) sourceProvision sourceProgram)
  (MkComponent (MkCoeffectSpec (targetHead :: targetRest) targetUnique) (MkCoeffectSpec (targetProvided :: targetMore) targetProvisionUnique) targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case consumerRanked of Refl impossible
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec (sourceHead :: sourceRest) sourceUnique) (MkCoeffectSpec [] sourceProvisionUnique) sourceProgram)
  (MkComponent (MkCoeffectSpec [] targetUnique) targetProvision targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case depends of Here impossible; There later impossible
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec (sourceHead :: sourceRest) sourceUnique) (MkCoeffectSpec [] sourceProvisionUnique) sourceProgram)
  (MkComponent (MkCoeffectSpec (targetHead :: targetRest) targetUnique) (MkCoeffectSpec [] targetProvisionUnique) targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case provides of Here impossible; There later impossible
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec (sourceHead :: sourceRest) sourceUnique) (MkCoeffectSpec [] sourceProvisionUnique) sourceProgram)
  (MkComponent (MkCoeffectSpec (targetHead :: targetRest) targetUnique) (MkCoeffectSpec (targetProvided :: targetMore) targetProvisionUnique) targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case provides of Here impossible; There later impossible
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec (sourceHead :: sourceRest) sourceUnique) (MkCoeffectSpec (sourceProvided :: sourceMore) sourceProvisionUnique) sourceProgram)
  (MkComponent (MkCoeffectSpec [] targetUnique) targetProvision targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case depends of Here impossible; There later impossible
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec (sourceHead :: sourceRest) sourceUnique) (MkCoeffectSpec (sourceProvided :: sourceMore) sourceProvisionUnique) sourceProgram)
  (MkComponent (MkCoeffectSpec (targetHead :: targetRest) targetUnique) (MkCoeffectSpec [] targetProvisionUnique) targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case providerRanked of Refl impossible
r181PrecedenceRanks
  (MkComponent (MkCoeffectSpec (sourceHead :: sourceRest) sourceUnique) (MkCoeffectSpec (sourceProvided :: sourceMore) sourceProvisionUnique) sourceProgram)
  (MkComponent (MkCoeffectSpec (targetHead :: targetRest) targetUnique) (MkCoeffectSpec (targetProvided :: targetMore) targetProvisionUnique) targetProgram)
  providerRank consumerRank providerRanked consumerRanked wanted provides depends =
    case providerRanked of Refl impossible

||| Empty generated catalog, but NOT an empty component universe: both actual
||| provider and dependency-bearing consumer are admitted and rank-coherent.
public export
r181Protocol : RegistrationProtocol ToyKey ToyValue ToyRuntime String
r181Protocol = MkRegistrationProtocol (\tag => Nothing) r181ProtocolRank
  (\parent, child, step, tag, parentRank, childRank, occurs, parentRanked,
    childRanked, tagged, cataloged => case cataloged of Refl impossible)
  r181PrecedenceRanks

||| Authenticate protocol discipline and exact count7 of the SAME whole trace;
||| the consumer is unavailable at its prospective swapped block source.
||| This is NOT yet a full AdjacentActorSwapSafety counterexample.
export
0 r181TraceStructure :
  (RegistrationDiscipline r181Protocol (the (DecEq Nat) %search) r181WholeTrace,
   (transitionCount r181WholeTrace = 7),
   (applyAction {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime}
      {error = String} @{%search} @{%search} (LBegin 1) r179ObservedRootSource = Nothing))
r181TraceStructure =
  (RegistrationDisciplineStep _ _ (0 ** Refl)
    (RegistrationDisciplineStep _ _ (1 ** Refl)
      (RegistrationDisciplineStep _ _ ()
        (RegistrationDisciplineStep _ _ ()
          (RegistrationDisciplineStep _ _ ()
            (RegistrationDisciplineStep _ _ ()
              (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd)))))),
   Refl, Refl)

||| Observe the real normalized provider table before the totality validator.
||| The validator checks EVERY actual actor boundary, not just the endpoint.
export
0 r181TotalityObserved :
  (table : OwnedTable ToyKey ToyValue DGamma.Section3Example.toySpecA) ->
  (0 tableObserved : (restrictOwnedPreservingOrder @{%search}
    DGamma.Section3Example.toySpecA (ownedValues (ownedA True)) = table)) ->
  (binding : Maybe Bool) ->
  (0 bindingObserved : (lookupBinding @{%search} ServiceA (ownedValues table) = binding)) ->
  (0 present : (isJust binding = True)) ->
  (isJust (checkTraceComponentsTotal (the (DecEq Nat) %search)
    (the (DecEq ToyKey) %search) r181WholeTrace) = True)
r181TotalityObserved table tableObserved Nothing bindingObserved present =
  case present of Refl impossible
r181TotalityObserved table tableObserved (Just service) bindingObserved present =
  rewrite tableObserved in rewrite bindingObserved in Refl
