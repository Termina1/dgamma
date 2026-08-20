module DGamma.CP4DeletionWithdrawalJoin

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPostCloseFold
import DGamma.CP4DeletionRetirementPersistence
import DGamma.CP4DeletionSelectedEpisodeFold
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionWithdrawalCurrent
import DGamma.CP4DeletionEndpoint
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

public export
record SplitGenerationScan
  (name : Type) (nameEq : DecEq name)
  (startOrdinal : Nat) (startLive : GenerationEnvironment name)
  {first, middle, finalState : SystemState name key value world error}
  (left : Transitions first middle) (right : Transitions middle finalState)
  (finalOrdinal : Nat) (finalLive : GenerationEnvironment name) where
  constructor MkSplitGenerationScan
  splitOrdinal : Nat
  splitLive : GenerationEnvironment name
  0 splitLeftScan : GenerationTraceScan nameEq startOrdinal startLive left
    splitOrdinal splitLive
  0 splitRightScan : GenerationTraceScan nameEq splitOrdinal splitLive right
    finalOrdinal finalLive

0 splitGenerationScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live (appendTransitions left right)
    finalOrdinal finalLive ->
  SplitGenerationScan name nameEq ordinal live left right finalOrdinal finalLive
splitGenerationScan nameEq ordinal live NoTransitions right finalOrdinal finalLive
  scan = MkSplitGenerationScan ordinal live GenerationTraceScanEnd scan
splitGenerationScan nameEq ordinal live
  (MoreTransitions transition rest) right finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan) =
    case splitGenerationScan nameEq (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live)
      rest right finalOrdinal finalLive tailScan of
      MkSplitGenerationScan middleOrdinal middleLive leftScan rightScan =>
        MkSplitGenerationScan middleOrdinal middleLive
          (GenerationTraceScanStep transition rest leftScan) rightScan

0 natLTEReflJoin : (n : Nat) -> LTE n n
natLTEReflJoin Z = LTEZero
natLTEReflJoin (S n) = LTESucc (natLTEReflJoin n)

0 scanOrdinalCount :
  (scan : GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive) ->
  finalOrdinal = ordinal + transitionCount trace
scanOrdinalCount GenerationTraceScanEnd = sym (plusZeroRightNeutral _)
scanOrdinalCount (GenerationTraceScanStep transition rest tail) =
  trans (scanOrdinalCount tail)
    (plusSuccRightSucc _ (transitionCount rest))

0 noRegisteredAppendRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  NoRegisteredEpisode nameEq registered ordinal live
    (appendTransitions left right) ->
  (middleOrdinal : Nat ** (middleLive : GenerationEnvironment name **
    (GenerationTraceScan nameEq ordinal live left middleOrdinal middleLive,
     NoRegisteredEpisode nameEq registered middleOrdinal middleLive right)))
noRegisteredAppendRight nameEq registered ordinal live NoTransitions right
  noRegistered = (ordinal ** (live ** (GenerationTraceScanEnd, noRegistered)))
noRegisteredAppendRight nameEq registered ordinal live
  (MoreTransitions transition rest) right
  (NoRegisteredEpisodeStep _ _ noBegin tail) =
    case noRegisteredAppendRight nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live) rest right tail of
      (middleOrdinal ** (middleLive ** (leftScan, rightNoRegistered))) =>
        (middleOrdinal ** (middleLive **
          (GenerationTraceScanStep transition rest leftScan,
           rightNoRegistered)))

0 restrictNoRegisteredSingleton :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (generation : RegistrationGeneration name) -> Elem generation registered ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  NoRegisteredEpisode nameEq registered ordinal live trace ->
  NoRegisteredEpisode nameEq [generation] ordinal live trace
restrictNoRegisteredSingleton nameEq registered generation member ordinal live
  NoTransitions NoRegisteredEpisodeEnd = NoRegisteredEpisodeEnd
restrictNoRegisteredSingleton nameEq registered generation member ordinal live
  (MoreTransitions transition rest)
  (NoRegisteredEpisodeStep transition rest noBegin tail) =
    let singletonNoBegin : IsBeginAction (transitionAction transition) ->
          GenerationOwnedActor nameEq [generation] ordinal live
            (transitionAction transition) -> Void
        singletonNoBegin begin (_ ** (current, Here)) =
          noBegin begin (generation ** (current, member))
    in NoRegisteredEpisodeStep transition rest singletonNoBegin
      (restrictNoRegisteredSingleton nameEq registered generation member
        (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal
          (transitionAction transition) live) rest tail)

0 currentAtTailStart :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {afterState, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  LT (generationBirthOrdinal generation) ordinal ->
  (action : Action name key value world error) ->
  (rest : Transitions afterState finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) rest
    finalOrdinal finalLive ->
  lookupCurrentGeneration @{nameEq} actor finalLive = Just generation ->
  lookupCurrentGeneration @{nameEq} actor
    (advanceGenerationEnvironment @{nameEq} ordinal action live) =
    Just generation
currentAtTailStart nameEq actor generation ordinal live unique less action rest
  finalOrdinal finalLive scan finalCurrent = currentGenerationAtScanStart nameEq
    actor generation (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action live
      unique) (lteSuccRight less) rest finalOrdinal finalLive scan finalCurrent

||| Locate the promised retirement in the after-birth suffix and persist it to
||| that suffix's endpoint while the exact generation remains current.
0 retirementOccurrencePersists :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  LT (generationBirthOrdinal generation) ordinal ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq [generation] ordinal live trace ->
  lookupCurrentGeneration @{nameEq} actor live = Just generation ->
  lookupCurrentGeneration @{nameEq} actor finalLive = Just generation ->
  InactiveFiberAt name key world error value nameEq actor first ->
  ActionOccurs (ORetire actor) trace ->
  RetiredFiberAt name key world error value nameEq actor finalState
retirementOccurrencePersists nameEq keyEq actor generation ordinal live unique
  stamped less (MoreTransitions
    (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked) rest)
  finalOrdinal finalLive
  (GenerationTraceScanStep _ _ tailScan)
  (AlignedStep action tag checked rest alignedTail)
  (NoRegisteredEpisodeStep _ _ noBegin noRegisteredTail)
  currentStart finalCurrent inactive occurrence =
    let raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        nextCurrent = currentAtTailStart nameEq actor generation ordinal live
          unique less action rest finalOrdinal finalLive tailScan finalCurrent
        nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
        nextStamped = advanceGenerationEnvironmentPreservesStamped nameEq ordinal
          action live stamped
        nextInactiveAll = currentRegisteredInactiveStep nameEq keyEq [generation]
          ordinal live unique action _ _ tag raw noBegin
          (\selected, observed, Here, current =>
            let actorPresent = currentGenerationEntryFromLookup nameEq actor
                  generation live currentStart
                selectedPresent = currentGenerationEntryFromLookup nameEq
                  selected generation live current
                generationActor = stamped actor generation actorPresent
                generationSelected = stamped selected generation selectedPresent
                selectedActor = trans (sym generationSelected) generationActor
            in replace
              {p = \observedActor => InactiveFiberAt name key world error value
                nameEq observedActor first}
              (sym selectedActor) inactive)
        nextInactive = nextInactiveAll actor generation Here nextCurrent
    in case occurrence of
      ActionOccursHere _ _ sameAction => case sameAction of
        Refl =>
          case retireGivesRetiredInactive nameEq keyEq actor _ _ tag raw inactive of
            (retiredAt, inactiveAfter) =>
              retiredInactiveCurrentPersists nameEq keyEq actor generation
                (S ordinal)
                (advanceGenerationEnvironment @{nameEq} ordinal
                  (the (Action name key value world error) (ORetire actor)) live)
                nextUnique (lteSuccRight less) rest finalOrdinal finalLive
                tailScan alignedTail noRegisteredTail nextCurrent finalCurrent
                retiredAt inactiveAfter
      ActionOccursLater _ _ later =>
        retirementOccurrencePersists nameEq keyEq actor generation (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          nextUnique nextStamped (lteSuccRight less) rest finalOrdinal finalLive
          tailScan
          alignedTail noRegisteredTail nextCurrent finalCurrent nextInactive later


0 systemEtaWithdrawalJoin :
  (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
systemEtaWithdrawalJoin (MkSystemState ambient fibers) = Refl

0 alignedHeadRawJoin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (transition : Transition before afterState) ->
  (rest : Transitions afterState finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  applyAction @{nameEq} @{keyEq} (transitionAction transition) before =
    Just (transitionTag transition, afterState)
alignedHeadRawJoin nameEq keyEq
  (Fired nameEq keyEq action tag checked) rest
  (AlignedStep action tag checked rest tail) =
    checkedActionProjects nameEq keyEq action _ _ tag checked

0 currentAfterLocatedInsert :
  (nameEq : DecEq name) -> (child : name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  action = OInsert child parent component ->
  (generation : RegistrationGeneration name) ->
  generation = MkRegistrationGeneration child ordinal ->
  lookupCurrentGeneration @{nameEq} child
    (advanceGenerationEnvironment @{nameEq} ordinal action live) = Just generation
currentAfterLocatedInsert nameEq child ordinal live
  (OInsert child parent component) Refl generation generationInserted =
    replace
      {p = \observed => lookupCurrentGeneration @{nameEq} child
        (putCurrentGeneration @{nameEq} child
          (MkRegistrationGeneration child ordinal) live) = Just observed}
      (sym generationInserted)
      (lookupPutCurrentSelf nameEq child
        (MkRegistrationGeneration child ordinal) live)

0 alignedTailJoin :
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions transition rest) ->
  AlignedTransitions name key world error value nameEq keyEq rest
alignedTailJoin (AlignedStep action tag checked rest tail) = tail

0 noRegisteredAppendRightAtScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {middleOrdinal : Nat} -> {middleLive : GenerationEnvironment name} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (left : Transitions first middle) ->
  (right : Transitions middle finalState) ->
  GenerationTraceScan nameEq ordinal live left middleOrdinal middleLive ->
  NoRegisteredEpisode nameEq registered ordinal live
    (appendTransitions left right) ->
  NoRegisteredEpisode nameEq registered middleOrdinal middleLive right
noRegisteredAppendRightAtScan nameEq registered ordinal live NoTransitions right
  GenerationTraceScanEnd noRegistered = noRegistered
noRegisteredAppendRightAtScan nameEq registered ordinal live
  (MoreTransitions transition rest) right
  (GenerationTraceScanStep _ _ tailScan)
  (NoRegisteredEpisodeStep _ _ noBegin tail) =
    noRegisteredAppendRightAtScan nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction transition) live) rest right tailScan tail


||| Build endpoint retirement for one generated birth by splitting the exact
||| center scanner at that birth and consuming `generatedRetiresLater`.
0 generatedRetiredAtCenterEnd :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (startOrdinal : Nat) ->
  (registered : List (RegistrationGeneration name)) ->
  (generation : RegistrationGeneration name) -> Elem generation registered ->
  (center : Transitions centerFirst centerFinal) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq startOrdinal startLive center finalOrdinal finalLive ->
  GenerationEnvironmentNamesUnique startLive ->
  GenerationEnvironmentStamped startLive ->
  AlignedTransitions name key world error value nameEq keyEq center ->
  NoRegisteredEpisode nameEq registered startOrdinal startLive center ->
  GeneratedDuring name key world error value selected startOrdinal center
    generation ->
  lookupCurrentGeneration @{nameEq} (generationName generation) finalLive =
    Just generation ->
  RetiredFiberAt name key world error value nameEq
    (generationName generation) centerFinal
generatedRetiredAtCenterEnd nameEq keyEq selected startOrdinal registered
  generation member center finalOrdinal finalLive centerScan uniqueStart
  stampedStart aligned noRegistered generated finalCurrent =
    case generated of
      MkGeneratedDuring child component birth stamp retires =>
        let decomposedScan : GenerationTraceScan nameEq startOrdinal startLive
              (appendTransitions (beforeActionOccurrence birth)
                (MoreTransitions (locatedTransition birth)
                  (afterActionOccurrence birth))) finalOrdinal finalLive
            decomposedScan = replace
              {p = \observed => GenerationTraceScan nameEq startOrdinal startLive
                observed finalOrdinal finalLive}
              (sym (actionOccurrenceDecomposition birth)) centerScan
        in case splitGenerationScan nameEq startOrdinal startLive
          (beforeActionOccurrence birth)
          (MoreTransitions (locatedTransition birth)
            (afterActionOccurrence birth)) finalOrdinal finalLive
          decomposedScan of
          MkSplitGenerationScan beforeOrdinal beforeLive beforeScan
            fromBirthScan =>
              case fromBirthScan of
                GenerationTraceScanStep _ _ afterScan =>
                  let beforeCount = scanOrdinalCount beforeScan
                      0 birthOrdinal : (beforeOrdinal =
                        startOrdinal + locatedActionOrdinal birth)
                      birthOrdinal = trans beforeCount
                        (cong (startOrdinal +)
                          (cong transitionCount Refl))
                      birthAction : transitionAction (locatedTransition birth) =
                        OInsert child (ChildOf selected) component
                      birthAction = locatedAction birth
                      0 beforeUnique : GenerationEnvironmentNamesUnique
                        beforeLive
                      beforeUnique = generationTraceScanPreservesUnique nameEq
                        beforeScan uniqueStart
                      0 beforeStamped : GenerationEnvironmentStamped beforeLive
                      beforeStamped = generationTraceScanPreservesStamped nameEq
                        beforeScan stampedStart
                      0 afterUnique : GenerationEnvironmentNamesUnique
                        (advanceGenerationEnvironment @{nameEq} beforeOrdinal
                          (transitionAction (locatedTransition birth)) beforeLive)
                      afterUnique = advanceGenerationEnvironmentPreservesUnique
                        nameEq beforeOrdinal (transitionAction (locatedTransition birth))
                        beforeLive beforeUnique
                      0 afterStamped : GenerationEnvironmentStamped
                        (advanceGenerationEnvironment @{nameEq} beforeOrdinal
                          (transitionAction (locatedTransition birth)) beforeLive)
                      afterStamped = advanceGenerationEnvironmentPreservesStamped
                        nameEq beforeOrdinal (transitionAction (locatedTransition birth))
                        beforeLive beforeStamped
                      0 generationInserted : generation =
                        MkRegistrationGeneration child beforeOrdinal
                      generationInserted = trans stamp
                        (sym (cong (MkRegistrationGeneration child)
                          birthOrdinal))
                      currentInserted : lookupCurrentGeneration @{nameEq} child
                          (advanceGenerationEnvironment @{nameEq} beforeOrdinal
                            (transitionAction (locatedTransition birth)) beforeLive) =
                        Just generation
                      currentInserted = currentAfterLocatedInsert nameEq child
                        beforeOrdinal beforeLive
                        (transitionAction (locatedTransition birth)) birthAction
                        generation generationInserted
                      decomposedAligned = replace
                        {p = \observed => AlignedTransitions name key world error
                          value nameEq keyEq observed}
                        (sym (actionOccurrenceDecomposition birth)) aligned
                      0 alignedParts :
                        (AlignedTransitions name key world error value nameEq
                          keyEq (beforeActionOccurrence birth),
                         AlignedTransitions name key world error value nameEq
                          keyEq (MoreTransitions (locatedTransition birth)
                            (afterActionOccurrence birth)))
                      alignedParts = alignedAppendSplit
                        (beforeActionOccurrence birth)
                        (MoreTransitions (locatedTransition birth) (afterActionOccurrence birth))
                        decomposedAligned
                      0 afterAligned : AlignedTransitions name key world error
                        value nameEq keyEq (afterActionOccurrence birth)
                      afterAligned = alignedTailJoin (snd alignedParts)
                      0 decomposedNoRegistered : NoRegisteredEpisode nameEq
                        registered startOrdinal startLive
                        (appendTransitions (beforeActionOccurrence birth)
                          (MoreTransitions (locatedTransition birth)
                            (afterActionOccurrence birth)))
                      decomposedNoRegistered = replace
                        {p = \observed => NoRegisteredEpisode nameEq registered
                          startOrdinal startLive observed}
                        (sym (actionOccurrenceDecomposition birth)) noRegistered
                      0 fromBirthNoRegistered : NoRegisteredEpisode nameEq
                        registered beforeOrdinal beforeLive
                        (MoreTransitions (locatedTransition birth)
                          (afterActionOccurrence birth))
                      fromBirthNoRegistered = noRegisteredAppendRightAtScan
                        nameEq registered startOrdinal startLive
                        (beforeActionOccurrence birth)
                        (MoreTransitions (locatedTransition birth)
                          (afterActionOccurrence birth)) beforeScan
                        decomposedNoRegistered
                      0 afterNoRegistered : NoRegisteredEpisode nameEq registered
                        (S beforeOrdinal)
                        (advanceGenerationEnvironment @{nameEq} beforeOrdinal
                          (transitionAction (locatedTransition birth)) beforeLive)
                        (afterActionOccurrence birth)
                      afterNoRegistered = case fromBirthNoRegistered of
                        NoRegisteredEpisodeStep _ _ birthNoBegin tail => tail
                  in let 0 raw : (applyAction @{nameEq} @{keyEq}
                            (OInsert child (ChildOf selected) component)
                            (actionBeforeState birth) =
                          Just (transitionTag (locatedTransition birth),
                            actionAfterState birth))
                         raw = replace
                            {p = \observed => applyAction @{nameEq} @{keyEq}
                              observed (actionBeforeState birth) =
                              Just (transitionTag (locatedTransition birth),
                                actionAfterState birth)}
                            birthAction
                            (alignedHeadRawJoin nameEq keyEq
                              (locatedTransition birth)
                              (afterActionOccurrence birth) (snd alignedParts))
                  in let 0 rawEta : (applyAction @{nameEq} @{keyEq}
                            (OInsert child (ChildOf selected) component)
                            (MkSystemState (worldState (actionBeforeState birth))
                              (registry (actionBeforeState birth))) =
                          Just (transitionTag (locatedTransition birth),
                            actionAfterState birth))
                         rawEta = replace
                            {p = \observed => applyAction @{nameEq} @{keyEq}
                              (OInsert child (ChildOf selected) component) observed =
                              Just (transitionTag (locatedTransition birth),
                            actionAfterState birth)}
                            (sym (systemEtaWithdrawalJoin
                              (actionBeforeState birth))) raw
                  in let 0 insertView : ForeignInsertPlanView name key world
                            error value nameEq keyEq child (ChildOf selected)
                            component (worldState (actionBeforeState birth))
                            (registry (actionBeforeState birth))
                            (transitionTag (locatedTransition birth))
                            (actionAfterState birth)
                         insertView = foreignInsertPlanView nameEq keyEq child
                            (ChildOf selected) component
                            (worldState (actionBeforeState birth))
                            (registry (actionBeforeState birth))
                            (transitionTag (locatedTransition birth))
                            (actionAfterState birth) rawEta
                         0 absent : lookupFiber @{nameEq} {name = name}
                           {key = key} {value = value} {world = world}
                           {error = error} child
                            (registry (actionBeforeState birth)) = Nothing
                         absent = foreignInsertViewAbsent insertView
                         0 inactiveAfter : InactiveFiberAt name key world error
                            value nameEq child (actionAfterState birth)
                         inactiveAfter = MkInactiveFiberAt component
                            (ChildOf selected) False emptyOwned Nothing
                            (foreignInsertTargetFound insertView)
                         0 singletonNoRegistered :
                            NoRegisteredEpisode nameEq [generation]
                              (S beforeOrdinal)
                              (advanceGenerationEnvironment @{nameEq}
                                beforeOrdinal
                                (transitionAction (locatedTransition birth)) beforeLive)
                              (afterActionOccurrence birth)
                         singletonNoRegistered =
                            restrictNoRegisteredSingleton nameEq
                              registered generation member
                              (S beforeOrdinal)
                              (advanceGenerationEnvironment @{nameEq}
                                beforeOrdinal
                                (transitionAction (locatedTransition birth)) beforeLive)
                              (afterActionOccurrence birth)
                              afterNoRegistered
                         0 less : LT (generationBirthOrdinal
                            generation) (S beforeOrdinal)
                         less = rewrite stamp in rewrite sym birthOrdinal in
                            LTESucc (natLTEReflJoin beforeOrdinal)
                  in replace
                    {p = \observed => RetiredFiberAt name key
                      world error value nameEq observed centerFinal}
                    (sym (cong generationName stamp))
                    (retirementOccurrencePersists nameEq keyEq
                      child generation (S beforeOrdinal)
                      (advanceGenerationEnvironment @{nameEq}
                        beforeOrdinal
                        (transitionAction (locatedTransition birth)) beforeLive)
                      afterUnique afterStamped less (afterActionOccurrence birth) finalOrdinal
                      finalLive afterScan afterAligned
                      singletonNoRegistered currentInserted
                      (replace
                        {p = \actor =>
                          lookupCurrentGeneration @{nameEq}
                            actor finalLive = Just generation}
                        (cong generationName stamp) finalCurrent)
                      inactiveAfter retires)
  
||| Complete occurrence/scanner join used by CP4DeletionEndpoint.
public export
0 currentRegisteredWithdrawableFromTrace :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment name) ->
  (center : Transitions centerFirst afterClose) ->
  (centerFinalOrdinal : Nat) ->
  (centerFinalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq startOrdinal startLive center centerFinalOrdinal
    centerFinalLive ->
  GenerationEnvironmentNamesUnique startLive ->
  GenerationEnvironmentStamped startLive ->
  AlignedTransitions name key world error value nameEq keyEq center ->
  NoRegisteredEpisode nameEq registered startOrdinal startLive center ->
  RegisteredGenerationsDuring selected startOrdinal registered center ->
  (suffix : Transitions afterClose finalState) ->
  RegisteredGenerationsBornBefore registered centerFinalOrdinal ->
  GenerationEnvironmentNamesUnique centerFinalLive ->
  GenerationTraceScan nameEq centerFinalOrdinal centerFinalLive suffix
    finalOrdinal finalLive ->
  GenerationEnvironmentStamped finalLive ->
  AlignedTransitions name key world error value nameEq keyEq suffix ->
  NoRegisteredEpisode nameEq registered centerFinalOrdinal centerFinalLive
    suffix ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    centerFinalLive afterClose ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered
    centerFinalLive afterClose ->
  CurrentRegisteredWithdrawable name key world error value nameEq registered
    finalLive finalState
currentRegisteredWithdrawableFromTrace nameEq keyEq selected registered
  startOrdinal startLive center centerFinalOrdinal centerFinalLive centerScan
  uniqueStart stampedStart centerAligned centerNoRegistered registeredDuring
  suffix bornBefore
  uniqueCenter suffixScan finalStamped suffixAligned suffixNoRegistered
  sourceInactive sourceEmpty actor generation member finalCurrent =
    let 0 present : Elem (actor, generation) finalLive
        present = currentGenerationEntryFromLookup nameEq actor generation
          finalLive finalCurrent
        0 generationActor : actor = generationName generation
        generationActor = sym (finalStamped actor generation present)
    in case generationActor of
      Refl =>
        let currentCenter = currentGenerationAtScanStart nameEq actor generation
              centerFinalOrdinal centerFinalLive uniqueCenter
              (bornBefore generation member) suffix finalOrdinal finalLive suffixScan
              finalCurrent
            generated = fst registeredDuring generation member
            retiredCenter = generatedRetiredAtCenterEnd nameEq keyEq selected
              startOrdinal registered generation member center centerFinalOrdinal
              centerFinalLive centerScan uniqueStart stampedStart centerAligned
              centerNoRegistered
              generated currentCenter
            singletonSuffixNoRegistered = restrictNoRegisteredSingleton nameEq
              registered generation member centerFinalOrdinal centerFinalLive suffix
              suffixNoRegistered
            inactiveCenter = sourceInactive actor generation member currentCenter
            retiredFinal = retiredInactiveCurrentPersists nameEq keyEq actor generation
              centerFinalOrdinal centerFinalLive uniqueCenter
              (bornBefore generation member) suffix finalOrdinal finalLive suffixScan
              suffixAligned singletonSuffixNoRegistered currentCenter finalCurrent
              retiredCenter inactiveCenter
            finalInactiveAll = currentRegisteredInactiveTrace nameEq keyEq registered
              centerFinalOrdinal centerFinalLive uniqueCenter suffix finalOrdinal
              finalLive suffixScan suffixAligned suffixNoRegistered sourceInactive
            finalEmptyAll = currentRegisteredEmptyTableTrace nameEq keyEq registered
              centerFinalOrdinal centerFinalLive uniqueCenter suffix finalOrdinal
              finalLive suffixScan suffixAligned suffixNoRegistered sourceInactive
              sourceEmpty
            finalInactive = finalInactiveAll actor generation member finalCurrent
        in case retiredFinal of
          MkRetiredFiberAt fiber found retiredTrue =>
            case finalInactive of
              MkInactiveFiberAt component parent retiredFlag table outcome
                inactiveFound =>
                  let sameFiber = justInjective (trans (sym found) inactiveFound)
                  in case sameFiber of
                    Refl => (fiber ** (found, (retiredTrue,
                      (Refl, finalEmptyAll (generationName generation) generation
                        member finalCurrent fiber
                        found))))

||| Every registered birth selected by `RegisteredGenerationsDuring` occurs at a
||| strict scanner position before the center endpoint.
public export
0 registeredBornBeforeCenterEnd :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {startLive : GenerationEnvironment name} ->
  (nameEq : DecEq name) -> (selected : name) -> (startOrdinal : Nat) ->
  (registered : List (RegistrationGeneration name)) ->
  (center : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq startOrdinal startLive center finalOrdinal
    finalLive ->
  RegisteredGenerationsDuring selected startOrdinal registered center ->
  RegisteredGenerationsBornBefore registered finalOrdinal
registeredBornBeforeCenterEnd nameEq selected startOrdinal registered center
  finalOrdinal finalLive scan (generatedAll, complete) generation member =
    case generatedAll generation member of
      MkGeneratedDuring child component birth stamp retires =>
        let decomposed : GenerationTraceScan nameEq startOrdinal startLive
              (appendTransitions (beforeActionOccurrence birth)
                (MoreTransitions (locatedTransition birth)
                  (afterActionOccurrence birth))) finalOrdinal finalLive
            decomposed = replace
              {p = \observed => GenerationTraceScan nameEq startOrdinal startLive
                observed finalOrdinal finalLive}
              (sym (actionOccurrenceDecomposition birth)) scan
        in case splitGenerationScan nameEq startOrdinal startLive
          (beforeActionOccurrence birth)
          (MoreTransitions (locatedTransition birth)
            (afterActionOccurrence birth)) finalOrdinal finalLive decomposed of
          MkSplitGenerationScan beforeOrdinal beforeLive beforeScan fromBirth =>
            case fromBirth of
              GenerationTraceScanStep _ _ afterScan =>
                let beforeCount = scanOrdinalCount beforeScan
                    birthOrdinal : (beforeOrdinal =
                      startOrdinal + locatedActionOrdinal birth)
                    birthOrdinal = trans beforeCount
                      (cong (startOrdinal +) (cong transitionCount Refl))
                    beforeLessFinal : LT beforeOrdinal finalOrdinal
                    beforeLessFinal = generationScanStartLTE afterScan
                in replace
                  {p = \observed => LT (generationBirthOrdinal observed)
                    finalOrdinal}
                  (sym stamp)
                  (replace
                    {p = \observedBirth => LT observedBirth finalOrdinal}
                    birthOrdinal beforeLessFinal)
