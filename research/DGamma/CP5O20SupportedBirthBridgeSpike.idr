module DGamma.CP5O20SupportedBirthBridgeSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5AllSupportedMetadataSpike
import DGamma.CP5AcceptedSupportTruthSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O21EndpointIdentitySpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| An actual canonical child birth has the actual ORIGINAL endpoint metadata.
||| Exact original origin comes from this capital's deletion/sorting producer.
export
0 canonicalGeneratedOriginMetadata :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (selected, parent : name) -> (component : Component key value world error) ->
  LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule capital)) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just observed) ->
  ((ChildOf parent, component) = (fiberParent observed, fiberComponent observed))
canonicalGeneratedOriginMetadata name key world error value nameEq keyEq protocol original capital unique
  selected parent component occurrence observed found =
    uniqueRawBirthMetadata name key world error value nameEq keyEq original unique selected
      (ChildOf parent) (fiberParent observed) component (fiberComponent observed)
      (generatedRegistrationActionOccurrence (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) occurrence))
      (rawMetadataBirthAtPrefix name key world error value nameEq keyEq original original NoTransitions
        (currentBirthTraceAppendEmpty name key world error value original)
        (replayAligned (chainReplayCapital (capitalPremises capital)))
        (replayInitialEmpty (chainReplayCapital (capitalPremises capital))) selected observed found)

||| The actual canonical placement produces the child occurrence; original
||| uniqueness identifies its component, rather than asking for that equality.
export
0 canonicalSupportedChildBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (selected, parent : name) -> (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just observed) ->
  (fiberParent observed = ChildOf parent) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected finalState = True) ->
  LocatedGeneratedRegistration selected parent (fiberComponent observed) (canonicalTrace (canonicalSchedule capital))
canonicalSupportedChildBirth name key world error value nameEq keyEq protocol original capital unique
  selected parent observed found parentExact supported =
    case childGenerationBeforeOwnLifecycle (inputPlacement (canonicalSchedule capital)) selected parent
      (orderComplete (supportLinearization (canonicalSchedule capital)) selected supported) observed found parentExact of
      (component ** occurrence ** _) =>
        replace {p = \program => LocatedGeneratedRegistration selected parent program (canonicalTrace (canonicalSchedule capital))}
          (cong snd (canonicalGeneratedOriginMetadata name key world error value nameEq keyEq protocol original capital unique
            selected parent component occurrence observed found)) occurrence

||| Accepted static metadata PLUS genuine A9 support truth. The opposite fiber,
||| fields and support are produced, not premises of a bridge constructor.
export
0 bridgeSupportedOriginalTarget :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  (selected : name) -> (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected leftFinal = True) ->
  (opposite : Fiber name key value world error **
    ((lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} (renameForward (expectedBridgeBijection sameInputs) selected) (registry rightFinal) = Just opposite),
     (fiberComponent opposite = fiberComponent sourceFiber),
     (fiberParent opposite = supportMapParent name (renameForward (expectedBridgeBijection sameInputs)) (fiberParent sourceFiber)),
     (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
       @{nameEq} @{keyEq} (renameForward (expectedBridgeBijection sameInputs) selected) rightFinal = True)))
bridgeSupportedOriginalTarget name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
  leftUnique rightUnique matched selected sourceFiber sourceFound supported =
    case acceptedAllSupportedMetadataForward name key world error value nameEq keyEq protocol left right sameInputs
      (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
      (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
      (replayDiscipline (chainReplayCapital (capitalPremises leftCapital)))
      (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital))) leftUnique rightUnique
      selected sourceFiber sourceFound supported of
      (opposite ** (found, component, parent)) => (opposite ** (found, component, parent,
        acceptedSupportedTruthForward name key world error value nameEq keyEq protocol left right sameInputs matched
          (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
          (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
          (replayDiscipline (chainReplayCapital (capitalPremises leftCapital)))
          (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital))) leftUnique rightUnique selected supported))

||| The LEFT canonical birth's exact original origin has the accepted CURRENT
||| generation, independent of any prospective operational permutation.
export
0 leftCanonicalOriginCurrentStamp :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (leftFinalGenerations (generatedRegistrationTree sameInputs)) = Just generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just observed) ->
  (birth : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule capital))) ->
  generation = registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) birth)
leftCanonicalOriginCurrentStamp name key world error value nameEq keyEq protocol left right sameInputs capital unique
  selected parent component generation current observed found birth =
    acceptedLeftEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs
      (replayAligned (chainReplayCapital (capitalPremises capital)))
      (replayInitialEmpty (chainReplayCapital (capitalPremises capital))) unique
      selected generation current observed found (ChildOf parent) component
      (generatedRegistrationActionOccurrence (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) birth))

||| The RIGHT canonical birth's exact original origin has the accepted CURRENT
||| generation, independent of any prospective operational permutation.
export
0 rightCanonicalOriginCurrentStamp :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (generation : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (rightFinalGenerations (generatedRegistrationTree sameInputs)) = Just generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry rightFinal) = Just observed) ->
  (birth : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule capital))) ->
  generation = registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) birth)
rightCanonicalOriginCurrentStamp name key world error value nameEq keyEq protocol left right sameInputs capital unique
  selected parent component generation current observed found birth =
    acceptedRightEndpointBirthIdentity name key world error value nameEq keyEq left right sameInputs
      (replayAligned (chainReplayCapital (capitalPremises capital)))
      (replayInitialEmpty (chainReplayCapital (capitalPremises capital))) unique
      selected generation current observed found (ChildOf parent) component
      (generatedRegistrationActionOccurrence (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence capital) birth))

||| Exact accepted-generation triangle for any two actual canonical occurrences
||| at the fixed current names. Opposite occurrence existence is a separate task.
export
0 canonicalSupportedOriginTriangle :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (selected, leftParent, rightParent : name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected leftFinal = True) ->
  (leftBirth : LocatedGeneratedRegistration selected leftParent leftComponent (canonicalTrace (canonicalSchedule leftCapital))) ->
  (rightBirth : LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
    rightParent rightComponent (canonicalTrace (canonicalSchedule rightCapital))) ->
  generationForward (generatedGenerationBijection sameInputs)
    (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence leftCapital) leftBirth)) =
  registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence rightCapital) rightBirth)
canonicalSupportedOriginTriangle name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
  leftUnique rightUnique selected leftParent rightParent leftComponent rightComponent sourceFiber sourceFound supported leftBirth rightBirth =
    case acceptedSupportedForwardDomain name key world error value nameEq keyEq left right sameInputs
      (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
      (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
      (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital))) selected supported of
      (leftGeneration ** rightGeneration ** opposite ** (leftCurrent, rightCurrent, mapped, rightFound)) =>
        trans (cong (generationForward (generatedGenerationBijection sameInputs))
          (sym (leftCanonicalOriginCurrentStamp name key world error value nameEq keyEq protocol left right sameInputs leftCapital leftUnique
            selected leftParent leftComponent leftGeneration leftCurrent sourceFiber sourceFound leftBirth)))
          (trans mapped (rightCanonicalOriginCurrentStamp name key world error value nameEq keyEq protocol left right sameInputs rightCapital rightUnique
            (renameForward (expectedBridgeBijection sameInputs) selected) rightParent rightComponent rightGeneration rightCurrent opposite rightFound rightBirth))

||| PRODUCE the opposite canonical occurrence at the fixed child AND parent,
||| same component. A9 is genuinely used to obtain opposite support.
export
0 mappedSupportedCanonicalBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected leftFinal = True) ->
  (leftBirth : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule leftCapital))) ->
  LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
    (renameForward (expectedBridgeBijection sameInputs) parent) component (canonicalTrace (canonicalSchedule rightCapital))
mappedSupportedCanonicalBirth name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
  leftUnique rightUnique matched selected parent component sourceFiber sourceFound supported leftBirth =
    case bridgeSupportedOriginalTarget name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
      leftUnique rightUnique matched selected sourceFiber sourceFound supported of
      (opposite ** (found, componentExact, parentExact, rightSupported)) =>
        replace {p = \program => LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
          (renameForward (expectedBridgeBijection sameInputs) parent) program (canonicalTrace (canonicalSchedule rightCapital))}
          (trans componentExact (sym (cong snd (canonicalGeneratedOriginMetadata name key world error value nameEq keyEq protocol left leftCapital leftUnique
            selected parent component leftBirth sourceFiber sourceFound))))
          (canonicalSupportedChildBirth name key world error value nameEq keyEq protocol right rightCapital rightUnique
            (renameForward (expectedBridgeBijection sameInputs) selected) (renameForward (expectedBridgeBijection sameInputs) parent) opposite found
            (trans parentExact (cong (supportMapParent name (renameForward (expectedBridgeBijection sameInputs)))
              (sym (cong fst (canonicalGeneratedOriginMetadata name key world error value nameEq keyEq protocol left leftCapital leftUnique
                selected parent component leftBirth sourceFiber sourceFound))))) rightSupported)

||| Fixed-bijection canonical-to-canonical birth clause, on originally supported
||| children. Neither an opposite occurrence nor the triangle is a premise.
export
0 supportedCanonicalBirthBridgeObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (left : Transitions initial leftFinal) -> (right : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq left right) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq left) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq right) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  GeneratedOrchestrationMatched name key world error value nameEq left right (generatedGenerationBijection sameInputs) ->
  (selected, parent : name) -> (component : Component key value world error) ->
  (sourceFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry leftFinal) = Just sourceFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected leftFinal = True) ->
  (leftBirth : LocatedGeneratedRegistration selected parent component (canonicalTrace (canonicalSchedule leftCapital))) ->
  (rightBirth : LocatedGeneratedRegistration (renameForward (expectedBridgeBijection sameInputs) selected)
    (renameForward (expectedBridgeBijection sameInputs) parent) component (canonicalTrace (canonicalSchedule rightCapital)) **
    generationForward (generatedGenerationBijection sameInputs)
      (registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence leftCapital) leftBirth)) =
    registrationGeneration (replayGeneratedRegistrationOrigin (canonicalOccurrenceCorrespondence rightCapital) rightBirth))
supportedCanonicalBirthBridgeObserved name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
  leftUnique rightUnique matched selected parent component sourceFiber sourceFound supported leftBirth =
    (mappedSupportedCanonicalBirth name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
      leftUnique rightUnique matched selected parent component sourceFiber sourceFound supported leftBirth **
     canonicalSupportedOriginTriangle name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital leftUnique rightUnique
      selected parent (renameForward (expectedBridgeBijection sameInputs) parent) component component sourceFiber sourceFound supported leftBirth
      (mappedSupportedCanonicalBirth name key world error value nameEq keyEq protocol left right sameInputs leftCapital rightCapital
        leftUnique rightUnique matched selected parent component sourceFiber sourceFound supported leftBirth))
