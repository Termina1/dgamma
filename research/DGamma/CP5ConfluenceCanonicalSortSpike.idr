module DGamma.CP5ConfluenceCanonicalSortSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4TerminalRecovery
import DGamma.CP4RecoveryModelTrace
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4Support
import DGamma.CP4SupportQuiescence
import DGamma.CP4SupportSolution
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5UniqueRawNameOrdinalCapital
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| An open episode before sorting: its installed interval may contain arbitrary
||| foreign interleavings all the way to the final Active endpoint.
public export
record LocatedInterleavedOpenEpisode
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedInterleavedOpenEpisode
  openPreStart : SystemState name key value world error
  openStart : SystemState name key value world error
  openPrefix : Transitions initial openPreStart
  openBegin : BeginStep nameEq keyEq selected openPreStart openStart
  openInside : Transitions openStart finalState
  openInstalled : InstalledTrace name key world error value nameEq keyEq selected
    openInside
  openNoEarlierLifecycle : NoLifecycleBy selected openPrefix
  0 openActiveAtFinal : supportedActiveAt @{nameEq} selected finalState = True
  0 openDecomposition : appendTransitions openPrefix
    (MoreTransitions (beginTransition openBegin) openInside) = global

||| Structural consequence after every closing episode is deleted.  Uniqueness
||| is occurrence-indexed by the begin ordinal (`transitionCount openPrefix`),
||| avoiding the old prose-only claim of “exactly one”.
public export
record ClosingFreeTraceShape
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkClosingFreeTraceShape
  supportedOpenEpisode : (selected : name) ->
    isSupported @{nameEq} @{keyEq} selected finalState = True ->
    LocatedInterleavedOpenEpisode name key world error value nameEq keyEq
      selected trace
  0 supportedOpenEpisodeUnique : (selected : name) ->
    (supported : isSupported @{nameEq} @{keyEq} selected finalState = True) ->
    (other : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq
      selected trace) ->
    transitionCount (openPrefix (supportedOpenEpisode selected supported)) =
      transitionCount (openPrefix other)
  unsupportedTakesNoLifecycle : (selected : name) ->
    isSupported @{nameEq} @{keyEq} selected finalState = False ->
    NoLifecycleBy selected trace

||| Finite topological capital for the exact Equation-62 support relation.
public export
record SupportOrderingCapital
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error) where
  constructor MkSupportOrderingCapital
  orderedSupportNames : List name
  orderedSupportLinearization : LinearizesSupport name key world error value
    nameEq keyEq state orderedSupportNames

||| Original-endpoint/reduced-endpoint bridge specialized to the one support
||| order chosen by canonicalization.  Endpoint withdrawal can erase a path
||| through an unsupported intermediate, so a reduced linearization does not in
||| general linearize the original endpoint.  The corrected bridge therefore
||| requires and retains the original-order witness instead of claiming a
||| universal transfer theorem.
public export
record CanonicalSupportTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (originalFinal, reducedFinal : SystemState name key value world error)
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal)
  (order : List name) where
  constructor MkCanonicalSupportTransport
  0 supportTruthPreserved : (n : name) ->
    isSupported @{nameEq} @{keyEq} n originalFinal =
      isSupported @{nameEq} @{keyEq} n reducedFinal
  originalSupportLinearization :
    LinearizesSupport name key world error value nameEq keyEq originalFinal order
  inputPlacementToOriginal :
    {initial, canonicalFinal : SystemState name key value world error} ->
    (canonical : Transitions initial canonicalFinal) ->
    CanonicalInputPlacement name key world error value nameEq keyEq reducedFinal
      order canonical ->
    CanonicalInputPlacement name key world error value nameEq keyEq originalFinal
      order canonical

||| Sorting result with every recursive invariant, replay generator/stage
||| correspondence, external-input witness, and registration-accounting field
||| required by one-trace schedule assembly.
public export
record SortedClosingFreeTrace
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    originalFinal) where
  constructor MkSortedClosingFreeTrace
  sortedFinal : SystemState name key value world error
  sortedTrace : Transitions initial sortedFinal
  sortingReplayCorrespondence : RelationalReplayCorrespondence name key world
    error value original sortedTrace
  sortingAdjacentDerivation : FiniteAdjacentSwapDerivation name key world error
    value protocol nameEq keyEq original sortedTrace
  sortedPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sortedTrace
  sortedSameInputs : SameExternalOrchestration nameEq original sortedTrace
  sortedBlock : (n : name) -> Elem n (orderedSupportNames ordering) ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n sortedTrace
  sortedBlocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier (orderedSupportNames ordering)) ->
    (laterIn : Elem later (orderedSupportNames ordering)) ->
    BeforeIn earlier later (orderedSupportNames ordering) ->
    BlockBefore name key world error value nameEq keyEq sortedTrace earlier later
      (sortedBlock earlier earlierIn) (sortedBlock later laterIn)
  0 sortedBlockRangesDisjoint : (earlier, later : name) ->
    (earlierIn : Elem earlier (orderedSupportNames ordering)) ->
    (laterIn : Elem later (orderedSupportNames ordering)) ->
    BeforeIn earlier later (orderedSupportNames ordering) ->
    (earlierPosition, laterPosition : Nat) ->
    LTE (S earlierPosition)
      (S (transitionCount (blockBody (sortedBlock earlier earlierIn)))) ->
    LTE (S laterPosition)
      (S (transitionCount (blockBody (sortedBlock later laterIn)))) ->
    Not (transitionCount (traceBeforeBlock (sortedBlock earlier earlierIn)) +
      earlierPosition =
      transitionCount (traceBeforeBlock (sortedBlock later laterIn)) +
      laterPosition)
  sortedLifecycleCoverage : LifecycleActorsCovered
    (orderedSupportNames ordering) sortedTrace
  sortedInputPlacement : CanonicalInputPlacement name key world error value
    nameEq keyEq originalFinal (orderedSupportNames ordering) sortedTrace
  sortedEndpoint : CanonicalEndpointRelation name key world error value nameEq
    keyEq originalFinal sortedFinal
  0 sortedWithdrawsNoNames : endpointWithdrawnNames sortedEndpoint = []
  0 sortedWithdrawsNoGenerations :
    endpointWithdrawnGenerations sortedEndpoint = []
  sortedRegistrationTree : CanonicalRegistrationCorrespondence original
    sortedTrace (endpointWithdrawnGenerations sortedEndpoint)

||| Sorting occurrence provenance is computed from the explicit finite sequence
||| of O6-sealed adjacent-swap results.  There is no occurrence-map constructor
||| argument to clone independently of those operational nodes.
public export
0 sortingOccurrenceCorrespondence :
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq keyEq
    original ordering) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (sortedTrace sorted)
sortingOccurrenceCorrespondence sorted =
  finiteDerivationOccurrenceCorrespondence (sortingAdjacentDerivation sorted)

||| Research-side bridge from a fired transition to its action owner.  The
||| production analogue is private to CP3, so CanonicalSort owns the exact
||| projection it needs without widening the frozen production surface.
0 canonicalTransitionActorActionOwner :
  (transition : Transition before afterState) ->
  transitionActor transition = actionOwner (transitionAction transition)
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (OInsert actor parent component) tag checked) = Refl
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (ORetire actor) tag checked) = Refl
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (ORemove actor) tag checked) = Refl
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (LBegin actor) tag checked) = Refl
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (LAdvance actor) tag checked) = Refl
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (LDivert actor) tag checked) = Refl
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (LLeave actor) tag checked) = Refl
canonicalTransitionActorActionOwner
  (Fired nameEq keyEq (LUnload actor) tag checked) = Refl

||| CanonicalSort-local active-to-installed bridge.  CP3 proves the same fact
||| privately; repeating the total observation here avoids depending on that
||| private implementation or changing the frozen production API.
0 canonicalActiveImpliesInstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
0 canonicalSupportedActiveImpliesInstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  supportedActiveAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
canonicalSupportedActiveImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  canonicalSupportedActiveImpliesInstalled nameEq selected state evidence |
    Nothing = absurd evidence
  canonicalSupportedActiveImpliesInstalled nameEq selected state evidence |
    Just (MkFiber component parent retired table (Inactive outcome)) =
      absurd evidence
  canonicalSupportedActiveImpliesInstalled nameEq selected state evidence |
    Just (MkFiber component parent retired table
      (Reloading remaining accumulator view)) = absurd evidence
  canonicalSupportedActiveImpliesInstalled nameEq selected state evidence |
    Just (MkFiber component parent retired table (Active accumulator view)) = Refl
  canonicalSupportedActiveImpliesInstalled nameEq selected state evidence |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) = absurd evidence

canonicalActiveImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  canonicalActiveImpliesInstalled nameEq selected state evidence | Nothing =
    absurd evidence
  canonicalActiveImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber) proof lifecycle
    canonicalActiveImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    canonicalActiveImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    canonicalActiveImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = Refl
    canonicalActiveImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

||| The endpoint of an installed trace remains installed.  This local fold is
||| kept alongside the CanonicalSort consumers because the equivalent anchor
||| classifier helper is private to its production module.
0 canonicalInstalledTraceEnd :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected trace ->
  installedAt @{nameEq} selected finalState = True
canonicalInstalledTraceEnd NoTransitions (InstalledEnd installed) = installed
canonicalInstalledTraceEnd
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (InstalledStep action tag checked rest sourceInstalled tailInstalled) =
    canonicalInstalledTraceEnd rest tailInstalled

||| At a quiet endpoint, an installed fiber can only be Active.  The lookup and
||| lifecycle are eliminated once, at the observation that owns both facts.
0 canonicalQuietInstalledActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  quiet @{nameEq} @{keyEq} state = True ->
  (selected : name) -> installedAt @{nameEq} selected state = True ->
  supportedActiveAt @{nameEq} selected state = True
canonicalQuietInstalledActive nameEq keyEq state quietState selected installed
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  canonicalQuietInstalledActive nameEq keyEq state quietState selected installed |
    Nothing = absurd installed
  canonicalQuietInstalledActive nameEq keyEq state quietState selected installed |
    Just (MkFiber component parent retired table (Inactive outcome)) =
      absurd installed
  canonicalQuietInstalledActive nameEq keyEq state quietState selected installed |
    Just (MkFiber component parent retired table
      (Reloading remaining accumulator view)) =
        absurd (quietFiberFromState nameEq keyEq state quietState selected
          (MkFiber component parent retired table
            (Reloading remaining accumulator view)) found)
  canonicalQuietInstalledActive nameEq keyEq state quietState selected installed |
    Just (MkFiber component parent retired table (Active accumulator view)) = Refl
  canonicalQuietInstalledActive nameEq keyEq state quietState selected installed |
    Just (MkFiber component parent retired table
      (Unloading accumulator view outcome)) =
        absurd (quietFiberFromState nameEq keyEq state quietState selected
          (MkFiber component parent retired table
            (Unloading accumulator view outcome)) found)

||| Extend an exact located closing episode when its containing trace is given a
||| checked right suffix.  The episode data are unchanged; only the trailing
||| decomposition is reassociated.
0 canonicalExtendLocatedClosingRight :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (left : Transitions initial middle) ->
  (right : Transitions middle finalState) ->
  (global : Transitions initial finalState) ->
  appendTransitions left right = global ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected left ->
  LocatedClosedEpisode name key world error value nameEq keyEq selected global
canonicalExtendLocatedClosingRight left right global decomposition
  (MkLocatedClosedEpisode preStart afterState beforeOpening episode afterClosing
    located) =
      MkLocatedClosedEpisode preStart afterState beforeOpening episode
        (appendTransitions afterClosing right)
        (rewrite sym (appendTransitionsAssociative
          (closedTransitions episode) afterClosing right) in
         rewrite sym (appendTransitionsAssociative beforeOpening
          (MoreTransitions (beginTransition (closedOpening episode))
            (appendTransitions (closedTransitions episode) afterClosing)) right) in
         rewrite located in decomposition)

0 canonicalFalseNotTrue : False = True -> Void
canonicalFalseNotTrue Refl impossible

||| A selected lifecycle occurrence in an initially empty segment whose endpoint
||| is uninstalled must close inside that segment.  The closing-free global
||| suffix extension then eliminates it.
0 canonicalLifecycleAbsentBeforeUninstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, middle, finalState, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (left : Transitions initial middle) ->
  (right : Transitions middle finalState) ->
  (global : Transitions initial finalState) ->
  appendTransitions left right = global ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  bindings (registry initial) = [] ->
  installedAt @{nameEq} selected middle = False ->
  NoClosingEpisodes name key world error value nameEq keyEq global ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action stepBefore =
    Just (tag, stepAfter)) ->
  actionOwner action = selected ->
  isLifecycleAction action = True ->
  OccursIn (Fired {before = stepBefore} {afterState = stepAfter}
    nameEq keyEq action tag checked) left ->
  Void
canonicalLifecycleAbsentBeforeUninstalled nameEq keyEq selected left right global
  decomposition aligned initialEmpty endpointUninstalled noClosing action tag
  checked owner lifecycle occurs =
    case classifyForeignLifecycleOccurrence nameEq keyEq selected action owner
      lifecycle tag checked left aligned occurs of
      (anchor ** ContinuationCloses closing) =>
        noClosing selected (canonicalExtendLocatedClosingRight left right global
          decomposition (closingOccurrenceGivesLocatedEpisode nameEq keyEq
            selected (Fired nameEq keyEq action tag checked) left aligned
            initialEmpty anchor closing))
      (anchor ** ContinuationStaysInstalled installed) =>
        canonicalFalseNotTrue (trans (sym endpointUninstalled)
          (canonicalInstalledTraceEnd (lifecycleAfterInstalled anchor) installed))

||| Fold an occurrence-level exclusion into the structural `NoLifecycleBy`
||| witness required by the closing-free shape.
0 canonicalNoLifecycleFromAbsence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (({stepBefore, stepAfter : SystemState name key value world error} ->
    (transition : Transition stepBefore stepAfter) ->
    OccursIn transition trace ->
    isLifecycleAction (transitionAction transition) = True ->
    transitionActor transition = selected -> Void)) ->
  NoLifecycleBy selected trace
canonicalNoLifecycleFromAbsence selected NoTransitions absent =
  NoLifecycleByEnd
canonicalNoLifecycleFromAbsence selected
  (MoreTransitions transition rest) absent =
    NoLifecycleByStep transition rest
      (\lifecycle, same => absent transition OccursHere lifecycle same)
      (canonicalNoLifecycleFromAbsence selected rest
        (\laterTransition, occurs, lifecycle, same =>
          absent laterTransition (OccursLater occurs) lifecycle same))

||| Any lifecycle occurrence of an endpoint-unsupported actor either supplies a
||| forbidden closed episode or survives installed to the quiet endpoint, where
||| support/active agreement contradicts endpoint unsupportedness.
0 canonicalUnsupportedLifecycleAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState, stepBefore, stepAfter :
    SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  bindings (registry initial) = [] ->
  NoClosingEpisodes name key world error value nameEq keyEq trace ->
  quiet @{nameEq} @{keyEq} finalState = True ->
  SupportMatchesActive nameEq keyEq finalState ->
  isSupported @{nameEq} @{keyEq} selected finalState = False ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action stepBefore =
    Just (tag, stepAfter)) ->
  OccursIn (Fired {before = stepBefore} {afterState = stepAfter}
    nameEq keyEq action tag checked) trace ->
  isLifecycleAction action = True ->
  transitionActor (Fired {before = stepBefore} {afterState = stepAfter}
    nameEq keyEq action tag checked) = selected ->
  Void
canonicalUnsupportedLifecycleAbsent nameEq keyEq selected trace aligned
  initialEmpty noClosing quietState supportMatches unsupported action tag checked
  occurs lifecycle actorSame =
    case classifyForeignLifecycleOccurrence nameEq keyEq selected action
      (trans (sym (canonicalTransitionActorActionOwner
        (Fired nameEq keyEq action tag checked))) actorSame)
      lifecycle tag checked trace aligned occurs of
      (anchor ** ContinuationCloses closing) =>
        noClosing selected (closingOccurrenceGivesLocatedEpisode nameEq keyEq
          selected (Fired nameEq keyEq action tag checked) trace aligned
          initialEmpty anchor closing)
      (anchor ** ContinuationStaysInstalled installed) =>
        canonicalFalseNotTrue (trans (sym unsupported)
          (trans (supportMatches selected)
            (canonicalQuietInstalledActive nameEq keyEq finalState quietState
              selected (canonicalInstalledTraceEnd
                (lifecycleAfterInstalled anchor) installed))))

||| Aligned traces expose the exact proof dictionaries needed by the lifecycle
||| classifiers while folding occurrence-level exclusion into `NoLifecycleBy`.
0 canonicalAlignedNoLifecycleFromAbsence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (({stepBefore, stepAfter : SystemState name key value world error} ->
    (action : Action name key value world error) ->
    (tag : RuleTag) ->
    (checked : checkedApplyAction @{nameEq} @{keyEq} action stepBefore =
      Just (tag, stepAfter)) ->
    OccursIn (Fired {before = stepBefore} {afterState = stepAfter}
      nameEq keyEq action tag checked) trace ->
    isLifecycleAction action = True ->
    transitionActor (Fired {before = stepBefore} {afterState = stepAfter}
      nameEq keyEq action tag checked) = selected -> Void)) ->
  NoLifecycleBy selected trace
canonicalAlignedNoLifecycleFromAbsence nameEq keyEq selected NoTransitions
  AlignedEnd absent = NoLifecycleByEnd
canonicalAlignedNoLifecycleFromAbsence nameEq keyEq selected
  (MoreTransitions _ _) (AlignedStep action tag checked rest alignedRest) absent =
    NoLifecycleByStep (Fired nameEq keyEq action tag checked) rest
      (\lifecycle, same => absent action tag checked OccursHere lifecycle same)
      (canonicalAlignedNoLifecycleFromAbsence nameEq keyEq selected rest
        alignedRest
        (\laterAction, laterTag, laterChecked, occurs, lifecycle, same =>
          absent laterAction laterTag laterChecked (OccursLater occurs) lifecycle
            same))

||| Fully erased first-lifecycle view.  Every constructor binds the transition's
||| erased middle state and stored dictionaries through its exact indexed head;
||| no scan output is runtime-relevant.
public export
data ErasedFirstLifecycleView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  Transitions initial finalState -> Type where
  ErasedLifecycleEnd :
    ErasedFirstLifecycleView name key world error value nameEq selected
      NoTransitions
  ErasedLifecycleHere :
    {first, middle, finalState : SystemState name key value world error} ->
    (0 transition : Transition first middle) ->
    (0 rest : Transitions middle finalState) ->
    (0 sameActor : transitionActor transition = selected) ->
    (0 lifecycle : isLifecycleAction (transitionAction transition) = True) ->
    ErasedFirstLifecycleView name key world error value nameEq selected
      (MoreTransitions transition rest)
  ErasedLifecycleSkipActor :
    {first, middle, finalState : SystemState name key value world error} ->
    (0 transition : Transition first middle) ->
    (0 rest : Transitions middle finalState) ->
    (0 distinctActor : Not (transitionActor transition = selected)) ->
    (0 later : ErasedFirstLifecycleView name key world error value nameEq selected
      rest) ->
    ErasedFirstLifecycleView name key world error value nameEq selected
      (MoreTransitions transition rest)
  ErasedLifecycleSkipAction :
    {first, middle, finalState : SystemState name key value world error} ->
    (0 transition : Transition first middle) ->
    (0 rest : Transitions middle finalState) ->
    (0 notLifecycle : isLifecycleAction (transitionAction transition) = False) ->
    (0 later : ErasedFirstLifecycleView name key world error value nameEq selected
      rest) ->
    ErasedFirstLifecycleView name key world error value nameEq selected
      (MoreTransitions transition rest)

0 erasedLifecycleViewOrdinal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  ErasedFirstLifecycleView name key world error value nameEq selected trace ->
  Maybe Nat
erasedLifecycleViewOrdinal ErasedLifecycleEnd = Nothing
erasedLifecycleViewOrdinal
  (ErasedLifecycleHere transition rest sameActor lifecycle) = Just Z
erasedLifecycleViewOrdinal
  (ErasedLifecycleSkipActor transition rest distinctActor later) =
    map S (erasedLifecycleViewOrdinal later)
erasedLifecycleViewOrdinal
  (ErasedLifecycleSkipAction transition rest notLifecycle later) =
    map S (erasedLifecycleViewOrdinal later)

mutual
  0 erasedLifecycleActionDecision :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (selected : name) ->
    {first, middle, finalState : SystemState name key value world error} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionActor transition = selected ->
    (observed : Bool) ->
    isLifecycleAction (transitionAction transition) = observed ->
    ErasedFirstLifecycleView name key world error value nameEq selected
      (MoreTransitions transition rest)
  erasedLifecycleActionDecision nameEq selected transition rest sameActor True
    lifecycle = ErasedLifecycleHere transition rest sameActor lifecycle
  erasedLifecycleActionDecision nameEq selected transition rest sameActor False
    notLifecycle = ErasedLifecycleSkipAction transition rest notLifecycle
      (erasedFirstLifecycleView nameEq selected rest)

  0 erasedLifecycleActorDecision :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (selected : name) ->
    {first, middle, finalState : SystemState name key value world error} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    Dec (transitionActor transition = selected) ->
    ErasedFirstLifecycleView name key world error value nameEq selected
      (MoreTransitions transition rest)
  erasedLifecycleActorDecision nameEq selected transition rest (Yes sameActor) =
    erasedLifecycleActionDecision nameEq selected transition rest sameActor
      (isLifecycleAction (transitionAction transition)) Refl
  erasedLifecycleActorDecision nameEq selected transition rest (No distinctActor) =
    ErasedLifecycleSkipActor transition rest distinctActor
      (erasedFirstLifecycleView nameEq selected rest)

  ||| Covering proof-level scan.  Quantity 0 is essential: the existential middle
  ||| of `MoreTransitions` is unavailable to runtime-relevant code.
  0 erasedFirstLifecycleView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (nameEq : DecEq name) -> (selected : name) ->
    {initial, finalState : SystemState name key value world error} ->
    (trace : Transitions initial finalState) ->
    ErasedFirstLifecycleView name key world error value nameEq selected trace
  erasedFirstLifecycleView nameEq selected NoTransitions = ErasedLifecycleEnd
  erasedFirstLifecycleView nameEq selected
    (MoreTransitions transition rest) =
      erasedLifecycleActorDecision nameEq selected transition rest
        (decEq @{nameEq} (transitionActor transition) selected)

0 erasedLifecycleOrdinalAtHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  transitionActor transition = selected ->
  isLifecycleAction (transitionAction transition) = True ->
  (view : ErasedFirstLifecycleView name key world error value nameEq selected
    (MoreTransitions transition rest)) ->
  erasedLifecycleViewOrdinal view = Just Z
erasedLifecycleOrdinalAtHead nameEq selected transition rest sameActor lifecycle
  (ErasedLifecycleHere transition rest foundActor foundLifecycle) = Refl
erasedLifecycleOrdinalAtHead nameEq selected transition rest sameActor lifecycle
  (ErasedLifecycleSkipActor transition rest distinctActor later) =
    void (distinctActor sameActor)
erasedLifecycleOrdinalAtHead nameEq selected transition rest sameActor lifecycle
  (ErasedLifecycleSkipAction transition rest notLifecycle later) =
    void (canonicalFalseNotTrue (trans (sym notLifecycle) lifecycle))

0 erasedLifecycleOrdinalThroughExcludedHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, middle, before, afterState, finalState :
    SystemState name key value world error} ->
  (transition : Transition first middle) ->
  (earlierRest : Transitions middle before) ->
  (opening : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (isLifecycleAction (transitionAction transition) = True ->
    Not (transitionActor transition = selected)) ->
  ((tailView : ErasedFirstLifecycleView name key world error value nameEq selected
      (appendTransitions earlierRest (MoreTransitions opening later))) ->
    erasedLifecycleViewOrdinal tailView =
      Just (transitionCount earlierRest)) ->
  (view : ErasedFirstLifecycleView name key world error value nameEq selected
    (MoreTransitions transition
      (appendTransitions earlierRest (MoreTransitions opening later)))) ->
  erasedLifecycleViewOrdinal view = Just (S (transitionCount earlierRest))
erasedLifecycleOrdinalThroughExcludedHead nameEq selected transition earlierRest
  opening later excluded induction
  (ErasedLifecycleHere _ _ sameActor lifecycle) =
    void (excluded lifecycle sameActor)
erasedLifecycleOrdinalThroughExcludedHead nameEq selected transition earlierRest
  opening later excluded induction
  (ErasedLifecycleSkipActor _ _ distinctActor tailView) =
    cong (map S) (induction tailView)
erasedLifecycleOrdinalThroughExcludedHead nameEq selected transition earlierRest
  opening later excluded induction
  (ErasedLifecycleSkipAction _ _ notLifecycle tailView) =
    cong (map S) (induction tailView)

0 erasedLifecycleOrdinalAtOpening :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {initial, before, afterState, finalState :
    SystemState name key value world error} ->
  {earlier : Transitions initial before} ->
  (noEarlier : NoLifecycleBy selected earlier) ->
  (opening : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  transitionActor opening = selected ->
  isLifecycleAction (transitionAction opening) = True ->
  (view : ErasedFirstLifecycleView name key world error value nameEq selected
    (appendTransitions earlier (MoreTransitions opening later))) ->
  erasedLifecycleViewOrdinal view = Just (transitionCount earlier)
erasedLifecycleOrdinalAtOpening nameEq selected NoLifecycleByEnd opening later
  sameActor lifecycle view =
    erasedLifecycleOrdinalAtHead nameEq selected opening later sameActor lifecycle
      view
erasedLifecycleOrdinalAtOpening nameEq selected
  (NoLifecycleByStep transition earlierRest excluded noEarlier) opening later
  sameActor lifecycle view =
    erasedLifecycleOrdinalThroughExcludedHead nameEq selected transition earlierRest
      opening later excluded
      (\tailView => erasedLifecycleOrdinalAtOpening nameEq selected noEarlier
        opening later sameActor lifecycle tailView)
      view

0 erasedLifecycleOrdinalAtDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {initial, before, afterState, finalState :
    SystemState name key value world error} ->
  (earlier : Transitions initial before) ->
  (opening : Transition before afterState) ->
  (later : Transitions afterState finalState) ->
  (global : Transitions initial finalState) ->
  appendTransitions earlier (MoreTransitions opening later) = global ->
  NoLifecycleBy selected earlier ->
  transitionActor opening = selected ->
  isLifecycleAction (transitionAction opening) = True ->
  (view : ErasedFirstLifecycleView name key world error value nameEq selected
    global) ->
  erasedLifecycleViewOrdinal view = Just (transitionCount earlier)
erasedLifecycleOrdinalAtDecomposition nameEq selected earlier opening later
  (appendTransitions earlier (MoreTransitions opening later)) Refl noEarlier
  sameActor lifecycle view =
    erasedLifecycleOrdinalAtOpening nameEq selected noEarlier opening later
      sameActor lifecycle view

||| Every located open episode pins the erased scan to its opening ordinal.
0 erasedLifecycleOrdinalAtOpenEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (episode : LocatedInterleavedOpenEpisode name key world error value nameEq
    keyEq selected global) ->
  erasedLifecycleViewOrdinal (erasedFirstLifecycleView nameEq selected global) =
    Just (transitionCount (openPrefix episode))
erasedLifecycleOrdinalAtOpenEpisode nameEq keyEq selected global
  (MkLocatedInterleavedOpenEpisode before afterState earlier opening later
    installed noEarlier active decomposition) =
      erasedLifecycleOrdinalAtDecomposition nameEq selected earlier
        (beginTransition opening) later global decomposition noEarlier Refl Refl
        (erasedFirstLifecycleView nameEq selected global)

||| A supported quiet endpoint has a last opening; closing-freedom makes it the
||| first selected lifecycle occurrence as well.
0 canonicalSupportedOpenEpisode :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  NoClosingEpisodes name key world error value nameEq keyEq trace ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq trace) ->
  (selected : name) ->
  isSupported @{nameEq} @{keyEq} selected finalState = True ->
  LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected
    trace
canonicalSupportedOpenEpisode nameEq keyEq protocol trace noClosing premises
  selected supported =
    let activeFinal = trans
          (sym (replaySupportMatchesActive premises selected)) supported
        installedFinal = canonicalSupportedActiveImpliesInstalled nameEq selected
          _ activeFinal
        initialUninstalled = emptyRegistryUninstalled nameEq selected _
          (replayInitialEmpty premises)
    in case extractLastOpening nameEq keyEq selected trace
      (replayAligned premises) initialUninstalled installedFinal of
      MkLastOpeningResult before afterState earlier opening later decomposition
        installed =>
          let openingSourceUninstalled = fst (snd
                (lBeginBoundary nameEq keyEq selected before afterState LBeginTag
                  (beginEquation opening)))
              decomposedAligned = replace
                {p = \candidate => AlignedTransitions name key world error value
                  nameEq keyEq candidate}
                (sym decomposition) (replayAligned premises)
              earlierAligned = fst (alignedAppendSplit earlier
                (MoreTransitions (beginTransition opening) later)
                decomposedAligned)
              noEarlier = canonicalAlignedNoLifecycleFromAbsence nameEq keyEq
                selected earlier earlierAligned
                (\action, tag, checked, occurs, lifecycle, actorSame =>
                  canonicalLifecycleAbsentBeforeUninstalled nameEq keyEq selected
                    earlier (MoreTransitions (beginTransition opening) later)
                    trace decomposition earlierAligned
                    (replayInitialEmpty premises) openingSourceUninstalled
                    noClosing action tag checked
                    (trans (sym (canonicalTransitionActorActionOwner
                      (Fired nameEq keyEq action tag checked))) actorSame)
                    lifecycle occurs)
          in MkLocatedInterleavedOpenEpisode before afterState earlier opening
            later installed noEarlier activeFinal decomposition

||| Two open episodes for one actor share the proof-level first-lifecycle
||| ordinal, hence have equal occurrence ordinals.
0 canonicalOpenEpisodeOrdinalUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (left, right : LocatedInterleavedOpenEpisode name key world error value
    nameEq keyEq selected global) ->
  transitionCount (openPrefix left) = transitionCount (openPrefix right)
canonicalOpenEpisodeOrdinalUnique nameEq keyEq selected global left right =
  justInjective (trans
    (sym (erasedLifecycleOrdinalAtOpenEpisode nameEq keyEq selected global left))
    (erasedLifecycleOrdinalAtOpenEpisode nameEq keyEq selected global right))

||| Derive the unique closing-free shape from the exact recursive bundle.
public export
0 closingFreeTraceShapeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  NoClosingEpisodes name key world error value nameEq keyEq trace ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace
closingFreeTraceShapeSpike nameEq keyEq protocol trace noClosing premises =
  MkClosingFreeTraceShape
    (\selected, supported => canonicalSupportedOpenEpisode nameEq keyEq protocol
      trace noClosing premises selected supported)
    (\selected, supported, other => canonicalOpenEpisodeOrdinalUnique nameEq
      keyEq selected trace
      (canonicalSupportedOpenEpisode nameEq keyEq protocol trace noClosing
        premises selected supported)
      other)
    (\selected, unsupported => canonicalAlignedNoLifecycleFromAbsence nameEq
      keyEq selected trace (replayAligned premises)
      (\action, tag, checked, occurs, lifecycle, actorSame =>
        canonicalUnsupportedLifecycleAbsent nameEq keyEq selected trace
          (replayAligned premises) (replayInitialEmpty premises) noClosing
          (replayQuiet premises) (replaySupportMatchesActive premises)
          unsupported action tag checked occurs lifecycle actorSame))

||| Transitivity for the non-strict protocol-rank order used by the stable-sort
||| invariant.  It is kept explicit so insertion preservation never depends on
||| an inferred `Transitive` implementation.
0 canonicalRankLTETransitive :
  {left, middle, right : Nat} ->
  LTE left middle ->
  LTE middle right ->
  LTE left right
canonicalRankLTETransitive LTEZero later = LTEZero
canonicalRankLTETransitive (LTESucc earlier) (LTESucc later) =
  LTESucc (canonicalRankLTETransitive earlier later)

||| The actual active lookup equation, without a separately mirrored evaluator.
0 canonicalSupportedActiveAtFound :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (state : SystemState name key value world error) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry state) = Just fiber) ->
  (supportedActiveAt {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected state = isActive (fiberLifecycle fiber))
canonicalSupportedActiveAtFound name key world error value nameEq state selected fiber found =
  activePredicateAtFoundQ {name = name} {key = key} {value = value} {world = world} {error = error}
    nameEq state selected fiber found

||| Exact fiber, active observation and protocol rank owned by one erased lookup.
record CanonicalActiveRank
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error) (nameEq : DecEq name)
  (state : SystemState name key value world error) (selected : name) where
  constructor MkCanonicalActiveRank
  0 activeRankFiber : Fiber name key value world error
  0 activeRankFound : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} selected (registry state) = Just activeRankFiber)
  0 activeRankActive : (isActive (fiberLifecycle activeRankFiber) = True)
  activeProtocolRank : Nat
  0 activeProtocolRankExact : (registrationRank protocol (fiberComponent activeRankFiber) = Just activeProtocolRank)

||| Missing lookup is observed at the actual exported predicate.
0 canonicalSupportedActiveAtMissing :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (state : SystemState name key value world error) -> (selected : name) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry state) = Nothing) ->
  (supportedActiveAt {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected state = False)
canonicalSupportedActiveAtMissing name key world error value nameEq state selected found =
  rewrite found in Refl

||| Rank extraction eliminates only the producer's returned rank witness.
0 canonicalActiveRankAtFound :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  (state : SystemState name key value world error) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry state) = Just fiber) ->
  (isActive (fiberLifecycle fiber) = True) ->
  RegistryProtocolRanked protocol nameEq state ->
  CanonicalActiveRank name key world error value protocol nameEq state selected
canonicalActiveRankAtFound name key world error value protocol nameEq state selected fiber found active ranked =
  case ranked selected fiber found of
    (rank ** hasRank) => MkCanonicalActiveRank fiber found active rank hasRank

||| One exact lookup split owns both absence exclusion and the rank payload.
0 canonicalSupportedRankObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (selected : name) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry state) = observed) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected state = True) ->
  SupportMatchesActive nameEq keyEq state -> RegistryProtocolRanked protocol nameEq state ->
  CanonicalActiveRank name key world error value protocol nameEq state selected
canonicalSupportedRankObserved name key world error value protocol nameEq keyEq state selected Nothing found supported matches ranked =
  absurd (trans (sym (canonicalSupportedActiveAtMissing name key world error value nameEq state selected found))
    (trans (sym (matches selected)) supported))
canonicalSupportedRankObserved name key world error value protocol nameEq keyEq state selected (Just fiber) found supported matches ranked =
  canonicalActiveRankAtFound name key world error value protocol nameEq state selected fiber found
    (trans (sym (canonicalSupportedActiveAtFound name key world error value nameEq state selected fiber found))
      (trans (sym (matches selected)) supported)) ranked

||| The caller supplies support, never a chosen fiber or a chosen protocol rank.
0 canonicalSupportedRank :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) -> (selected : name) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected state = True) ->
  SupportMatchesActive nameEq keyEq state -> RegistryProtocolRanked protocol nameEq state ->
  CanonicalActiveRank name key world error value protocol nameEq state selected
canonicalSupportedRank name key world error value protocol nameEq keyEq state selected supported matches ranked =
  canonicalSupportedRankObserved name key world error value protocol nameEq keyEq state selected
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry state)) Refl supported matches ranked

||| Executable total rank observation; absent/unranked names use zero only off the certified domain.
canonicalProtocolRank :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  (state : SystemState name key value world error) -> name -> Nat
canonicalProtocolRank name key world error value protocol nameEq state selected =
  maybe 0 (\fiber => maybe 0 id (registrationRank protocol (fiberComponent fiber)))
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry state))

||| The defaulted executable observation agrees with each exact path rank witness.
0 canonicalProtocolRankExact :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  (state : SystemState name key value world error) -> (selected : name) -> (rank : Nat) ->
  NameProtocolRank protocol nameEq state selected rank ->
  (canonicalProtocolRank name key world error value protocol nameEq state selected = rank)
canonicalProtocolRankExact name key world error value protocol nameEq state selected rank
  (MkNameProtocolRank fiber found ranked) = rewrite found in rewrite ranked in Refl

0 canonicalRankedSupportPathStrict :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) ->
  (state : SystemState name key value world error) -> (lower, upper : name) ->
  RankedSupportPath protocol nameEq state lower upper ->
  LT (canonicalProtocolRank name key world error value protocol nameEq state lower)
    (canonicalProtocolRank name key world error value protocol nameEq state upper)
canonicalRankedSupportPathStrict name key world error value protocol nameEq state lower upper
  (MkRankedSupportPath lowerRank upperRank lowerWitness upperWitness increases) =
    rewrite canonicalProtocolRankExact name key world error value protocol nameEq state lower lowerRank lowerWitness in
    rewrite canonicalProtocolRankExact name key world error value protocol nameEq state upper upperRank upperWitness in increases

||| Every head is bounded by every following rank, with all order evidence erased.
data CanonicalRanksOrdered : (item : Type) -> (rank : item -> Nat) -> List item -> Type where
  CanonicalRanksNil : {item : Type} -> {rank : item -> Nat} -> CanonicalRanksOrdered item rank []
  CanonicalRanksCons : {item : Type} -> {rank : item -> Nat} ->
    (head : item) -> (rest : List item) ->
    (0 headBelow : (later : item) -> Elem later rest -> LTE (rank head) (rank later)) ->
    (0 tailOrdered : CanonicalRanksOrdered item rank rest) ->
    CanonicalRanksOrdered item rank (head :: rest)

||| Output and its full invariant are constructed together, never independently sorted.
record CanonicalRankSortResult (item : Type) (rank : item -> Nat) (source : List item) where
  constructor MkCanonicalRankSortResult
  rankSortedItems : List item
  0 rankSortedOrdered : CanonicalRanksOrdered item rank rankSortedItems
  0 rankSortedUnique : UniqueKeys rankSortedItems
  0 rankSortedForward : (selected : item) -> Elem selected source -> Elem selected rankSortedItems
  0 rankSortedBackward : (selected : item) -> Elem selected rankSortedItems -> Elem selected source

0 canonicalRanksTail : (item : Type) -> (rank : item -> Nat) ->
  (head : item) -> (rest : List item) ->
  CanonicalRanksOrdered item rank (head :: rest) -> CanonicalRanksOrdered item rank rest
canonicalRanksTail item rank head rest (CanonicalRanksCons head rest below ordered) = ordered

0 canonicalRanksHeadBelow : (item : Type) -> (rank : item -> Nat) ->
  (head : item) -> (rest : List item) -> CanonicalRanksOrdered item rank (head :: rest) ->
  (selected : item) -> Elem selected rest -> LTE (rank head) (rank selected)
canonicalRanksHeadBelow item rank head rest (CanonicalRanksCons head rest below ordered) = below

0 canonicalUniqueTail : (item : Type) -> (head : item) -> (rest : List item) ->
  UniqueKeys (head :: rest) -> UniqueKeys rest
canonicalUniqueTail item head rest (UniqueCons fresh unique) = unique

0 canonicalUniqueHeadAbsent : (item : Type) -> (head : item) -> (rest : List item) ->
  UniqueKeys (head :: rest) -> Not (Elem head rest)
canonicalUniqueHeadAbsent item head rest (UniqueCons fresh unique) = fresh

0 canonicalRanksLowerThroughHead : (item : Type) -> (rank : item -> Nat) ->
  (inserted, head : item) -> (rest : List item) -> LTE (rank inserted) (rank head) ->
  CanonicalRanksOrdered item rank (head :: rest) ->
  (selected : item) -> Elem selected (head :: rest) -> LTE (rank inserted) (rank selected)
canonicalRanksLowerThroughHead item rank inserted head rest before ordered selected present =
  case present of
    Here => before
    There later => canonicalRankLTETransitive before
      (canonicalRanksHeadBelow item rank head rest ordered selected later)

0 canonicalRankExistingForward : (item : Type) -> (inserted : item) -> (rest : List item) ->
  Elem inserted rest -> (selected : item) -> Elem selected (inserted :: rest) -> Elem selected rest
canonicalRankExistingForward item inserted rest existing selected present =
  case present of
    Here => existing
    There later => later

0 canonicalRankPushOldTail : (item : Type) -> (inserted, head : item) -> (rest : List item) ->
  (selected : item) -> Elem selected (head :: rest) -> Elem selected (head :: inserted :: rest)
canonicalRankPushOldTail item inserted head rest selected present =
  case present of
    Here => Here
    There later => There (There later)

0 canonicalRankSwapFront : (item : Type) -> (inserted, head : item) -> (rest : List item) ->
  (selected : item) -> Elem selected (inserted :: head :: rest) -> Elem selected (head :: inserted :: rest)
canonicalRankSwapFront item inserted head rest selected present =
  case present of
    Here => There Here
    There later => canonicalRankPushOldTail item inserted head rest selected later

0 canonicalRankConsMembership : (item : Type) -> (head : item) -> (left, right : List item) ->
  ((selected : item) -> Elem selected left -> Elem selected right) ->
  (selected : item) -> Elem selected (head :: left) -> Elem selected (head :: right)
canonicalRankConsMembership item head left right maps selected present =
  case present of
    Here => Here
    There later => There (maps selected later)

0 canonicalRankInsertedHeadAbsent : (item : Type) -> (inserted, head : item) -> (rest : List item) ->
  Not (Elem head rest) -> Not (Elem inserted (head :: rest)) -> Not (Elem head (inserted :: rest))
canonicalRankInsertedHeadAbsent item inserted head rest headFresh insertedFresh present =
  case present of
    Here => insertedFresh Here
    There later => headFresh later

0 canonicalRankHeadBelowInserted : (item : Type) -> (rank : item -> Nat) ->
  (inserted, head : item) -> (rest : List item) -> LTE (rank head) (rank inserted) ->
  ((selected : item) -> Elem selected rest -> LTE (rank head) (rank selected)) ->
  (selected : item) -> Elem selected (inserted :: rest) -> LTE (rank head) (rank selected)
canonicalRankHeadBelowInserted item rank inserted head rest before below selected present =
  case present of
    Here => before
    There later => below selected later

||| The comparison chooses a constructor that already owns the exact inserted list.
canonicalFreshRankInsertAt : (item : Type) -> (rank : item -> Nat) ->
  (inserted, head : item) -> (rest : List item) ->
  (0 ordered : CanonicalRanksOrdered item rank (head :: rest)) ->
  (0 unique : UniqueKeys (head :: rest)) ->
  (0 fresh : Not (Elem inserted (head :: rest))) ->
  Dec (LTE (rank inserted) (rank head)) -> CanonicalRankSortResult item rank (inserted :: rest) ->
  CanonicalRankSortResult item rank (inserted :: head :: rest)
canonicalFreshRankInsertAt item rank inserted head rest ordered unique fresh (Yes before) tailResult =
  MkCanonicalRankSortResult (inserted :: head :: rest)
    (CanonicalRanksCons inserted (head :: rest)
      (canonicalRanksLowerThroughHead item rank inserted head rest before ordered) ordered)
    (UniqueCons fresh unique) (\selected, present => present) (\selected, present => present)
canonicalFreshRankInsertAt item rank inserted head rest ordered unique fresh (No notBefore) tailResult =
  MkCanonicalRankSortResult (head :: rankSortedItems tailResult)
    (CanonicalRanksCons head (rankSortedItems tailResult)
      (\selected, present => canonicalRankHeadBelowInserted item rank inserted head rest
        (lteSuccLeft (notLTEImpliesGT notBefore))
        (canonicalRanksHeadBelow item rank head rest ordered) selected
        (rankSortedBackward tailResult selected present)) (rankSortedOrdered tailResult))
    (UniqueCons
      (\present => canonicalRankInsertedHeadAbsent item inserted head rest
        (canonicalUniqueHeadAbsent item head rest unique) fresh
        (rankSortedBackward tailResult head present)) (rankSortedUnique tailResult))
    (\selected, present => canonicalRankConsMembership item head (inserted :: rest)
      (rankSortedItems tailResult) (rankSortedForward tailResult) selected
      (canonicalRankSwapFront item inserted head rest selected present))
    (\selected, present => canonicalRankSwapFront item head inserted rest selected
      (canonicalRankConsMembership item head (rankSortedItems tailResult) (inserted :: rest)
        (rankSortedBackward tailResult) selected present))

||| Structural fresh insertion constructs membership, uniqueness and order in the same recursion.
canonicalFreshRankInsert : (item : Type) -> (rank : item -> Nat) ->
  (inserted : item) -> (rest : List item) ->
  (0 ordered : CanonicalRanksOrdered item rank rest) -> (0 unique : UniqueKeys rest) ->
  (0 fresh : Not (Elem inserted rest)) -> CanonicalRankSortResult item rank (inserted :: rest)
canonicalFreshRankInsert item rank inserted [] ordered unique fresh =
  MkCanonicalRankSortResult [inserted]
    (CanonicalRanksCons inserted [] (\selected, present => absurd present) CanonicalRanksNil)
    (UniqueCons fresh UniqueNil) (\selected, present => present) (\selected, present => present)
canonicalFreshRankInsert item rank inserted (head :: rest) ordered unique fresh =
  canonicalFreshRankInsertAt item rank inserted head rest ordered unique fresh
    (isLTE (rank inserted) (rank head))
    (canonicalFreshRankInsert item rank inserted rest
      (canonicalRanksTail item rank head rest ordered) (canonicalUniqueTail item head rest unique)
      (\present => fresh (There present)))

||| Duplicate elimination is part of the same package, not a later uniqueness claim.
canonicalRankInsertSeen : (item : Type) -> (rank : item -> Nat) ->
  (inserted : item) -> (rest : List item) ->
  (0 ordered : CanonicalRanksOrdered item rank rest) -> (0 unique : UniqueKeys rest) ->
  Dec (Elem inserted rest) -> CanonicalRankSortResult item rank (inserted :: rest)
canonicalRankInsertSeen item rank inserted rest ordered unique (Yes existing) =
  MkCanonicalRankSortResult rest ordered unique
    (canonicalRankExistingForward item inserted rest existing) (\selected, present => There present)
canonicalRankInsertSeen item rank inserted rest ordered unique (No fresh) =
  canonicalFreshRankInsert item rank inserted rest ordered unique fresh

canonicalRankInsert : (item : Type) -> (itemEq : DecEq item) -> (rank : item -> Nat) ->
  (inserted : item) -> (rest : List item) ->
  (0 ordered : CanonicalRanksOrdered item rank rest) -> (0 unique : UniqueKeys rest) ->
  CanonicalRankSortResult item rank (inserted :: rest)
canonicalRankInsert item itemEq rank inserted rest ordered unique =
  canonicalRankInsertSeen item rank inserted rest ordered unique (isElem @{itemEq} inserted rest)

||| Relate the newly inserted output to the original unsorted source, at construction.
canonicalRankSortCompose : (item : Type) -> (rank : item -> Nat) ->
  (head : item) -> (rest : List item) -> (tailResult : CanonicalRankSortResult item rank rest) ->
  CanonicalRankSortResult item rank (head :: rankSortedItems tailResult) ->
  CanonicalRankSortResult item rank (head :: rest)
canonicalRankSortCompose item rank head rest tailResult inserted =
  MkCanonicalRankSortResult (rankSortedItems inserted) (rankSortedOrdered inserted) (rankSortedUnique inserted)
    (\selected, present => rankSortedForward inserted selected
      (canonicalRankConsMembership item head rest (rankSortedItems tailResult)
        (rankSortedForward tailResult) selected present))
    (\selected, present => canonicalRankConsMembership item head (rankSortedItems tailResult) rest
      (rankSortedBackward tailResult) selected (rankSortedBackward inserted selected present))

canonicalRankSortStep : (item : Type) -> (itemEq : DecEq item) -> (rank : item -> Nat) ->
  (head : item) -> (rest : List item) -> CanonicalRankSortResult item rank rest ->
  CanonicalRankSortResult item rank (head :: rest)
canonicalRankSortStep item itemEq rank head rest tailResult =
  canonicalRankSortCompose item rank head rest tailResult
    (canonicalRankInsert item itemEq rank head (rankSortedItems tailResult)
      (rankSortedOrdered tailResult) (rankSortedUnique tailResult))

||| Total stable-rank insertion sort with simultaneous deduplication and full invariant.
||| Equal-ranked distinct names are inserted before the suffix; there is no compute-then-prove pass.
canonicalStableRankSort : (item : Type) -> (itemEq : DecEq item) -> (rank : item -> Nat) ->
  (source : List item) -> CanonicalRankSortResult item rank source
canonicalStableRankSort item itemEq rank [] =
  MkCanonicalRankSortResult [] CanonicalRanksNil UniqueNil
    (\selected, present => absurd present) (\selected, present => absurd present)
canonicalStableRankSort item itemEq rank (head :: rest) =
  canonicalRankSortStep item itemEq rank head rest (canonicalStableRankSort item itemEq rank rest)

0 canonicalRankBeforeFromHead : (item : Type) -> (rank : item -> Nat) ->
  (head : item) -> (rest : List item) -> (upper : item) ->
  LT (rank head) (rank upper) -> Elem upper (head :: rest) -> BeforeIn head upper (head :: rest)
canonicalRankBeforeFromHead item rank head rest upper strict upperIn =
  case upperIn of
    Here => void (succNotLTEpred strict)
    There later => BeforeHere later

0 canonicalRankBeforeUpperSplit : (item : Type) -> (rank : item -> Nat) ->
  (head : item) -> (rest : List item) -> (lower, upper : item) ->
  CanonicalRanksOrdered item rank (head :: rest) -> Elem lower rest ->
  LT (rank lower) (rank upper) ->
  (Elem upper rest -> BeforeIn lower upper rest) ->
  Elem upper (head :: rest) -> BeforeIn lower upper (head :: rest)
canonicalRankBeforeUpperSplit item rank head rest lower upper ordered lowerIn strict tailBefore upperIn =
  case upperIn of
    Here => void (LTImpliesNotGTE strict (canonicalRanksHeadBelow item rank head rest ordered lower lowerIn))
    There later => BeforeThere (tailBefore later)

0 canonicalRankBeforeLowerSplit : (item : Type) -> (rank : item -> Nat) ->
  (head : item) -> (rest : List item) -> (lower, upper : item) ->
  CanonicalRanksOrdered item rank (head :: rest) -> LT (rank lower) (rank upper) ->
  Elem upper (head :: rest) ->
  (Elem lower rest -> Elem upper rest -> BeforeIn lower upper rest) ->
  Elem lower (head :: rest) -> BeforeIn lower upper (head :: rest)
canonicalRankBeforeLowerSplit item rank head rest lower upper ordered strict upperIn tailBefore lowerIn =
  case lowerIn of
    Here => canonicalRankBeforeFromHead item rank head rest upper strict upperIn
    There later => canonicalRankBeforeUpperSplit item rank head rest lower upper ordered later strict
      (tailBefore later) upperIn

||| A strict protocol path rank becomes actual occurrence order in the sorted list.
0 canonicalRankOrderBefore : (item : Type) -> (rank : item -> Nat) -> (order : List item) ->
  CanonicalRanksOrdered item rank order -> (lower, upper : item) ->
  LT (rank lower) (rank upper) -> Elem lower order -> Elem upper order -> BeforeIn lower upper order
canonicalRankOrderBefore item rank [] ordered lower upper strict lowerIn upperIn = absurd lowerIn
canonicalRankOrderBefore item rank (head :: rest) ordered lower upper strict lowerIn upperIn =
  canonicalRankBeforeLowerSplit item rank head rest lower upper ordered strict upperIn
    (\lowerTail, upperTail => canonicalRankOrderBefore item rank rest
      (canonicalRanksTail item rank head rest ordered) lower upper strict lowerTail upperTail) lowerIn

0 canonicalListMemberKnownYes : (item : Type) -> (itemEq : DecEq item) ->
  (selected, head : item) -> (rest : List item) -> (same : selected = head) ->
  (decEq @{itemEq} selected head = Yes same) -> listMember @{itemEq} selected (head :: rest) = True
canonicalListMemberKnownYes item itemEq selected selected rest Refl observed = rewrite observed in Refl

0 canonicalListMemberKnownNo : (item : Type) -> (itemEq : DecEq item) ->
  (selected, head : item) -> (rest : List item) -> (different : Not (selected = head)) ->
  (decEq @{itemEq} selected head = No different) ->
  listMember @{itemEq} selected (head :: rest) = listMember @{itemEq} selected rest
canonicalListMemberKnownNo item itemEq selected head rest different observed = rewrite observed in Refl

0 canonicalListMemberCompleteStep : (item : Type) -> (itemEq : DecEq item) ->
  (selected, head : item) -> (rest : List item) ->
  (listMember @{itemEq} selected rest = True -> Elem selected rest) ->
  (decision : Dec (selected = head)) -> (decEq @{itemEq} selected head = decision) ->
  listMember @{itemEq} selected (head :: rest) = True -> Elem selected (head :: rest)
canonicalListMemberCompleteStep item itemEq selected head rest complete (Yes same) observed present =
  rewrite same in Here
canonicalListMemberCompleteStep item itemEq selected head rest complete (No different) observed present =
  There (complete (trans (sym (canonicalListMemberKnownNo item itemEq selected head rest different observed)) present))

0 canonicalListMemberComplete : (item : Type) -> (itemEq : DecEq item) ->
  (selected : item) -> (values : List item) -> listMember @{itemEq} selected values = True -> Elem selected values
canonicalListMemberComplete item itemEq selected [] present = absurd present
canonicalListMemberComplete item itemEq selected (head :: rest) present =
  canonicalListMemberCompleteStep item itemEq selected head rest
    (canonicalListMemberComplete item itemEq selected rest) (decEq @{itemEq} selected head) Refl present

0 canonicalListMemberSoundNo : (item : Type) -> (itemEq : DecEq item) ->
  (selected, head : item) -> (rest : List item) -> Not (selected = head) ->
  (listMember @{itemEq} selected (head :: rest) = listMember @{itemEq} selected rest) ->
  (Elem selected rest -> listMember @{itemEq} selected rest = True) ->
  Elem selected (head :: rest) -> listMember @{itemEq} selected (head :: rest) = True
canonicalListMemberSoundNo item itemEq selected head rest different observed sound present =
  case present of
    Here => void (different Refl)
    There later => trans observed (sound later)

0 canonicalListMemberSoundStep : (item : Type) -> (itemEq : DecEq item) ->
  (selected, head : item) -> (rest : List item) ->
  (Elem selected rest -> listMember @{itemEq} selected rest = True) ->
  (decision : Dec (selected = head)) -> (decEq @{itemEq} selected head = decision) ->
  Elem selected (head :: rest) -> listMember @{itemEq} selected (head :: rest) = True
canonicalListMemberSoundStep item itemEq selected head rest sound (Yes same) observed present =
  canonicalListMemberKnownYes item itemEq selected head rest same observed
canonicalListMemberSoundStep item itemEq selected head rest sound (No different) observed present =
  canonicalListMemberSoundNo item itemEq selected head rest different
    (canonicalListMemberKnownNo item itemEq selected head rest different observed) sound present

0 canonicalListMemberSound : (item : Type) -> (itemEq : DecEq item) ->
  (selected : item) -> (values : List item) -> Elem selected values -> listMember @{itemEq} selected values = True
canonicalListMemberSound item itemEq selected [] present = absurd present
canonicalListMemberSound item itemEq selected (head :: rest) present =
  canonicalListMemberSoundStep item itemEq selected head rest
    (canonicalListMemberSound item itemEq selected rest) (decEq @{itemEq} selected head) Refl present

||| Assemble exactly LinearizesSupport from the producer-owned sorted support set.
0 canonicalSupportOrderingFromSort :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  RegistryProtocolRanked protocol nameEq state -> RegistryParentRanksIncrease protocol nameEq state ->
  CanonicalRankSortResult name (canonicalProtocolRank name key world error value protocol nameEq state)
    (supportSet {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} @{keyEq} state) ->
  SupportOrderingCapital name key world error value nameEq keyEq state
canonicalSupportOrderingFromSort name key world error value protocol nameEq keyEq state ranked parentRanked sorted =
  MkSupportOrderingCapital (rankSortedItems sorted)
    (MkLinearizesSupport (rankSortedUnique sorted)
      (\selected, present => canonicalListMemberSound name nameEq selected
        (supportSet {name = name} {key = key} {value = value} {world = world} {error = error}
          @{nameEq} @{keyEq} state) (rankSortedBackward sorted selected present))
      (\selected, supported => rankSortedForward sorted selected
        (canonicalListMemberComplete name nameEq selected
          (supportSet {name = name} {key = key} {value = value} {world = world} {error = error}
            @{nameEq} @{keyEq} state) supported))
      (\lower, upper, path, lowerIn, upperIn => canonicalRankOrderBefore name
        (canonicalProtocolRank name key world error value protocol nameEq state)
        (rankSortedItems sorted) (rankSortedOrdered sorted) lower upper
        (canonicalRankedSupportPathStrict name key world error value protocol nameEq state lower upper
          (supportPathRankIncreases {name = name} {key = key} {value = value} {world = world} {error = error}
            protocol nameEq state ranked parentRanked path)) lowerIn upperIn))

||| Concrete reduction checks: nonmonotone ranks with a duplicate, and stable equal-rank names.
0 canonicalRankSortConcreteChecks :
  (rankSortedItems (canonicalStableRankSort Nat %search (\selected => selected) [3, 1, 2, 1, 0]) = [0, 1, 2, 3],
   rankSortedItems (canonicalStableRankSort Nat %search (\selected => 0) [3, 1, 2]) = [3, 1, 2])
canonicalRankSortConcreteChecks = (Refl, Refl)

||| Construct the finite linearization from re-established Lemma-68 capital.
public export
0 supportOrderingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  SupportOrderingCapital name key world error value nameEq keyEq finalState
supportOrderingSpike {name} {key} {world} {error} {value} {finalState} nameEq keyEq protocol trace bundle =
  canonicalSupportOrderingFromSort name key world error value protocol nameEq keyEq finalState
    (replayProtocolRanked bundle) (replayParentRanksIncrease bundle)
    (canonicalStableRankSort name nameEq
      (canonicalProtocolRank name key world error value protocol nameEq finalState)
      (supportSet {name = name} {key = key} {value = value} {world = world} {error = error}
        @{nameEq} @{keyEq} finalState))

||| Empty withdrawal lists have no inhabitants.  Keeping this eliminator local
||| avoids depending on the private analogue in the production support module.
0 canonicalElemEmpty : Elem item [] -> Void
canonicalElemEmpty Here impossible
canonicalElemEmpty (There later) impossible

||| Sorting base case: an unchanged endpoint is a canonical endpoint relation
||| with no current-name or historical-generation withdrawals.
0 canonicalSortingIdentityEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  CanonicalEndpointRelation name key world error value nameEq keyEq state state
canonicalSortingIdentityEndpoint nameEq keyEq state =
  MkCanonicalEndpointRelation [] []
    (MkEffectStateRelated Refl (\selected => Refl))
    (\selected, outside => fiberControlMaybeReflexive
      (lookupFiber @{nameEq} selected (registry state)))
    (\selected, present => void (canonicalElemEmpty present))
    (\selected, present => void (canonicalElemEmpty present))

||| Base assembly for a trace that already has the required actor blocks and
||| input placement.  This is the terminal case of the stable sorting proof.
0 canonicalSortedIdentity :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq
    keyEq trace) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    finalState) ->
  (blocks : (n : name) -> Elem n (orderedSupportNames ordering) ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n trace) ->
  (blocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier (orderedSupportNames ordering)) ->
    (laterIn : Elem later (orderedSupportNames ordering)) ->
    BeforeIn earlier later (orderedSupportNames ordering) ->
    BlockBefore name key world error value nameEq keyEq trace earlier later
      (blocks earlier earlierIn) (blocks later laterIn)) ->
  ((earlier, later : name) ->
    (earlierIn : Elem earlier (orderedSupportNames ordering)) ->
    (laterIn : Elem later (orderedSupportNames ordering)) ->
    BeforeIn earlier later (orderedSupportNames ordering) ->
    (earlierPosition, laterPosition : Nat) ->
    LTE (S earlierPosition) (S (transitionCount
      (blockBody (blocks earlier earlierIn)))) ->
    LTE (S laterPosition) (S (transitionCount
      (blockBody (blocks later laterIn)))) ->
    Not (transitionCount (traceBeforeBlock (blocks earlier earlierIn)) +
      earlierPosition = transitionCount
        (traceBeforeBlock (blocks later laterIn)) + laterPosition)) ->
  LifecycleActorsCovered (orderedSupportNames ordering) trace ->
  CanonicalInputPlacement name key world error value nameEq keyEq finalState
    (orderedSupportNames ordering) trace ->
  CanonicalRegistrationCorrespondence trace trace [] ->
  SortedClosingFreeTrace name key world error value protocol nameEq keyEq trace
    ordering
canonicalSortedIdentity nameEq keyEq protocol trace premises ordering blocks
  blocksFollowOrder rangesDisjoint lifecycleCoverage inputPlacement
  registrationTree =
    MkSortedClosingFreeTrace finalState trace
      (finiteDerivationReplayCorrespondence
        (the (FiniteAdjacentSwapDerivation name key world error value protocol
          nameEq keyEq trace trace) FiniteAdjacentSwapDone))
      (the (FiniteAdjacentSwapDerivation name key world error value protocol
        nameEq keyEq trace trace) FiniteAdjacentSwapDone) premises
      (sameExternalOrchestrationReflexiveSpike nameEq trace)
      blocks blocksFollowOrder rangesDisjoint lifecycleCoverage inputPlacement
      (canonicalSortingIdentityEndpoint nameEq keyEq finalState) Refl Refl
      registrationTree

||| O17 reached-state core: each transport fact is indexed by the same current trace.
||| Block ranges and a fixed desired order are later refinements, not assumed here.
record CanonicalSortingReplayState
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error) (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkCanonicalSortingReplayState
  sortingCurrentFinal : SystemState name key value world error
  sortingCurrentTrace : Transitions initial sortingCurrentFinal
  0 sortingReplayDerivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    original sortingCurrentTrace
  0 sortingCurrentPremises : ReplayInvariantBundle name key world error value protocol nameEq keyEq sortingCurrentTrace
  0 sortingCurrentExternal : SameExternalOrchestration nameEq original sortingCurrentTrace
  0 sortingCurrentEndpoint : RelationalReplayEndpoint name key world error value nameEq keyEq
    originalFinal sortingCurrentFinal

||| The current order is freshly produced from that exact reached bundle, not a fixed-order transport theorem.
0 canonicalSortingCurrentOrdering :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  SupportOrderingCapital name key world error value nameEq keyEq (sortingCurrentFinal current)
canonicalSortingCurrentOrdering name key world error value protocol nameEq keyEq current =
  supportOrderingSpike nameEq keyEq protocol (sortingCurrentTrace current) (sortingCurrentPremises current)

||| Generator/stage provenance is computed from the operational nodes, never copied independently.
0 canonicalSortingReplayCorrespondence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  RelationalReplayCorrespondence name key world error value original (sortingCurrentTrace current)
canonicalSortingReplayCorrespondence name key world error value protocol nameEq keyEq current =
  finiteDerivationReplayCorrespondence (sortingReplayDerivation current)

||| Action/generation origin is the exact finite derivation fold.
0 canonicalSortingOccurrenceCorrespondence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  ActionRegistrationReplayCorrespondence name key world error value original (sortingCurrentTrace current)
canonicalSortingOccurrenceCorrespondence name key world error value protocol nameEq keyEq current =
  finiteDerivationOccurrenceCorrespondence (sortingReplayDerivation current)

0 canonicalSortingReplayStart :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, originalFinal : SystemState name key value world error) ->
  (original : Transitions initial originalFinal) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  CanonicalSortingReplayState name key world error value protocol nameEq keyEq original
canonicalSortingReplayStart name key world error value protocol nameEq keyEq initial originalFinal original premises =
  MkCanonicalSortingReplayState originalFinal original FiniteAdjacentSwapDone premises
    (sameExternalOrchestrationReflexiveSpike nameEq original)
    (relationalReplayEndpointReflexiveSpike nameEq keyEq originalFinal (replayFinalWellFormed premises))

0 canonicalSortingDerivationAppend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, middleFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) -> (middleTrace : Transitions initial middleFinal) ->
  (target : Transitions initial targetFinal) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source middleTrace ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq middleTrace target ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target
canonicalSortingDerivationAppend name key world error value protocol nameEq keyEq source source target FiniteAdjacentSwapDone later = later
canonicalSortingDerivationAppend name key world error value protocol nameEq keyEq source middleTrace target
  (FiniteAdjacentSwapStep source prefixTrace left right suffix orientation diamond result middleTrace rest) later =
    FiniteAdjacentSwapStep source prefixTrace left right suffix orientation diamond result target
      (canonicalSortingDerivationAppend name key world error value protocol nameEq keyEq
        (swappedTrace result) middleTrace target rest later)

||| Compose one authentic local result into the same current-state origin chain.
0 canonicalSortingReplayExtend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  {pairFirst, pairMiddle, pairFinal : SystemState name key value world error} ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (sortingCurrentFinal current)) ->
  AdjacentSwapOrientationEvidence left right ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  AdjacentSwapResult name key world error value protocol nameEq keyEq
    (sortingCurrentTrace current) prefixTrace left right suffix diamond ->
  CanonicalSortingReplayState name key world error value protocol nameEq keyEq original
canonicalSortingReplayExtend name key world error value protocol nameEq keyEq original current
  prefixTrace left right suffix orientation diamond result =
    MkCanonicalSortingReplayState (replayedFinal result) (swappedTrace result)
      (canonicalSortingDerivationAppend name key world error value protocol nameEq keyEq
        original (sortingCurrentTrace current) (swappedTrace result) (sortingReplayDerivation current)
        (FiniteAdjacentSwapStep (sortingCurrentTrace current) prefixTrace left right suffix orientation
          diamond result (swappedTrace result) FiniteAdjacentSwapDone))
      (swappedPremises result)
      (sameExternalOrchestrationTransitiveSpike nameEq (sortingCurrentExternal current)
        (swappedSameExternalInputs result))
      (relationalReplayEndpointTransitiveSpike nameEq keyEq _ (sortingCurrentFinal current)
        (replayedFinal result) (sortingCurrentEndpoint current) (swappedEndpoint result))

||| Execute the frozen splice at the state's own full bundle; no moved trace is accepted.
0 canonicalSortingReplaySwap :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  {pairFirst, pairMiddle, pairFinal : SystemState name key value world error} ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (sortingCurrentFinal current)) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = sortingCurrentTrace current) ->
  AdjacentSwapOrientationEvidence left right ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)) ->
  CanonicalSortingReplayState name key world error value protocol nameEq keyEq original
canonicalSortingReplaySwap name key world error value protocol nameEq keyEq original current
  prefixTrace left right suffix decomposition orientation diamond pairExternal =
    canonicalSortingReplayExtend name key world error value protocol nameEq keyEq original current
      prefixTrace left right suffix orientation diamond
      (adjacentSwapSuffixSpike nameEq keyEq protocol (sortingCurrentTrace current) prefixTrace left right suffix
        decomposition (sortingCurrentPremises current) diamond pairExternal)

0 canonicalPaperActivationLifecycle :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {before, afterState : SystemState name key value world error} ->
  (transition : Transition before afterState) -> PaperActivationStep transition ->
  isLifecycleAction (transitionAction transition) = True
canonicalPaperActivationLifecycle name key world error value transition (PaperBeginStep action tag) = rewrite action in Refl
canonicalPaperActivationLifecycle name key world error value transition (PaperIterStep action tag) = rewrite action in Refl
canonicalPaperActivationLifecycle name key world error value transition (PaperFinishStep action tag) = rewrite action in Refl

0 canonicalRootChildInsertImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (root, child, parent : name) -> (rootComponent, childComponent : Component key value world error) ->
  (OInsert {name = name} root Root rootComponent = OInsert child (ChildOf parent) childComponent) -> Void
canonicalRootChildInsertImpossible _ _ _ _ _ _ _ _ _ _ Refl impossible

0 canonicalLifecycleInternal :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {before, afterState : SystemState name key value world error} ->
  (transition : Transition before afterState) -> isLifecycleAction (transitionAction transition) = True ->
  RootOrchestrationStep nameEq transition -> Void
canonicalLifecycleInternal name key world error value nameEq transition lifecycle (RootInsertStep action) =
  canonicalFalseNotTrue (trans (sym (cong isLifecycleAction action)) lifecycle)
canonicalLifecycleInternal name key world error value nameEq transition lifecycle (RootRetireStep fiber found parent action) =
  canonicalFalseNotTrue (trans (sym (cong isLifecycleAction action)) lifecycle)
canonicalLifecycleInternal name key world error value nameEq transition lifecycle (RootRemoveStep fiber found parent action) =
  canonicalFalseNotTrue (trans (sym (cong isLifecycleAction action)) lifecycle)

||| The sole root insertion stays the sole external input when hoisted across an activation.
0 canonicalRootInsertPairExternal :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle finalState) ->
  (root : name) -> (component : Component key value world error) ->
  PaperActivationStep left -> (transitionAction right = OInsert root Root component) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions))
canonicalRootInsertPairExternal name key world error value nameEq keyEq left right root component leftActivation rootAction diamond =
  SkipLeftInternal left (MoreTransitions right NoTransitions)
    (canonicalLifecycleInternal name key world error value nameEq left
      (canonicalPaperActivationLifecycle name key world error value left leftActivation))
    (MatchExternalInput (transitionAction right) right NoTransitions (RootInsertStep rootAction)
      (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)
      (RootInsertStep (trans (movedRightAction diamond) rootAction)) Refl (movedRightAction diamond)
      (SkipRightInternal (movedLeft diamond) NoTransitions
        (canonicalLifecycleInternal name key world error value nameEq (movedLeft diamond)
          (canonicalPaperActivationLifecycle name key world error value (movedLeft diamond)
            (movedLeftActivationBranch diamond leftActivation))) SameExternalOrchestrationEnd))

0 canonicalSortingPairAligned :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions left (MoreTransitions right NoTransitions))
canonicalSortingPairAligned name key world error value protocol nameEq keyEq original prefixTrace left right suffix decomposition premises =
  fst (alignedAppendSplit (MoreTransitions left (MoreTransitions right NoTransitions)) suffix
    (snd (alignedAppendSplit prefixTrace (MoreTransitions left (MoreTransitions right suffix))
      (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym decomposition) (replayAligned premises)))))

0 canonicalSortingPairSourceWellFormed :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  registryWellFormed {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} pairFirst = True
canonicalSortingPairSourceWellFormed name key world error value protocol nameEq keyEq original prefixTrace left right suffix decomposition premises =
  alignedTraceWellFormedEnd nameEq keyEq prefixTrace
    (fst (alignedAppendSplit prefixTrace (MoreTransitions left (MoreTransitions right suffix))
      (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym decomposition) (replayAligned premises))))
    (replayInitialWellFormed premises)

0 canonicalSortingAppendRightOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState, selectedBefore, selectedAfter : SystemState name key value world error} ->
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  (selected : Transition selectedBefore selectedAfter) ->
  OccursIn selected right -> OccursIn selected (appendTransitions left right)
canonicalSortingAppendRightOccurrence name key world error value NoTransitions right selected occurs = occurs
canonicalSortingAppendRightOccurrence name key world error value (MoreTransitions head rest) right selected occurs =
  OccursLater (canonicalSortingAppendRightOccurrence name key world error value rest right selected occurs)

0 canonicalSortingPairIndependent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  TraceIndependent name key world error value keyEq (MoreTransitions left (MoreTransitions right NoTransitions))
canonicalSortingPairIndependent name key world error value protocol nameEq keyEq original prefixTrace left right suffix decomposition premises =
  traceIndependentUnderEmbedding
    (\transition, occurs => replace {p = OccursIn transition} decomposition
      (canonicalSortingAppendRightOccurrence name key world error value prefixTrace
        (MoreTransitions left (MoreTransitions right suffix)) transition
        (appendLeftOccurrenceEmbedding (MoreTransitions left (MoreTransitions right NoTransitions)) suffix transition occurs)))
    (replayIndependent premises)

||| Derive the actual A/O diamond from a reached bundle and a distinct root insertion.
||| Early applicability, alignment and parent exclusion are produced, not extra caller premises.
0 canonicalRootInsertHoistDiamond :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (root : name) -> (component : Component key value world error) ->
  PaperActivationStep left -> (transitionAction right = OInsert root Root component) ->
  Not (transitionActor left = root) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
canonicalRootInsertHoistDiamond name key world error value protocol nameEq keyEq original prefixTrace left right suffix
  decomposition premises root component leftActivation rootAction different =
    activationOrchestrationDiamondSpike nameEq keyEq left right
      (canonicalSortingPairAligned name key world error value protocol nameEq keyEq original prefixTrace left right suffix decomposition premises)
      leftActivation (PaperInsertStep rootAction)
      (\same => different (trans same
        (trans (canonicalTransitionActorActionOwner right) (cong actionOwner rootAction))))
      (\child, parent, childComponent, childAction, actorSame =>
        canonicalRootChildInsertImpossible name key world error value root child parent component childComponent
          (trans (sym rootAction) childAction))
      (canonicalSortingPairSourceWellFormed name key world error value protocol nameEq keyEq original prefixTrace left right suffix decomposition premises)
      (canonicalSortingPairIndependent name key world error value protocol nameEq keyEq original prefixTrace left right suffix decomposition premises)

||| One root-hoist result owns the diamond, replay and exact moved root action together.
record CanonicalRootInsertionHoist
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error) (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) (prefixTrace : Transitions initial pairFirst)
  (left : Transition pairFirst pairMiddle) (right : Transition pairMiddle pairFinal)
  (suffix : Transitions pairFinal originalFinal) (root : name) (component : Component key value world error) where
  constructor MkCanonicalRootInsertionHoist
  rootHoistDiamond : LocalRelationalDiamond name key world error value nameEq keyEq left right
  rootHoistResult : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original prefixTrace left right suffix rootHoistDiamond
  0 rootHoistedAction : (transitionAction (movedRight rootHoistDiamond) = OInsert root Root component)

0 canonicalRootInsertionHoistFromDiamond :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (root : name) -> (component : Component key value world error) ->
  PaperActivationStep left -> (transitionAction right = OInsert root Root component) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component
canonicalRootInsertionHoistFromDiamond name key world error value protocol nameEq keyEq original prefixTrace left right suffix
  decomposition premises root component leftActivation rootAction diamond =
    MkCanonicalRootInsertionHoist diamond
      (adjacentSwapSuffixSpike nameEq keyEq protocol original prefixTrace left right suffix decomposition premises diamond
        (canonicalRootInsertPairExternal name key world error value nameEq keyEq left right root component leftActivation rootAction diamond))
      (trans (movedRightAction diamond) rootAction)

||| A genuine nontrivial root insertion hoist, with no supplied target, diamond or external-order proof.
0 canonicalRootInsertionHoist :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (root : name) -> (component : Component key value world error) ->
  PaperActivationStep left -> (transitionAction right = OInsert root Root component) ->
  Not (transitionActor left = root) ->
  CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component
canonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix
  decomposition premises root component leftActivation rootAction different =
    canonicalRootInsertionHoistFromDiamond name key world error value protocol nameEq keyEq original prefixTrace left right suffix
      decomposition premises root component leftActivation rootAction
      (canonicalRootInsertHoistDiamond name key world error value protocol nameEq keyEq original prefixTrace left right suffix
        decomposition premises root component leftActivation rootAction different)

||| Locate the moved root at the exact producer-owned prefix in the returned trace.
0 canonicalHoistedRootOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) -> (root : name) -> (component : Component key value world error) ->
  (hoist : CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component) ->
  LocatedActionOccurrence (OInsert root Root component) (swappedTrace (rootHoistResult hoist))
canonicalHoistedRootOccurrence name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist =
  MkLocatedActionOccurrence _ _ prefixTrace (movedRight (rootHoistDiamond hoist))
    (MoreTransitions (movedLeft (rootHoistDiamond hoist)) (replayedSuffix (rootHoistResult hoist)))
    (rootHoistedAction hoist) (sym (swappedDecomposition (rootHoistResult hoist)))

0 canonicalHoistedRootOrdinal :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) -> (root : name) -> (component : Component key value world error) ->
  (hoist : CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component) ->
  (locatedActionOrdinal (canonicalHoistedRootOccurrence name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist) = transitionCount prefixTrace)
canonicalHoistedRootOrdinal name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist = Refl

0 canonicalOriginalHoistedRootOccurrence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) -> (root : name) -> (component : Component key value world error) ->
  (hoist : CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component) ->
  LocatedActionOccurrence (OInsert root Root component) original
canonicalOriginalHoistedRootOccurrence name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist =
  MkLocatedActionOccurrence _ _ (appendTransitions prefixTrace (MoreTransitions left NoTransitions)) right suffix
    (trans (sym (movedRightAction (rootHoistDiamond hoist))) (rootHoistedAction hoist))
    (trans (appendTransitionsAssociative prefixTrace (MoreTransitions left NoTransitions) (MoreTransitions right suffix))
      (originalDecomposition (rootHoistResult hoist)))

0 canonicalSortingPrefixSnocCount :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {initial, before, afterState : SystemState name key value world error} ->
  (prefixTrace : Transitions initial before) -> (transition : Transition before afterState) ->
  transitionCount (appendTransitions prefixTrace (MoreTransitions transition NoTransitions)) = S (transitionCount prefixTrace)
canonicalSortingPrefixSnocCount name key world error value NoTransitions transition = Refl
canonicalSortingPrefixSnocCount name key world error value (MoreTransitions head rest) transition =
  cong S (canonicalSortingPrefixSnocCount name key world error value rest transition)

||| An actual hoisted root moves left by exactly one ordinal, not merely to an equal endpoint.
0 canonicalRootHoistMovesOneOrdinal :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) -> (root : name) -> (component : Component key value world error) ->
  (hoist : CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component) ->
  (S (locatedActionOrdinal (canonicalHoistedRootOccurrence name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist)) =
    locatedActionOrdinal (canonicalOriginalHoistedRootOccurrence name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist))
canonicalRootHoistMovesOneOrdinal name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist =
  sym (canonicalSortingPrefixSnocCount name key world error value prefixTrace left)

0 canonicalRootHoistNonempty :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) -> (root : name) -> (component : Component key value world error) ->
  (hoist : CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component) ->
  PaperActivationStep left ->
  NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    original (swappedTrace (rootHoistResult hoist))
canonicalRootHoistNonempty name key world error value protocol nameEq keyEq original prefixTrace left right suffix root component hoist leftActivation =
  NonEmptyAdjacentSwap original prefixTrace left right suffix
    (AdjacentActivationOrchestration left right leftActivation
      (PaperInsertStep (trans (sym (movedRightAction (rootHoistDiamond hoist))) (rootHoistedAction hoist))))
    (rootHoistDiamond hoist) (rootHoistResult hoist) (swappedTrace (rootHoistResult hoist)) FiniteAdjacentSwapDone

0 canonicalSortingAcceptRootHoist :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  {pairFirst, pairMiddle, pairFinal : SystemState name key value world error} ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (sortingCurrentFinal current)) ->
  (root : name) -> (component : Component key value world error) -> PaperActivationStep left ->
  CanonicalRootInsertionHoist name key world error value protocol nameEq keyEq
    (sortingCurrentTrace current) prefixTrace left right suffix root component ->
  CanonicalSortingReplayState name key world error value protocol nameEq keyEq original
canonicalSortingAcceptRootHoist name key world error value protocol nameEq keyEq original current
  prefixTrace left right suffix root component leftActivation hoist =
    canonicalSortingReplayExtend name key world error value protocol nameEq keyEq original current
      prefixTrace left right suffix
      (AdjacentActivationOrchestration left right leftActivation
        (PaperInsertStep (trans (sym (movedRightAction (rootHoistDiamond hoist))) (rootHoistedAction hoist))))
      (rootHoistDiamond hoist) (rootHoistResult hoist)

0 canonicalSortingHoistRoot :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  {pairFirst, pairMiddle, pairFinal : SystemState name key value world error} ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (sortingCurrentFinal current)) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = sortingCurrentTrace current) ->
  (root : name) -> (component : Component key value world error) -> PaperActivationStep left ->
  (transitionAction right = OInsert root Root component) -> Not (transitionActor left = root) ->
  CanonicalSortingReplayState name key world error value protocol nameEq keyEq original
canonicalSortingHoistRoot name key world error value protocol nameEq keyEq original current
  prefixTrace left right suffix decomposition root component leftActivation rootAction different =
    canonicalSortingAcceptRootHoist name key world error value protocol nameEq keyEq original current
      prefixTrace left right suffix root component leftActivation
      (canonicalRootInsertionHoist name key world error value protocol nameEq keyEq
        (sortingCurrentTrace current) prefixTrace left right suffix decomposition (sortingCurrentPremises current)
        root component leftActivation rootAction different)

0 canonicalSortingLifecycleActiveSame :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {left, right : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated left right -> isActive left = isActive right
canonicalSortingLifecycleActiveSame name key world error value (InactiveControls outcome) = Refl
canonicalSortingLifecycleActiveSame name key world error value (ReloadingControls remaining accumulator view) = Refl
canonicalSortingLifecycleActiveSame name key world error value (ActiveControls accumulator view) = Refl
canonicalSortingLifecycleActiveSame name key world error value (UnloadingControls accumulator view outcome) = Refl

0 canonicalSortingFiberActiveSame :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {left, right : Fiber name key value world error} -> FiberControlRelated left right ->
  isActive (fiberLifecycle left) = isActive (fiberLifecycle right)
canonicalSortingFiberActiveSame name key world error value
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) =
      canonicalSortingLifecycleActiveSame name key world error value lifecycleSame

0 canonicalSortingFiberComponentSame :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {left, right : Fiber name key value world error} -> FiberControlRelated left right ->
  fiberComponent left = fiberComponent right
canonicalSortingFiberComponentSame name key world error value
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) = Refl

0 canonicalSortingFiberParentSame :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {left, right : Fiber name key value world error} -> FiberControlRelated left right ->
  fiberParent left = fiberParent right
canonicalSortingFiberParentSame name key world error value
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable rightTable
    leftLifecycle rightLifecycle parentSame retiredSame lifecycleSame) = parentSame

0 canonicalSortingSupportFromRelatedActive :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (source, target : SystemState name key value world error) -> (selected : name) ->
  (rankView : CanonicalActiveRank name key world error value protocol nameEq source selected) ->
  ForeignRelatedFiberFound name key world error value nameEq selected (registry source) (registry target) (activeRankFiber rankView) ->
  SupportMatchesActive nameEq keyEq target ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected target = True
canonicalSortingSupportFromRelatedActive name key world error value protocol nameEq keyEq source target selected rankView related targetMatches =
  trans (targetMatches selected)
    (trans (canonicalSupportedActiveAtFound name key world error value nameEq target selected
      (foreignRelatedFiber related) (foreignRelatedFound related))
      (trans (sym (canonicalSortingFiberActiveSame name key world error value (foreignRelatedControl related)))
        (activeRankActive rankView)))

0 canonicalSortingSupportFromActiveRank :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (source, target : SystemState name key value world error) -> (selected : name) ->
  CanonicalActiveRank name key world error value protocol nameEq source selected ->
  ControlEquivalent name key world error value nameEq source target -> SupportMatchesActive nameEq keyEq target ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected target = True
canonicalSortingSupportFromActiveRank name key world error value protocol nameEq keyEq source target selected rankView controls targetMatches =
  canonicalSortingSupportFromRelatedActive name key world error value protocol nameEq keyEq source target selected rankView
    (foreignControlLookupFound {name = name} {key = key} {value = value} {world = world} {error = error}
      nameEq selected (registry source) (registry target) (activeRankFiber rankView) (activeRankFound rankView)
      (controlPointwise controls selected)) targetMatches

||| Full no-withdrawal control equivalence transports support truth; not the refuted deletion transfer.
0 canonicalSortingSupportTrueForward :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (source, target : SystemState name key value world error) ->
  RegistryProtocolRanked protocol nameEq source -> SupportMatchesActive nameEq keyEq source ->
  SupportMatchesActive nameEq keyEq target -> ControlEquivalent name key world error value nameEq source target ->
  (selected : name) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected source = True) ->
  isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected target = True
canonicalSortingSupportTrueForward name key world error value protocol nameEq keyEq source target ranked sourceMatches targetMatches controls selected supported =
  canonicalSortingSupportFromActiveRank name key world error value protocol nameEq keyEq source target selected
    (canonicalSupportedRank name key world error value protocol nameEq keyEq source selected supported sourceMatches ranked)
    controls targetMatches

0 canonicalSortingPrecedenceFromFibers :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) -> (lower, upper : name) ->
  (edge : PrecedenceEdge nameEq lower upper source) ->
  ForeignRelatedFiberFound name key world error value nameEq lower (registry source) (registry target) (providerFiber edge) ->
  ForeignRelatedFiberFound name key world error value nameEq upper (registry source) (registry target) (consumerFiber edge) ->
  PrecedenceEdge nameEq lower upper target
canonicalSortingPrecedenceFromFibers name key world error value nameEq source target lower upper edge lowerTarget upperTarget =
  MkPrecedenceEdge (edgeKey edge) (foreignRelatedFiber lowerTarget) (foreignRelatedFiber upperTarget)
    (foreignRelatedFound lowerTarget) (foreignRelatedFound upperTarget)
    (replace {p = \component => Elem (edgeKey edge) (dependencies (componentProvisions component))}
      (canonicalSortingFiberComponentSame name key world error value (foreignRelatedControl lowerTarget)) (providerDeclares edge))
    (replace {p = \component => Elem (edgeKey edge) (dependencies (componentDependencies component))}
      (canonicalSortingFiberComponentSame name key world error value (foreignRelatedControl upperTarget)) (consumerDeclares edge))

0 canonicalSortingPrecedenceForward :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) -> ControlEquivalent name key world error value nameEq source target ->
  (lower, upper : name) -> PrecedenceEdge nameEq lower upper source -> PrecedenceEdge nameEq lower upper target
canonicalSortingPrecedenceForward name key world error value nameEq source target controls lower upper edge =
  canonicalSortingPrecedenceFromFibers name key world error value nameEq source target lower upper edge
    (foreignControlLookupFound {name = name} {key = key} {value = value} {world = world} {error = error}
      nameEq lower (registry source) (registry target) (providerFiber edge) (providerFound edge) (controlPointwise controls lower))
    (foreignControlLookupFound {name = name} {key = key} {value = value} {world = world} {error = error}
      nameEq upper (registry source) (registry target) (consumerFiber edge) (consumerFound edge) (controlPointwise controls upper))

0 canonicalSortingParentFromFiber :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) -> (parent, child : name) ->
  (edge : ParentSupportEdge nameEq parent child source) ->
  ForeignRelatedFiberFound name key world error value nameEq child (registry source) (registry target) (childFiber edge) ->
  ParentSupportEdge nameEq parent child target
canonicalSortingParentFromFiber name key world error value nameEq source target parent child edge targetChild =
  MkParentSupportEdge (foreignRelatedFiber targetChild) (foreignRelatedFound targetChild)
    (trans (sym (canonicalSortingFiberParentSame name key world error value (foreignRelatedControl targetChild))) (childParent edge))

0 canonicalSortingParentForward :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) -> ControlEquivalent name key world error value nameEq source target ->
  (parent, child : name) -> ParentSupportEdge nameEq parent child source -> ParentSupportEdge nameEq parent child target
canonicalSortingParentForward name key world error value nameEq source target controls parent child edge =
  canonicalSortingParentFromFiber name key world error value nameEq source target parent child edge
    (foreignControlLookupFound {name = name} {key = key} {value = value} {world = world} {error = error}
      nameEq child (registry source) (registry target) (childFiber edge) (childFound edge) (controlPointwise controls child))

0 canonicalSortingSupportEdgeForward :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) -> ControlEquivalent name key world error value nameEq source target ->
  (lower, upper : name) -> SupportEdge nameEq source lower upper -> SupportEdge nameEq target lower upper
canonicalSortingSupportEdgeForward name key world error value nameEq source target controls lower upper (SupportPrecedence edge) =
  SupportPrecedence (canonicalSortingPrecedenceForward name key world error value nameEq source target controls lower upper edge)
canonicalSortingSupportEdgeForward name key world error value nameEq source target controls lower upper (SupportParent edge) =
  SupportParent (canonicalSortingParentForward name key world error value nameEq source target controls lower upper edge)

0 canonicalSortingSupportPathForward :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (source, target : SystemState name key value world error) -> ControlEquivalent name key world error value nameEq source target ->
  (lower, upper : name) -> SupportPath nameEq source lower upper -> SupportPath nameEq target lower upper
canonicalSortingSupportPathForward name key world error value nameEq source target controls lower upper (SupportPathOne edge) =
  SupportPathOne (canonicalSortingSupportEdgeForward name key world error value nameEq source target controls lower upper edge)
canonicalSortingSupportPathForward name key world error value nameEq source target controls lower upper (SupportPathMore edge rest) =
  SupportPathMore (canonicalSortingSupportEdgeForward name key world error value nameEq source target controls lower _ edge)
    (canonicalSortingSupportPathForward name key world error value nameEq source target controls _ upper rest)

||| Transport the SAME fixed list through a no-withdrawal replay, not an arbitrary deletion.
0 canonicalSortingFixedLinearization :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (source, target : SystemState name key value world error) ->
  RegistryProtocolRanked protocol nameEq source -> RegistryProtocolRanked protocol nameEq target ->
  SupportMatchesActive nameEq keyEq source -> SupportMatchesActive nameEq keyEq target ->
  ControlEquivalent name key world error value nameEq source target -> (order : List name) ->
  LinearizesSupport name key world error value nameEq keyEq source order ->
  LinearizesSupport name key world error value nameEq keyEq target order
canonicalSortingFixedLinearization name key world error value protocol nameEq keyEq source target
  sourceRanked targetRanked sourceMatches targetMatches controls order linearization =
    MkLinearizesSupport (orderUnique linearization)
      (\selected, present => canonicalSortingSupportTrueForward name key world error value protocol nameEq keyEq
        source target sourceRanked sourceMatches targetMatches controls selected (orderSound linearization selected present))
      (\selected, supported => orderComplete linearization selected
        (canonicalSortingSupportTrueForward name key world error value protocol nameEq keyEq target source
          targetRanked targetMatches sourceMatches (controlEquivalentSymmetric controls) selected supported))
      (\lower, upper, path, lowerIn, upperIn => supportPathsOrdered linearization lower upper
        (canonicalSortingSupportPathForward name key world error value nameEq target source
          (controlEquivalentSymmetric controls) lower upper path) lowerIn upperIn)

||| A single action admitted inside one actor's contiguous activation block.
||| This is only structural membership, never an applicability assumption.
data CanonicalWorkActorStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  (selected : name) -> (step : Transition before afterState) -> Type where
  CanonicalWorkLifecycle :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {before, afterState : SystemState name key value world error} ->
    {selected : name} -> {step : Transition before afterState} ->
    (0 lifecycle : isLifecycleAction (transitionAction step) = True) ->
    (0 actor : transitionActor step = selected) -> CanonicalWorkActorStep selected step
  CanonicalWorkRegistration :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {before, afterState : SystemState name key value world error} ->
    {selected, child : name} -> {component : Component key value world error} ->
    {step : Transition before afterState} ->
    (0 action : transitionAction step = OInsert child (ChildOf selected) component) ->
    CanonicalWorkActorStep selected step

0 canonicalWorkClassifyActor :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  {before, afterState : SystemState name key value world error} ->
  (step : Transition before afterState) -> Dec (CanonicalWorkActorStep selected step)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (OInsert child Root component) tag checked) =
  No (\member => case member of
    CanonicalWorkLifecycle lifecycle actor => case lifecycle of Refl impossible
    CanonicalWorkRegistration action => case action of Refl impossible)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (OInsert child (ChildOf parent) component) tag checked) =
  case decEq @{nameEq} parent selected of
    Yes same => Yes (CanonicalWorkRegistration (cong (\actual => OInsert child (ChildOf actual) component) same))
    No different => No (\member => case member of
      CanonicalWorkLifecycle lifecycle actor => case lifecycle of Refl impossible
      CanonicalWorkRegistration action => case action of Refl => different Refl)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (ORetire actor) tag checked) =
  No (\member => case member of
    CanonicalWorkLifecycle lifecycle same => case lifecycle of Refl impossible
    CanonicalWorkRegistration action => case action of Refl impossible)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (ORemove actor) tag checked) =
  No (\member => case member of
    CanonicalWorkLifecycle lifecycle same => case lifecycle of Refl impossible
    CanonicalWorkRegistration action => case action of Refl impossible)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (LBegin actor) tag checked) =
  case decEq @{nameEq} actor selected of
    Yes same => Yes (CanonicalWorkLifecycle Refl same)
    No different => No (\member => case member of
      CanonicalWorkLifecycle lifecycle same => different same
      CanonicalWorkRegistration action => case action of Refl impossible)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (LAdvance actor) tag checked) =
  case decEq @{nameEq} actor selected of
    Yes same => Yes (CanonicalWorkLifecycle Refl same)
    No different => No (\member => case member of
      CanonicalWorkLifecycle lifecycle same => different same
      CanonicalWorkRegistration action => case action of Refl impossible)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (LDivert actor) tag checked) =
  case decEq @{nameEq} actor selected of
    Yes same => Yes (CanonicalWorkLifecycle Refl same)
    No different => No (\member => case member of
      CanonicalWorkLifecycle lifecycle same => different same
      CanonicalWorkRegistration action => case action of Refl impossible)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (LLeave actor) tag checked) =
  case decEq @{nameEq} actor selected of
    Yes same => Yes (CanonicalWorkLifecycle Refl same)
    No different => No (\member => case member of
      CanonicalWorkLifecycle lifecycle same => different same
      CanonicalWorkRegistration action => case action of Refl impossible)
canonicalWorkClassifyActor name key world error value nameEq selected (Fired stepNameEq stepKeyEq (LUnload actor) tag checked) =
  case decEq @{nameEq} actor selected of
    Yes same => Yes (CanonicalWorkLifecycle Refl same)
    No different => No (\member => case member of
      CanonicalWorkLifecycle lifecycle same => different same
      CanonicalWorkRegistration action => case action of Refl impossible)

||| Maximal-prefix stopping evidence is tied to the actual remaining trace.
data CanonicalWorkActorBoundary :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (selected : name) -> Transitions first finalState -> Type where
  CanonicalWorkBoundaryEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {state : SystemState name key value world error} -> {selected : name} ->
    CanonicalWorkActorBoundary selected (NoTransitions {state})
  CanonicalWorkBoundaryBlocked :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {selected : name} -> (step : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (0 foreign : Not (CanonicalWorkActorStep selected step)) ->
    CanonicalWorkActorBoundary selected (MoreTransitions step rest)

||| The structural scan simultaneously owns its actual pieces, actor proof,
||| boundary and exact count equation; no existential state equality is guessed.
record CanonicalWorkActorPrefix
  (name, key, world, error : Type) (value : key -> Type) (selected : name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkCanonicalWorkActorPrefix
  workPrefixEnd : SystemState name key value world error
  workActorPrefix : Transitions first workPrefixEnd
  workActorRest : Transitions workPrefixEnd finalState
  0 workPrefixActorOnly : ActorLifecycleOnly selected workActorPrefix
  0 workPrefixDecomposition : appendTransitions workActorPrefix workActorRest = trace
  0 workPrefixCountSplit : transitionCount workActorPrefix + transitionCount workActorRest = transitionCount trace
  0 workPrefixBoundary : CanonicalWorkActorBoundary selected workActorRest

0 canonicalWorkActorPrefixCons :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  CanonicalWorkActorStep selected step ->
  CanonicalWorkActorPrefix name key world error value selected rest ->
  CanonicalWorkActorPrefix name key world error value selected (MoreTransitions step rest)
canonicalWorkActorPrefixCons name key world error value selected step rest (CanonicalWorkLifecycle lifecycle actor) tail =
  MkCanonicalWorkActorPrefix (workPrefixEnd tail) (MoreTransitions step (workActorPrefix tail)) (workActorRest tail)
    (ActorLifecycleStep step (workActorPrefix tail) lifecycle actor (workPrefixActorOnly tail))
    (cong (MoreTransitions step) (workPrefixDecomposition tail))
    (cong S (workPrefixCountSplit tail)) (workPrefixBoundary tail)
canonicalWorkActorPrefixCons name key world error value selected step rest (CanonicalWorkRegistration action) tail =
  MkCanonicalWorkActorPrefix (workPrefixEnd tail) (MoreTransitions step (workActorPrefix tail)) (workActorRest tail)
    (ActorYieldedRegistrationStep step (workActorPrefix tail) action (workPrefixActorOnly tail))
    (cong (MoreTransitions step) (workPrefixDecomposition tail))
    (cong S (workPrefixCountSplit tail)) (workPrefixBoundary tail)

||| Strictly structural/decreasing scan of the real trace, not supplied pieces.
0 canonicalWorkScanActorPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  CanonicalWorkActorPrefix name key world error value selected trace
canonicalWorkScanActorPrefix name key world error value nameEq selected NoTransitions =
  MkCanonicalWorkActorPrefix _ NoTransitions NoTransitions ActorLifecycleEnd Refl Refl CanonicalWorkBoundaryEnd
canonicalWorkScanActorPrefix name key world error value nameEq selected (MoreTransitions step rest) =
  case canonicalWorkClassifyActor name key world error value nameEq selected step of
    Yes owned => canonicalWorkActorPrefixCons name key world error value selected step rest owned
      (canonicalWorkScanActorPrefix name key world error value nameEq selected rest)
    No foreign => MkCanonicalWorkActorPrefix _ NoTransitions (MoreTransitions step rest)
      ActorLifecycleEnd Refl Refl (CanonicalWorkBoundaryBlocked step rest foreign)

0 canonicalWorkNoLifecycleCons :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (isLifecycleAction (transitionAction step) = True -> Not (transitionActor step = selected)) ->
  Dec (NoLifecycleBy selected rest) -> Dec (NoLifecycleBy selected (MoreTransitions step rest))
canonicalWorkNoLifecycleCons name key world error value selected step rest excluded (Yes tail) =
  Yes (NoLifecycleByStep step rest excluded tail)
canonicalWorkNoLifecycleCons name key world error value selected step rest excluded (No notTail) =
  No (\whole => case whole of NoLifecycleByStep head tail headExcluded tailExcluded => notTail tailExcluded)

0 canonicalWorkDecNoLifecycle :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> Dec (NoLifecycleBy selected trace)
canonicalWorkDecNoLifecycle name key world error value nameEq selected NoTransitions = Yes NoLifecycleByEnd
canonicalWorkDecNoLifecycle name key world error value nameEq selected (MoreTransitions step rest) =
  case decEq (isLifecycleAction (transitionAction step)) True of
    No notLifecycle => canonicalWorkNoLifecycleCons name key world error value selected step rest
      (\lifecycle, same => notLifecycle lifecycle)
      (canonicalWorkDecNoLifecycle name key world error value nameEq selected rest)
    Yes lifecycle => case decEq @{nameEq} (transitionActor step) selected of
      No different => canonicalWorkNoLifecycleCons name key world error value selected step rest
        (\isLife => different) (canonicalWorkDecNoLifecycle name key world error value nameEq selected rest)
      Yes same => No (\whole => case whole of
        NoLifecycleByStep head tail excluded tailExcluded => excluded lifecycle same)

0 canonicalWorkInstalledPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prefixTrace : Transitions first middle) -> (suffix : Transitions middle finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected (appendTransitions prefixTrace suffix) ->
  InstalledTrace name key world error value nameEq keyEq selected prefixTrace
canonicalWorkInstalledPrefix name key world error value nameEq keyEq selected NoTransitions suffix installed =
  InstalledEnd (installedTraceStart installed)
canonicalWorkInstalledPrefix name key world error value nameEq keyEq selected (MoreTransitions _ rest) suffix
  (InstalledStep action tag checked _ sourceInstalled tailInstalled) =
    InstalledStep action tag checked rest sourceInstalled
      (canonicalWorkInstalledPrefix name key world error value nameEq keyEq selected rest suffix tailInstalled)

||| Construct the contiguous block from actual scanned pieces. It does not
||| receive a block, target state, target trace, or final schedule from a caller.
0 canonicalWorkBlockFromPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
  (scanned : CanonicalWorkActorPrefix name key world error value selected (openInside episode)) ->
  NoLifecycleBy selected (workActorRest scanned) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected trace
canonicalWorkBlockFromPrefix name key world error value nameEq keyEq selected trace episode scanned noLater =
  MkLocatedOpenEpisodeBlock (openPreStart episode) (openStart episode) (workPrefixEnd scanned)
    (openPrefix episode) (openBegin episode) (workActorPrefix scanned)
    (canonicalWorkInstalledPrefix name key world error value nameEq keyEq selected (workActorPrefix scanned) (workActorRest scanned)
      (replace {p = InstalledTrace name key world error value nameEq keyEq selected}
        (sym (workPrefixDecomposition scanned)) (openInstalled episode)))
    (workPrefixActorOnly scanned) (workActorRest scanned) (openNoEarlierLifecycle episode) noLater (openActiveAtFinal episode)
    (trans (cong (\body => appendTransitions (openPrefix episode)
      (MoreTransitions (beginTransition (openBegin episode)) body)) (workPrefixDecomposition scanned)) (openDecomposition episode))

||| A ready branch owns scanned pieces plus checked no-later-lifecycle evidence;
||| its block is DERIVED by canonicalWorkBlockFromPrefix, never supplied here.
||| The other branch retains a genuine remaining grouping obligation.
data CanonicalWorkOpenInspection :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace -> Type where
  CanonicalWorkOpenReady :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
    {initial, finalState : SystemState name key value world error} ->
    {trace : Transitions initial finalState} ->
    {episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace} ->
    (scanned : CanonicalWorkActorPrefix name key world error value selected (openInside episode)) ->
    (0 noLater : NoLifecycleBy selected (workActorRest scanned)) ->
    CanonicalWorkOpenInspection name key world error value nameEq keyEq selected trace episode
  CanonicalWorkOpenInterleaved :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
    {initial, finalState : SystemState name key value world error} ->
    {trace : Transitions initial finalState} ->
    {episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace} ->
    (scanned : CanonicalWorkActorPrefix name key world error value selected (openInside episode)) ->
    (0 laterRemains : Not (NoLifecycleBy selected (workActorRest scanned))) ->
    CanonicalWorkOpenInspection name key world error value nameEq keyEq selected trace episode

0 canonicalWorkInspectScanned :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
  CanonicalWorkActorPrefix name key world error value selected (openInside episode) ->
  CanonicalWorkOpenInspection name key world error value nameEq keyEq selected trace episode
canonicalWorkInspectScanned name key world error value nameEq keyEq selected trace episode scanned =
  case canonicalWorkDecNoLifecycle name key world error value nameEq selected (workActorRest scanned) of
    Yes noLater => CanonicalWorkOpenReady scanned noLater
    No laterRemains => CanonicalWorkOpenInterleaved scanned laterRemains

||| Actual finite episode inspection: no caller-provided prefix or block.
public export
0 canonicalWorkInspectOpenEpisode :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
  CanonicalWorkOpenInspection name key world error value nameEq keyEq selected trace episode
canonicalWorkInspectOpenEpisode name key world error value nameEq keyEq selected trace episode =
  canonicalWorkInspectScanned name key world error value nameEq keyEq selected trace episode
    (canonicalWorkScanActorPrefix name key world error value nameEq selected (openInside episode))

||| Exact half-open range of a PRODUCED block; both counts are authenticated
||| against that same block's existential trace pieces.
record CanonicalWorkCompletedBlock
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkCanonicalWorkCompletedBlock
  workCompletedBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected trace
  workRangeStart : Nat
  workRangeSize : Nat
  0 workRangeStartExact : transitionCount (traceBeforeBlock workCompletedBlock) = workRangeStart
  0 workRangeSizeExact : S (transitionCount (blockBody workCompletedBlock)) = workRangeSize

0 canonicalWorkCompleteBlock :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
  (scanned : CanonicalWorkActorPrefix name key world error value selected (openInside episode)) ->
  NoLifecycleBy selected (workActorRest scanned) ->
  CanonicalWorkCompletedBlock name key world error value nameEq keyEq selected trace
canonicalWorkCompleteBlock name key world error value nameEq keyEq selected trace episode scanned noLater =
  MkCanonicalWorkCompletedBlock
    (canonicalWorkBlockFromPrefix name key world error value nameEq keyEq selected trace episode scanned noLater)
    (transitionCount (openPrefix episode)) (S (transitionCount (workActorPrefix scanned))) Refl Refl

||| Decreasing inspection worklist. Ready nodes own actual produced blocks AND
||| ordered, nonoverlapping numeric ranges; a blocked node explicitly retains
||| the next unresolved grouping/order obligation. This is NOT a sorter.
data CanonicalWorklistInspection :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> (pending : List name) -> (minimumStart : Nat) -> Type where
  CanonicalWorklistEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, finalState : SystemState name key value world error} ->
    {trace : Transitions initial finalState} ->
    {minimumStart : Nat} ->
    CanonicalWorklistInspection name key world error value nameEq keyEq trace [] minimumStart
  CanonicalWorklistReady :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, finalState : SystemState name key value world error} ->
    {trace : Transitions initial finalState} ->
    {selected : name} -> {remaining : List name} -> {minimumStart : Nat} ->
    (completed : CanonicalWorkCompletedBlock name key world error value nameEq keyEq selected trace) ->
    (0 startsAfter : LTE minimumStart (workRangeStart completed)) ->
    CanonicalWorklistInspection name key world error value nameEq keyEq trace remaining
      (workRangeStart completed + workRangeSize completed) ->
    CanonicalWorklistInspection name key world error value nameEq keyEq trace (selected :: remaining) minimumStart
  CanonicalWorklistNeedsGrouping :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, finalState : SystemState name key value world error} ->
    {trace : Transitions initial finalState} ->
    {selected : name} -> {remaining : List name} -> {minimumStart : Nat} ->
    (episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
    (scanned : CanonicalWorkActorPrefix name key world error value selected (openInside episode)) ->
    (0 laterRemains : Not (NoLifecycleBy selected (workActorRest scanned))) ->
    CanonicalWorklistInspection name key world error value nameEq keyEq trace (selected :: remaining) minimumStart
  CanonicalWorklistNeedsOrdering :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, finalState : SystemState name key value world error} ->
    {trace : Transitions initial finalState} ->
    {selected : name} -> {remaining : List name} -> {minimumStart : Nat} ->
    (completed : CanonicalWorkCompletedBlock name key world error value nameEq keyEq selected trace) ->
    (0 startsTooEarly : Not (LTE minimumStart (workRangeStart completed))) ->
    CanonicalWorklistInspection name key world error value nameEq keyEq trace (selected :: remaining) minimumStart

0 canonicalWorkContinueCompleted :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> (selected : name) ->
  (remaining : List name) -> (minimumStart : Nat) ->
  (completed : CanonicalWorkCompletedBlock name key world error value nameEq keyEq selected trace) ->
  ((nextMinimum : Nat) -> CanonicalWorklistInspection name key world error value nameEq keyEq trace remaining nextMinimum) ->
  CanonicalWorklistInspection name key world error value nameEq keyEq trace (selected :: remaining) minimumStart
canonicalWorkContinueCompleted name key world error value nameEq keyEq trace selected remaining minimumStart completed later =
  case isLTE minimumStart (workRangeStart completed) of
    Yes startsAfter => CanonicalWorklistReady completed startsAfter (later (workRangeStart completed + workRangeSize completed))
    No startsTooEarly => CanonicalWorklistNeedsOrdering completed startsTooEarly

0 canonicalWorkContinueInspection :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> (selected : name) ->
  (remaining : List name) -> (minimumStart : Nat) ->
  (episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
  CanonicalWorkOpenInspection name key world error value nameEq keyEq selected trace episode ->
  ((nextMinimum : Nat) -> CanonicalWorklistInspection name key world error value nameEq keyEq trace remaining nextMinimum) ->
  CanonicalWorklistInspection name key world error value nameEq keyEq trace (selected :: remaining) minimumStart
canonicalWorkContinueInspection name key world error value nameEq keyEq trace selected remaining minimumStart episode
  (CanonicalWorkOpenReady scanned noLater) later =
    canonicalWorkContinueCompleted name key world error value nameEq keyEq trace selected remaining minimumStart
      (canonicalWorkCompleteBlock name key world error value nameEq keyEq selected trace episode scanned noLater) later
canonicalWorkContinueInspection name key world error value nameEq keyEq trace selected remaining minimumStart episode
  (CanonicalWorkOpenInterleaved scanned laterRemains) later =
    CanonicalWorklistNeedsGrouping episode scanned laterRemains

||| The pending-name argument decreases structurally at every accepted block;
||| each episode's body scan decreases structurally too. No arbitrary fuel or
||| identity-as-complete-sort branch hides a failed grouping/order test.
0 canonicalWorkInspectNames :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> (pending : List name) ->
  ((selected : name) -> Elem selected pending -> LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
  (minimumStart : Nat) -> CanonicalWorklistInspection name key world error value nameEq keyEq trace pending minimumStart
canonicalWorkInspectNames name key world error value nameEq keyEq trace [] episodes minimumStart = CanonicalWorklistEnd
canonicalWorkInspectNames name key world error value nameEq keyEq trace (selected :: remaining) episodes minimumStart =
  canonicalWorkContinueInspection name key world error value nameEq keyEq trace selected remaining minimumStart
    (episodes selected Here)
    (canonicalWorkInspectOpenEpisode name key world error value nameEq keyEq selected trace (episodes selected Here))
    (\nextMinimum => canonicalWorkInspectNames name key world error value nameEq keyEq trace remaining
      (\actor, present => episodes actor (There present)) nextMinimum)

||| Transport the new premise through the ACTUAL sealed all-action origin of
||| one adjacent result, using authenticated count injectivity, not raw casts.
0 uniqueInsertionsAfterAdjacentResult :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) -> (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq original prefixTrace left right suffix diamond) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  UniqueRawNameInsertions name key world error value nameEq keyEq (swappedTrace result)
uniqueInsertionsAfterAdjacentResult name key world error value protocol nameEq keyEq original prefixTrace left right suffix diamond result unique =
  MkUniqueRawNameInsertions
    (\actor, leftParent, rightParent, leftComponent, rightComponent, leftBirth, rightBirth =>
      uniqueAdjacentOrdinalInjective (transitionCount prefixTrace)
        (locatedActionOrdinal leftBirth) (locatedActionOrdinal rightBirth)
        (locatedActionOrdinal (replayActionOrigin (operationalOccurrenceCorrespondence (swappedOccurrenceFold result)) leftBirth))
        (locatedActionOrdinal (replayActionOrigin (operationalOccurrenceCorrespondence (swappedOccurrenceFold result)) rightBirth))
        (operationalOrdinalRelation (swappedOccurrenceFold result) leftBirth)
        (operationalOrdinalRelation (swappedOccurrenceFold result) rightBirth)
        (uniqueInsertionPosition unique actor leftParent rightParent leftComponent rightComponent
          (replayActionOrigin (operationalOccurrenceCorrespondence (swappedOccurrenceFold result)) leftBirth)
          (replayActionOrigin (operationalOccurrenceCorrespondence (swappedOccurrenceFold result)) rightBirth)))

||| The whole global premise survives the actual finite operational derivation;
||| a reached worklist never needs a second caller-supplied uniqueness witness.
export
0 uniqueInsertionsAfterFiniteDerivation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  UniqueRawNameInsertions name key world error value nameEq keyEq target
uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq FiniteAdjacentSwapDone unique = unique
uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq
  (FiniteAdjacentSwapStep trace prefixTrace left right suffix orientation diamond result target rest) unique =
    uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq rest
      (uniqueInsertionsAfterAdjacentResult name key world error value protocol nameEq keyEq trace prefixTrace left right suffix diamond result unique)

||| One reached worklist ties the pending-order inspection, actual block ranges,
||| current bundle and finite derivation to the SAME current trace. Inspection
||| may still be blocked; this record is deliberately not SortedClosingFreeTrace.
record CanonicalSortingWorklist
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error) (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq originalFinal) where
  constructor MkCanonicalSortingWorklist
  workReachedReplay : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original
  0 workReachedUnique : UniqueRawNameInsertions name key world error value nameEq keyEq (sortingCurrentTrace workReachedReplay)
  0 workReachedShape : ClosingFreeTraceShape name key world error value nameEq keyEq (sortingCurrentTrace workReachedReplay)
  0 workReachedFixedOrder : LinearizesSupport name key world error value nameEq keyEq (sortingCurrentFinal workReachedReplay) (orderedSupportNames ordering)
  0 workReachedInspection : CanonicalWorklistInspection name key world error value nameEq keyEq
    (sortingCurrentTrace workReachedReplay) (orderedSupportNames ordering) Z

0 canonicalWorkFixedCurrentOrder :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq originalFinal) ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  LinearizesSupport name key world error value nameEq keyEq (sortingCurrentFinal current) (orderedSupportNames ordering)
canonicalWorkFixedCurrentOrder name key world error value protocol nameEq keyEq {originalFinal} original premises ordering current =
  canonicalSortingFixedLinearization name key world error value protocol nameEq keyEq originalFinal (sortingCurrentFinal current)
    (replayProtocolRanked premises) (replayProtocolRanked (sortingCurrentPremises current))
    (replaySupportMatchesActive premises) (replaySupportMatchesActive (sortingCurrentPremises current))
    (replayedControls (sortingCurrentEndpoint current)) (orderedSupportNames ordering) (orderedSupportLinearization ordering)

||| The next inspection derives reached uniqueness and the SAME desired order
||| from source capital and the actual finite replay. Only reached closing-free
||| shape remains a separate input for a future operational progress producer.
0 canonicalWorkInspectReached :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq originalFinal) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (current : CanonicalSortingReplayState name key world error value protocol nameEq keyEq original) ->
  ClosingFreeTraceShape name key world error value nameEq keyEq (sortingCurrentTrace current) ->
  CanonicalSortingWorklist name key world error value protocol nameEq keyEq original ordering
canonicalWorkInspectReached name key world error value protocol nameEq keyEq original premises ordering unique current shape =
  MkCanonicalSortingWorklist current
    (uniqueInsertionsAfterFiniteDerivation name key world error value protocol nameEq keyEq (sortingReplayDerivation current) unique)
    shape (canonicalWorkFixedCurrentOrder name key world error value protocol nameEq keyEq original premises ordering current)
    (canonicalWorkInspectNames name key world error value nameEq keyEq (sortingCurrentTrace current) (orderedSupportNames ordering)
      (\selected, present => supportedOpenEpisode shape selected
        (orderSound (canonicalWorkFixedCurrentOrder name key world error value protocol nameEq keyEq original premises ordering current) selected present)) Z)

||| Build the actual initial block/range/derivation worklist from precisely the
||| REVISED O17 inputs. Identity is only its initial reached trace, never an
||| assertion that a blocked input has already become canonically sorted.
0 canonicalWorkStart :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  CanonicalSortingWorklist name key world error value protocol nameEq keyEq trace ordering
canonicalWorkStart name key world error value nameEq keyEq protocol {initial} {finalState} trace premises shape ordering unique =
  canonicalWorkInspectReached name key world error value protocol nameEq keyEq trace premises ordering unique
    (canonicalSortingReplayStart name key world error value protocol nameEq keyEq initial finalState trace premises) shape

||| Every accepted pair of half-open worklist ranges is position-disjoint.
||| Only scalar counts cross the independently existential block states.
0 canonicalWorkRangePositionsApart :
  (start, size, nextStart, earlierPosition, laterPosition : Nat) ->
  LTE (S earlierPosition) size -> LTE (start + size) nextStart ->
  Not (start + earlierPosition = nextStart + laterPosition)
canonicalWorkRangePositionsApart start size nextStart earlierPosition laterPosition bounded separated same =
  LTImpliesNotGTE
    (canonicalRankLTETransitive
      (replace {p = \position => LTE position (start + size)}
        (sym (plusSuccRightSucc start earlierPosition))
        (plusLteMonotoneLeft start (S earlierPosition) size bounded)) separated)
    (replace {p = LTE nextStart} (sym same) (lteAddRight {m = laterPosition} nextStart))

||| Regression view of the actual single-block producer. R173 external
||| normalization is deliberately GATED on the remaining private value stack;
||| public wrapper visibility alone does not promise external reduction.
||| Nothing means grouping remains; Just is an authenticated (start,size), NOT
||| a complete canonical schedule or an input-placement certificate.
public export
0 canonicalWorkOpenBlockRange :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (episode : LocatedInterleavedOpenEpisode name key world error value nameEq keyEq selected trace) ->
  Maybe (Nat, Nat)
canonicalWorkOpenBlockRange name key world error value nameEq keyEq selected trace episode =
  case canonicalWorkInspectOpenEpisode name key world error value nameEq keyEq selected trace episode of
    CanonicalWorkOpenReady scanned noLater =>
      Just (workRangeStart (canonicalWorkCompleteBlock name key world error value nameEq keyEq selected trace episode scanned noLater),
        workRangeSize (canonicalWorkCompleteBlock name key world error value nameEq keyEq selected trace episode scanned noLater))
    CanonicalWorkOpenInterleaved scanned laterRemains => Nothing

||| Internal-only structural reduction evidence. This is not the removed C34
||| external whole-block normalization assertion: it inspects one actual
||| checked Begin step and distinguishes its actor from a foreign actor.
0 canonicalWorkInternalSingleStepReduction :
  (key, world, error : Type) -> (value : key -> Type) -> (keyEq : DecEq key) ->
  (before, afterState : SystemState Nat key value world error) ->
  (checked : checkedApplyAction @{the (DecEq Nat) %search} @{keyEq} (LBegin 0) before = Just (LBeginTag, afterState)) ->
  (transitionCount (workActorPrefix (canonicalWorkScanActorPrefix Nat key world error value %search 0 {first = before} {finalState = afterState}
    (MoreTransitions (Fired {before} {afterState} %search keyEq (LBegin 0) LBeginTag checked) NoTransitions))) = 1,
   transitionCount (workActorPrefix (canonicalWorkScanActorPrefix Nat key world error value %search 1 {first = before} {finalState = afterState}
    (MoreTransitions (Fired {before} {afterState} %search keyEq (LBegin 0) LBeginTag checked) NoTransitions))) = 0)
canonicalWorkInternalSingleStepReduction key world error value keyEq before afterState checked = (Refl, Refl)

||| The grouping cursor must skip neither an owned lifecycle action nor a
||| registration yielded by this actor. NoLifecycleBy alone would be too weak.
data CanonicalWorkForeignSpan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (selected : name) -> Transitions first finalState -> Type where
  CanonicalWorkForeignEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {state : SystemState name key value world error} -> {selected : name} ->
    CanonicalWorkForeignSpan selected (NoTransitions {state})
  CanonicalWorkForeignStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, middle, finalState : SystemState name key value world error} ->
    {selected : name} -> (step : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    (0 excluded : Not (CanonicalWorkActorStep selected step)) ->
    CanonicalWorkForeignSpan selected rest ->
    CanonicalWorkForeignSpan selected (MoreTransitions step rest)

||| Exact first owned action beyond a foreign span, with all reached state
||| indices and decomposition retained together by the search producer.
record CanonicalWorkNextActor
  (name, key, world, error : Type) (value : key -> Type) (selected : name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkCanonicalWorkNextActor
  workNextBefore : SystemState name key value world error
  workNextAfter : SystemState name key value world error
  workBeforeNext : Transitions first workNextBefore
  workNextStep : Transition workNextBefore workNextAfter
  workAfterNext : Transitions workNextAfter finalState
  0 workNextOwned : CanonicalWorkActorStep selected workNextStep
  0 workBeforeNextForeign : CanonicalWorkForeignSpan selected workBeforeNext
  0 workNextDecomposition : appendTransitions workBeforeNext (MoreTransitions workNextStep workAfterNext) = trace

0 canonicalWorkNextActorPrepend :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  Not (CanonicalWorkActorStep selected step) ->
  CanonicalWorkNextActor name key world error value selected rest ->
  CanonicalWorkNextActor name key world error value selected (MoreTransitions step rest)
canonicalWorkNextActorPrepend name key world error value selected step rest excluded next =
  MkCanonicalWorkNextActor (workNextBefore next) (workNextAfter next)
    (MoreTransitions step (workBeforeNext next)) (workNextStep next) (workAfterNext next)
    (workNextOwned next)
    (CanonicalWorkForeignStep step (workBeforeNext next) excluded (workBeforeNextForeign next))
    (cong (MoreTransitions step) (workNextDecomposition next))

||| Genuine decreasing selection from the worklist's grouping debt. Stop at
||| the FIRST owned action, including yielded registrations (not merely the
||| next lifecycle step); every skipped action is certified foreign.
0 canonicalWorkFindNextActor :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  Not (NoLifecycleBy selected trace) ->
  CanonicalWorkNextActor name key world error value selected trace
canonicalWorkFindNextActor name key world error value nameEq selected NoTransitions remains =
  void (remains NoLifecycleByEnd)
canonicalWorkFindNextActor name key world error value nameEq selected (MoreTransitions step rest) remains =
  case canonicalWorkClassifyActor name key world error value nameEq selected step of
    Yes owned => MkCanonicalWorkNextActor _ _ NoTransitions step rest owned CanonicalWorkForeignEnd Refl
    No foreign => canonicalWorkNextActorPrepend name key world error value selected step rest foreign
      (canonicalWorkFindNextActor name key world error value nameEq selected rest
        (\noTail => remains (NoLifecycleByStep step rest
          (\lifecycle, same => foreign (CanonicalWorkLifecycle lifecycle same)) noTail)))

||| The stronger foreign-action span entails its lifecycle-only projection.
0 canonicalWorkForeignNoLifecycle :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  CanonicalWorkForeignSpan selected trace -> NoLifecycleBy selected trace
canonicalWorkForeignNoLifecycle name key world error value selected CanonicalWorkForeignEnd = NoLifecycleByEnd
canonicalWorkForeignNoLifecycle name key world error value selected (CanonicalWorkForeignStep step rest excluded tail) =
  NoLifecycleByStep step rest (\lifecycle, same => excluded (CanonicalWorkLifecycle lifecycle same))
    (canonicalWorkForeignNoLifecycle name key world error value selected tail)

||| The actual grouping boundary forces a NONEMPTY foreign prefix before the
||| selected next owned action. This gives a genuine positive distance to move.
0 canonicalWorkNextAfterAlien :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (alien : Transition first middle) -> (rest : Transitions middle finalState) ->
  Not (CanonicalWorkActorStep selected alien) ->
  Not (NoLifecycleBy selected (MoreTransitions alien rest)) ->
  (next : CanonicalWorkNextActor name key world error value selected (MoreTransitions alien rest) **
    LT Z (transitionCount (workBeforeNext next)))
canonicalWorkNextAfterAlien name key world error value nameEq selected alien rest foreign remains =
  (canonicalWorkNextActorPrepend name key world error value selected alien rest foreign
    (canonicalWorkFindNextActor name key world error value nameEq selected rest
      (\noTail => remains (NoLifecycleByStep alien rest
        (\lifecycle, same => foreign (CanonicalWorkLifecycle lifecycle same)) noTail))) **
    LTESucc LTEZero)

||| The last foreign action of a nonempty span, with source split and count
||| correlation created simultaneously rather than recovered across states.
record CanonicalWorkForeignSnoc
  (name, key, world, error : Type) (value : key -> Type) (selected : name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkCanonicalWorkForeignSnoc
  workSnocBefore : SystemState name key value world error
  workSnocPrefix : Transitions first workSnocBefore
  workSnocLast : Transition workSnocBefore finalState
  0 workSnocPrefixForeign : CanonicalWorkForeignSpan selected workSnocPrefix
  0 workSnocLastForeign : Not (CanonicalWorkActorStep selected workSnocLast)
  0 workSnocDecomposition : appendTransitions workSnocPrefix (MoreTransitions workSnocLast NoTransitions) = trace
  0 workSnocCount : transitionCount trace = S (transitionCount workSnocPrefix)

||| Decreasing structural producer of the foreign action immediately before a
||| selected next action. It returns the exact last action, not a raw-name guess.
0 canonicalWorkSplitForeignLast :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (head : Transition first middle) -> (rest : Transitions middle finalState) ->
  CanonicalWorkForeignSpan selected (MoreTransitions head rest) ->
  CanonicalWorkForeignSnoc name key world error value selected (MoreTransitions head rest)
canonicalWorkSplitForeignLast name key world error value selected head NoTransitions
  (CanonicalWorkForeignStep _ _ excluded tail) =
    MkCanonicalWorkForeignSnoc _ NoTransitions head CanonicalWorkForeignEnd excluded Refl Refl
canonicalWorkSplitForeignLast name key world error value selected head (MoreTransitions next rest)
  (CanonicalWorkForeignStep _ _ excluded tail) =
    case canonicalWorkSplitForeignLast name key world error value selected next rest tail of
      MkCanonicalWorkForeignSnoc lastBefore earlier last earlierForeign lastForeign decomposition count =>
        MkCanonicalWorkForeignSnoc lastBefore (MoreTransitions head earlier) last
          (CanonicalWorkForeignStep head earlier excluded earlierForeign) lastForeign
          (cong (MoreTransitions head) decomposition) (cong S count)

0 canonicalWorkSnocBeforeNext :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (next : CanonicalWorkNextActor name key world error value selected trace) ->
  LT Z (transitionCount (workBeforeNext next)) ->
  CanonicalWorkForeignSnoc name key world error value selected (workBeforeNext next)
canonicalWorkSnocBeforeNext name key world error value selected
  (MkCanonicalWorkNextActor _ _ NoTransitions step suffix owned foreign decomposition) positive =
    void (succNotLTEzero positive)
canonicalWorkSnocBeforeNext name key world error value selected
  (MkCanonicalWorkNextActor _ _ (MoreTransitions head rest) step suffix owned foreign decomposition) positive =
    canonicalWorkSplitForeignLast name key world error value selected head rest foreign

||| A produced ADJACENT source pair at the grouping frontier. The left action
||| is foreign, the right action belongs to the selected block, and every state
||| and segment is actual. This is not yet a diamond/applicability certificate.
record CanonicalWorkGroupingPair
  (name, key, world, error : Type) (value : key -> Type) (selected : name)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkCanonicalWorkGroupingPair
  workPairFirst : SystemState name key value world error
  workPairMiddle : SystemState name key value world error
  workPairFinal : SystemState name key value world error
  workPairPrefix : Transitions first workPairFirst
  workPairLeft : Transition workPairFirst workPairMiddle
  workPairRight : Transition workPairMiddle workPairFinal
  workPairSuffix : Transitions workPairFinal finalState
  0 workPairLeftForeign : Not (CanonicalWorkActorStep selected workPairLeft)
  0 workPairRightOwned : CanonicalWorkActorStep selected workPairRight
  0 workPairDecomposition : appendTransitions workPairPrefix
    (MoreTransitions workPairLeft (MoreTransitions workPairRight workPairSuffix)) = trace

0 canonicalWorkGroupingPairFromSnoc :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (next : CanonicalWorkNextActor name key world error value selected trace) ->
  CanonicalWorkForeignSnoc name key world error value selected (workBeforeNext next) ->
  CanonicalWorkGroupingPair name key world error value selected trace
canonicalWorkGroupingPairFromSnoc name key world error value selected trace next split =
  MkCanonicalWorkGroupingPair (workSnocBefore split) (workNextBefore next) (workNextAfter next)
    (workSnocPrefix split) (workSnocLast split) (workNextStep next) (workAfterNext next)
    (workSnocLastForeign split) (workNextOwned next)
    (trans (sym (appendTransitionsAssociative (workSnocPrefix split)
      (MoreTransitions (workSnocLast split) NoTransitions) (MoreTransitions (workNextStep next) (workAfterNext next))))
      (trans (cong (\earlier => appendTransitions earlier (MoreTransitions (workNextStep next) (workAfterNext next)))
        (workSnocDecomposition split)) (workNextDecomposition next)))

0 canonicalWorkGroupingPairFromNext :
  (name, key, world, error : Type) -> (value : key -> Type) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (next : CanonicalWorkNextActor name key world error value selected trace) ->
  LT Z (transitionCount (workBeforeNext next)) ->
  CanonicalWorkGroupingPair name key world error value selected trace
canonicalWorkGroupingPairFromNext name key world error value selected trace next positive =
  canonicalWorkGroupingPairFromSnoc name key world error value selected trace next
    (canonicalWorkSnocBeforeNext name key world error value selected next positive)

||| Close the structural selection obligation of an actual grouping stop.
||| No adjacency, selected action, target trace or diamond is supplied.
0 canonicalWorkGroupingFromBoundary :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> CanonicalWorkActorBoundary selected trace ->
  Not (NoLifecycleBy selected trace) -> CanonicalWorkGroupingPair name key world error value selected trace
canonicalWorkGroupingFromBoundary name key world error value nameEq selected _ CanonicalWorkBoundaryEnd remains =
  void (remains NoLifecycleByEnd)
canonicalWorkGroupingFromBoundary name key world error value nameEq selected _
  (CanonicalWorkBoundaryBlocked alien rest foreign) remains =
    case canonicalWorkNextAfterAlien name key world error value nameEq selected alien rest foreign remains of
      (next ** positive) => canonicalWorkGroupingPairFromNext name key world error value selected
        (MoreTransitions alien rest) next positive

||| Bubble actor blocks by repeated `AdjacentSwapResult`s.  The output itself is
||| the sorting-specific recursive transport package, rather than only final
||| schedule-shaped data.
public export
0 sortClosingFreeTraceSpike :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    finalState) ->
  (0 uniqueInsertions : UniqueRawNameInsertions name key world error value
    nameEq keyEq trace) ->
  SortedClosingFreeTrace name key world error value protocol nameEq keyEq trace
    ordering
sortClosingFreeTraceSpike = ?sortClosingFreeTraceSpike_rhs

||| A retired endpoint entry cannot occur in the executable least support set.
||| The fixed-point equation exposes retirement before any parent/provider test.
0 canonicalRetiredFiberUnsupported :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  retired fiber = True ->
  isSupported @{nameEq} @{keyEq} selected state = False
canonicalRetiredFiberUnsupported nameEq keyEq selected state
  (MkFiber component parent True table lifecycle) found Refl =
    trans (supportSetIsSolution nameEq keyEq state selected)
      (rewrite found in Refl)

||| A missing endpoint entry is likewise absent from the support closure.
0 canonicalAbsentFiberUnsupported :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected (registry state) = Nothing ->
  isSupported @{nameEq} @{keyEq} selected state = False
canonicalAbsentFiberUnsupported nameEq keyEq selected state absent =
  trans (supportSetIsSolution nameEq keyEq state selected)
    (rewrite absent in Refl)

||| Every endpoint-withdrawn name was already outside original support.
0 canonicalWithdrawnOriginalUnsupported :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (originalFinal, reducedFinal : SystemState name key value world error) ->
  WithdrawnNameResult nameEq selected originalFinal reducedFinal ->
  isSupported @{nameEq} @{keyEq} selected originalFinal = False
canonicalWithdrawnOriginalUnsupported nameEq keyEq selected originalFinal
  reducedFinal
  (VestigialNameWithdrawn fiber found retiredProof notInstalled emptyTable
    absent) =
      canonicalRetiredFiberUnsupported nameEq keyEq selected originalFinal fiber
        found retiredProof
canonicalWithdrawnOriginalUnsupported nameEq keyEq selected originalFinal
  reducedFinal (NameAlreadyAbsent originalAbsent reducedAbsent) =
    canonicalAbsentFiberUnsupported nameEq keyEq selected originalFinal
      originalAbsent

||| Endpoint withdrawal always removes the raw name from the reduced registry.
0 canonicalWithdrawnReducedUnsupported :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (originalFinal, reducedFinal : SystemState name key value world error) ->
  WithdrawnNameResult nameEq selected originalFinal reducedFinal ->
  isSupported @{nameEq} @{keyEq} selected reducedFinal = False
canonicalWithdrawnReducedUnsupported nameEq keyEq selected originalFinal
  reducedFinal
  (VestigialNameWithdrawn fiber found retiredProof notInstalled emptyTable
    absent) =
      canonicalAbsentFiberUnsupported nameEq keyEq selected reducedFinal absent
canonicalWithdrawnReducedUnsupported nameEq keyEq selected originalFinal
  reducedFinal (NameAlreadyAbsent originalAbsent reducedAbsent) =
    canonicalAbsentFiberUnsupported nameEq keyEq selected reducedFinal
      reducedAbsent

||| Boolean equality from the two positive directions used by a pair of
||| linearizations over the same order.
0 canonicalBoolSameFromTrueMaps :
  (left, right : Bool) ->
  (left = True -> right = True) ->
  (right = True -> left = True) ->
  left = right
canonicalBoolSameFromTrueMaps False False forward backward = Refl
canonicalBoolSameFromTrueMaps False True forward backward =
  case backward Refl of Refl impossible
canonicalBoolSameFromTrueMaps True False forward backward =
  case forward Refl of Refl impossible
canonicalBoolSameFromTrueMaps True True forward backward = Refl

0 canonicalSharedOrderSupportForward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  {order : List name} ->
  LinearizesSupport name key world error value nameEq keyEq originalFinal order ->
  LinearizesSupport name key world error value nameEq keyEq reducedFinal order ->
  (selected : name) ->
  isSupported @{nameEq} @{keyEq} selected originalFinal = True ->
  isSupported @{nameEq} @{keyEq} selected reducedFinal = True
canonicalSharedOrderSupportForward originalLinearization reducedLinearization
  selected supported =
    orderSound reducedLinearization selected
      (orderComplete originalLinearization selected supported)

0 canonicalSharedOrderSupportBackward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  {order : List name} ->
  LinearizesSupport name key world error value nameEq keyEq originalFinal order ->
  LinearizesSupport name key world error value nameEq keyEq reducedFinal order ->
  (selected : name) ->
  isSupported @{nameEq} @{keyEq} selected reducedFinal = True ->
  isSupported @{nameEq} @{keyEq} selected originalFinal = True
canonicalSharedOrderSupportBackward originalLinearization reducedLinearization
  selected supported =
    orderSound originalLinearization selected
      (orderComplete reducedLinearization selected supported)

0 canonicalSharedOrderSupportSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  {order : List name} ->
  LinearizesSupport name key world error value nameEq keyEq originalFinal order ->
  LinearizesSupport name key world error value nameEq keyEq reducedFinal order ->
  (selected : name) ->
  isSupported @{nameEq} @{keyEq} selected originalFinal =
    isSupported @{nameEq} @{keyEq} selected reducedFinal
canonicalSharedOrderSupportSame {nameEq} {keyEq} {originalFinal} {reducedFinal}
  originalLinearization reducedLinearization selected =
    canonicalBoolSameFromTrueMaps
      (isSupported @{nameEq} @{keyEq} selected originalFinal)
      (isSupported @{nameEq} @{keyEq} selected reducedFinal)
      (canonicalSharedOrderSupportForward originalLinearization
        reducedLinearization selected)
      (canonicalSharedOrderSupportBackward originalLinearization
        reducedLinearization selected)

||| A support truth excludes membership in any list whose members are known
||| unsupported at that same endpoint.
0 canonicalSupportedNotElem :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {state : SystemState name key value world error} -> {withdrawn : List name} ->
  ((member : Elem selected withdrawn) ->
    isSupported @{nameEq} @{keyEq} selected state = False) ->
  isSupported @{nameEq} @{keyEq} selected state = True ->
  Not (Elem selected withdrawn)
canonicalSupportedNotElem unsupported supported member =
  canonicalFalseNotTrue (trans (sym (unsupported member)) supported)

0 canonicalOrderedNameOutsideWithdrawals :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  {order : List name} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  (originalLinearization : LinearizesSupport name key world error value nameEq
    keyEq originalFinal order) ->
  Elem selected order ->
  Not (Elem selected (endpointWithdrawnNames endpoint))
canonicalOrderedNameOutsideWithdrawals {nameEq} {keyEq} {selected}
  {originalFinal} {reducedFinal} endpoint originalLinearization selectedIn =
    canonicalSupportedNotElem
      (canonicalWithdrawnOriginalUnsupported nameEq keyEq selected originalFinal
        reducedFinal . endpointNamesWithdrawn endpoint selected)
      (orderSound originalLinearization selected selectedIn)

||| Producer-owned exact target lookup used to keep a transported edge's fiber,
||| lookup equation, and control proof correlated without repeated elimination.
record CanonicalOutsideFiberForward
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  (originalFinal, reducedFinal : SystemState name key value world error)
  (fiber : Fiber name key value world error) where
  constructor MkCanonicalOutsideFiberForward
  forwardTargetFiber : Fiber name key value world error
  0 forwardTargetFound : lookupFiber @{nameEq} selected
    (registry reducedFinal) = Just forwardTargetFiber
  0 forwardTargetControls : FiberControlRelated fiber forwardTargetFiber

||| Outside the withdrawal list, endpoint control equivalence produces the
||| exact matching target fiber and its static-control relation.
0 canonicalOutsideFiberForward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  Not (Elem selected (endpointWithdrawnNames endpoint)) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry originalFinal) = Just fiber ->
  CanonicalOutsideFiberForward name key world error value nameEq selected
    originalFinal reducedFinal fiber
canonicalOutsideFiberForward {nameEq} {selected} {originalFinal} {reducedFinal}
  endpoint outside fiber found =
    case foreignControlLookupFound nameEq selected (registry originalFinal)
      (registry reducedFinal) fiber found
      (endpointControlsOutside endpoint selected outside) of
      MkForeignRelatedFiberFound targetFiber targetFound controls =>
        MkCanonicalOutsideFiberForward targetFiber targetFound controls

||| The same exact lookup package is available from the reduced endpoint back
||| to the original endpoint by symmetry of the pointwise control relation.
0 canonicalOutsideFiberBackward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  Not (Elem selected (endpointWithdrawnNames endpoint)) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry reducedFinal) = Just fiber ->
  (sourceFiber : Fiber name key value world error **
   (lookupFiber @{nameEq} selected (registry originalFinal) = Just sourceFiber,
    FiberControlRelated sourceFiber fiber))
canonicalOutsideFiberBackward {nameEq} {selected} {originalFinal} {reducedFinal}
  endpoint outside fiber found =
    case foreignControlLookupFound nameEq selected (registry reducedFinal)
      (registry originalFinal) fiber found
      (fiberControlMaybeSymmetric
        (endpointControlsOutside endpoint selected outside)) of
      MkForeignRelatedFiberFound sourceFiber sourceFound controls =>
        (sourceFiber ** (sourceFound, fiberControlSymmetric controls))

||| Control-related fibers retain the exact static component.
0 canonicalFiberComponentSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Fiber name key value world error} ->
  FiberControlRelated left right -> fiberComponent left = fiberComponent right
canonicalFiberComponentSame
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) = Refl

||| Control-related fibers retain their exact registration parent.
0 canonicalFiberParentSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, right : Fiber name key value world error} ->
  (controls : FiberControlRelated left right) ->
  fiberParent left = fiberParent right
canonicalFiberParentSame
  (FibersControlRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable leftLifecycle rightLifecycle parentSame retiredSame
    lifecycleSame) = parentSame

||| Apply reduced input placement to the exact forward fiber package.
0 canonicalChildPlacementFromForward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  {order : List name} ->
  {initial, canonicalFinal : SystemState name key value world error} ->
  {canonical : Transitions initial canonicalFinal} ->
  (placement : CanonicalInputPlacement name key world error value nameEq keyEq
    reducedFinal order canonical) ->
  (selected, parent : name) ->
  (selectedIn : Elem selected order) ->
  (fiber : Fiber name key value world error) ->
  (forward : CanonicalOutsideFiberForward name key world error value nameEq
    selected originalFinal reducedFinal fiber) ->
  fiberParent fiber = ChildOf parent ->
  (component : Component key value world error **
   birth : LocatedGeneratedRegistration selected parent component canonical **
   (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} selected
      (registry (registrationBefore birth)) = Nothing,
    (action : Action name key value world error) ->
    (lifecycle : LocatedActionOccurrence action canonical) ->
    isLifecycleAction action = True -> actionOwner action = selected ->
    LT (registrationOrdinal birth) (locatedActionOrdinal lifecycle)))
canonicalChildPlacementFromForward placement selected parent selectedIn fiber
  forward childParent =
    childGenerationBeforeOwnLifecycle placement selected parent selectedIn
      (forwardTargetFiber forward) (forwardTargetFound forward)
      (trans (sym (canonicalFiberParentSame
        (forwardTargetControls forward))) childParent)

||| Forward the original endpoint child lookup once the chosen-order support
||| proof excludes its name from the withdrawal set.
0 canonicalChildPlacementToOriginal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  {order : List name} ->
  {initial, canonicalFinal : SystemState name key value world error} ->
  {canonical : Transitions initial canonicalFinal} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  (originalLinearization : LinearizesSupport name key world error value nameEq
    keyEq originalFinal order) ->
  (placement : CanonicalInputPlacement name key world error value nameEq keyEq
    reducedFinal order canonical) ->
  (selected, parent : name) ->
  (selectedIn : Elem selected order) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry originalFinal) = Just fiber ->
  fiberParent fiber = ChildOf parent ->
  (component : Component key value world error **
   birth : LocatedGeneratedRegistration selected parent component canonical **
   (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} selected
      (registry (registrationBefore birth)) = Nothing,
    (action : Action name key value world error) ->
    (lifecycle : LocatedActionOccurrence action canonical) ->
    isLifecycleAction action = True -> actionOwner action = selected ->
    LT (registrationOrdinal birth) (locatedActionOrdinal lifecycle)))
canonicalChildPlacementToOriginal endpoint originalLinearization placement
  selected parent selectedIn fiber found childParent =
    canonicalChildPlacementFromForward placement selected parent selectedIn fiber
      (canonicalOutsideFiberForward endpoint
        (canonicalOrderedNameOutsideWithdrawals endpoint originalLinearization
          selectedIn) fiber found)
      childParent

0 canonicalInputPlacementToOriginal :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  {order : List name} ->
  {initial, canonicalFinal : SystemState name key value world error} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  (originalLinearization : LinearizesSupport name key world error value nameEq
    keyEq originalFinal order) ->
  (canonical : Transitions initial canonicalFinal) ->
  CanonicalInputPlacement name key world error value nameEq keyEq reducedFinal
    order canonical ->
  CanonicalInputPlacement name key world error value nameEq keyEq originalFinal
    order canonical
canonicalInputPlacementToOriginal endpoint originalLinearization canonical
  placement =
    MkCanonicalInputPlacement (allRootInputsFirst placement)
      (rootGenerationFresh placement)
      (rootGenerationBeforeLifecycle placement)
      (canonicalChildPlacementToOriginal endpoint originalLinearization placement)

||| Rebuild one precedence edge from two producer-owned exact target lookups.
0 canonicalPrecedenceEdgeForwardFromFibers :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {lower, upper : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  (edge : PrecedenceEdge nameEq lower upper originalFinal) ->
  (lowerTarget : CanonicalOutsideFiberForward name key world error value nameEq
    lower originalFinal reducedFinal (providerFiber edge)) ->
  (upperTarget : CanonicalOutsideFiberForward name key world error value nameEq
    upper originalFinal reducedFinal (consumerFiber edge)) ->
  PrecedenceEdge nameEq lower upper reducedFinal
canonicalPrecedenceEdgeForwardFromFibers edge lowerTarget upperTarget =
  MkPrecedenceEdge (edgeKey edge) (forwardTargetFiber lowerTarget)
    (forwardTargetFiber upperTarget) (forwardTargetFound lowerTarget)
    (forwardTargetFound upperTarget)
    (replace
      {p = \component => Elem (edgeKey edge)
        (dependencies (componentProvisions component))}
      (canonicalFiberComponentSame (forwardTargetControls lowerTarget))
      (providerDeclares edge))
    (replace
      {p = \component => Elem (edgeKey edge)
        (dependencies (componentDependencies component))}
      (canonicalFiberComponentSame (forwardTargetControls upperTarget))
      (consumerDeclares edge))

||| Transport a precedence edge whose two endpoint actors are known outside the
||| raw withdrawal list.
0 canonicalPrecedenceEdgeForward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {lower, upper : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  Not (Elem lower (endpointWithdrawnNames endpoint)) ->
  Not (Elem upper (endpointWithdrawnNames endpoint)) ->
  PrecedenceEdge nameEq lower upper originalFinal ->
  PrecedenceEdge nameEq lower upper reducedFinal
canonicalPrecedenceEdgeForward endpoint lowerOutside upperOutside edge =
  canonicalPrecedenceEdgeForwardFromFibers edge
    (canonicalOutsideFiberForward endpoint lowerOutside (providerFiber edge)
      (providerFound edge))
    (canonicalOutsideFiberForward endpoint upperOutside (consumerFiber edge)
      (consumerFound edge))

||| Rebuild one parent edge from the child actor's exact target lookup.
0 canonicalParentEdgeForwardFromFiber :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {parent, child : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  (edge : ParentSupportEdge nameEq parent child originalFinal) ->
  (childTarget : CanonicalOutsideFiberForward name key world error value nameEq
    child originalFinal reducedFinal (childFiber edge)) ->
  ParentSupportEdge nameEq parent child reducedFinal
canonicalParentEdgeForwardFromFiber edge childTarget =
  MkParentSupportEdge (forwardTargetFiber childTarget)
    (forwardTargetFound childTarget)
    (trans (sym (canonicalFiberParentSame
      (forwardTargetControls childTarget))) (childParent edge))

||| Transport a parent edge when its child is outside the raw withdrawal list.
0 canonicalParentEdgeForward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {parent, child : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  Not (Elem child (endpointWithdrawnNames endpoint)) ->
  ParentSupportEdge nameEq parent child originalFinal ->
  ParentSupportEdge nameEq parent child reducedFinal
canonicalParentEdgeForward endpoint childOutside edge =
  canonicalParentEdgeForwardFromFiber edge
    (canonicalOutsideFiberForward endpoint childOutside (childFiber edge)
      (childFound edge))

||| Transport either half of Equation 62 between the endpoint registries.
0 canonicalSupportEdgeForward :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {lower, upper : name} ->
  {originalFinal, reducedFinal : SystemState name key value world error} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  Not (Elem lower (endpointWithdrawnNames endpoint)) ->
  Not (Elem upper (endpointWithdrawnNames endpoint)) ->
  SupportEdge nameEq originalFinal lower upper ->
  SupportEdge nameEq reducedFinal lower upper
canonicalSupportEdgeForward endpoint lowerOutside upperOutside
  (SupportPrecedence edge) =
    SupportPrecedence (canonicalPrecedenceEdgeForward endpoint lowerOutside
      upperOutside edge)
canonicalSupportEdgeForward endpoint lowerOutside upperOutside
  (SupportParent edge) =
    SupportParent (canonicalParentEdgeForward endpoint upperOutside edge)

||| Prove all support/parent/input-placement transport from the cumulative
||| endpoint relation and exact generated-registration accounting.
public export
0 canonicalSupportTransportSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, originalFinal, reducedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (reduced : Transitions initial reducedFinal) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal reducedFinal) ->
  CanonicalRegistrationCorrespondence original reduced
    (endpointWithdrawnGenerations endpoint) ->
  (order : List name) ->
  LinearizesSupport name key world error value nameEq keyEq reducedFinal order ->
  LinearizesSupport name key world error value nameEq keyEq originalFinal order ->
  CanonicalSupportTransport name key world error value nameEq keyEq originalFinal
    reducedFinal endpoint order
canonicalSupportTransportSpike nameEq keyEq original reduced endpoint tree order
  reducedLinearization originalLinearization =
    MkCanonicalSupportTransport
      (canonicalSharedOrderSupportSame originalLinearization
        reducedLinearization)
      originalLinearization
      (canonicalInputPlacementToOriginal endpoint originalLinearization)

||| Research-only authenticity companion for the immutable CP3 registration
||| tree.  It states exact occurrence equality, not merely equal birth ordinals:
||| the tree map must be the origin chosen by the deletion/sorting action replay.
||| Its indices make the proof unusable after replacing either the tree or the
||| occurrence correspondence.
public export
record AuthenticatedCanonicalRegistrationMap
  (name, key, world, error : Type) (value : key -> Type)
  {initial, originalFinal, canonicalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (canonical : Transitions initial canonicalFinal)
  (withdrawn : List (RegistrationGeneration name))
  (tree : CanonicalRegistrationCorrespondence original canonical withdrawn)
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) where
  constructor MkAuthenticatedCanonicalRegistrationMap
  0 canonicalOriginIsReplayOrigin :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component canonical) ->
    canonicalToOriginal tree occurrence =
      replayGeneratedRegistrationOrigin occurrences occurrence

||| The exact occurrence correspondence constructed by deletion followed by
||| sorting.  There is no caller-selected intermediate map at this boundary.
public export
0 deletionSortingOccurrenceCorrespondence :
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  {ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)} ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (sortedTrace sorted)
deletionSortingOccurrenceCorrespondence reduction sorted =
  composeActionRegistrationReplayCorrespondence
    (reductionOccurrenceCorrespondence reduction)
    (sortingOccurrenceCorrespondence sorted)

||| Ordinary CP3 registration-accounting laws stated directly over the exact
||| deletion/sorting occurrence fold.  They contain no strong-authentication
||| equality and no `OneTraceOrchestrationAccounting` value.
public export
record CanonicalReplayAccountingLaws
  (name, key, world, error : Type) (value : key -> Type)
  {initial, originalFinal, canonicalFinal :
    SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (canonical : Transitions initial canonicalFinal)
  (withdrawn : List (RegistrationGeneration name))
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) where
  constructor MkCanonicalReplayAccountingLaws
  replayOriginalRegistrationAccounted :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (occurrence : LocatedGeneratedRegistration child parent component original) ->
    Either (Elem (registrationGeneration occurrence) withdrawn)
      (canonicalOccurrence : LocatedGeneratedRegistration child parent component
        canonical **
       registrationGeneration
         (replayGeneratedRegistrationOrigin occurrences canonicalOccurrence) =
       registrationGeneration occurrence)
  0 replayCanonicalOccurrenceInjective :
    {child, parent : name} ->
    {component : Component key value world error} ->
    (leftOccurrence, rightOccurrence : LocatedGeneratedRegistration child parent
      component canonical) ->
    registrationGeneration (replayGeneratedRegistrationOrigin occurrences
      leftOccurrence) =
    registrationGeneration (replayGeneratedRegistrationOrigin occurrences
      rightOccurrence) ->
    registrationGeneration leftOccurrence = registrationGeneration rightOccurrence
  0 replayWithdrawnRegistrationRemoved :
    (generation : RegistrationGeneration name) -> Elem generation withdrawn ->
    (parent : name ** component : Component key value world error **
     occurrence : LocatedGeneratedRegistration (generationName generation)
       parent component original **
     (registrationGeneration occurrence = generation,
      (canonicalParent : name) ->
      (canonicalComponent : Component key value world error) ->
      (canonicalOccurrence : LocatedGeneratedRegistration
        (generationName generation) canonicalParent canonicalComponent canonical) ->
      registrationGeneration (replayGeneratedRegistrationOrigin occurrences
        canonicalOccurrence) = generation -> Void))

||| Construct the immutable CP3 tree by definition from the occurrence fold.
||| Consequently the strong authentication proof below is `Refl`.
public export
0 canonicalRegistrationTreeFromReplay :
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    canonical withdrawn occurrences) ->
  CanonicalRegistrationCorrespondence original canonical withdrawn
canonicalRegistrationTreeFromReplay occurrences laws =
  MkCanonicalRegistrationCorrespondence
    (replayGeneratedRegistrationOrigin occurrences)
    (replayOriginalRegistrationAccounted laws)
    (replayCanonicalOccurrenceInjective laws)
    (replayWithdrawnRegistrationRemoved laws)

public export
0 replayConstructedTreeAuthentication :
  (occurrences : ActionRegistrationReplayCorrespondence name key world error value
    original canonical) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    canonical withdrawn occurrences) ->
  AuthenticatedCanonicalRegistrationMap name key world error value original
    canonical withdrawn (canonicalRegistrationTreeFromReplay occurrences laws)
    occurrences
replayConstructedTreeAuthentication occurrences laws =
  MkAuthenticatedCanonicalRegistrationMap (\occurrence => Refl)

||| Full external/generated orchestration accounting through deletion followed
||| by sorting.  The registration map is authenticated against the exact
||| composed occurrence replay produced by those same indexed fold outputs.
public export
record OneTraceOrchestrationAccounting
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction))
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) where
  constructor MkOneTraceOrchestrationAccounting
  accountedEndpoint : CanonicalEndpointRelation name key world error value
    nameEq keyEq originalFinal (sortedFinal sorted)
  0 accountedWithdrawnExact : endpointWithdrawnGenerations accountedEndpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction)
  accountedExternalInputs : SameExternalOrchestration nameEq original
    (sortedTrace sorted)
  accountedGeneratedRegistrations : CanonicalRegistrationCorrespondence original
    (sortedTrace sorted) (endpointWithdrawnGenerations accountedEndpoint)
  accountedRegistrationAuthentication : AuthenticatedCanonicalRegistrationMap
    name key world error value original (sortedTrace sorted)
    (endpointWithdrawnGenerations accountedEndpoint)
    accountedGeneratedRegistrations
    (deletionSortingOccurrenceCorrespondence reduction sorted)

||| Checked strong-authentication producer from the raw fold and ordinary CP3
||| accounting laws.  This function does not assume the result accounting value.
public export
0 assembleOneTraceAccountingFromReplay :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal (sortedFinal sorted)) ->
  endpointWithdrawnGenerations endpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction) ->
  SameExternalOrchestration nameEq original (sortedTrace sorted) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    (sortedTrace sorted) (endpointWithdrawnGenerations endpoint)
    (deletionSortingOccurrenceCorrespondence reduction sorted)) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted
assembleOneTraceAccountingFromReplay reduction ordering sorted endpoint exact
  external laws =
    MkOneTraceOrchestrationAccounting endpoint exact external
      (canonicalRegistrationTreeFromReplay
        (deletionSortingOccurrenceCorrespondence reduction sorted) laws)
      (replayConstructedTreeAuthentication
        (deletionSortingOccurrenceCorrespondence reduction sorted) laws)

||| Abstract O16 assembler only.  It assumes the hard deletion reduction, sorting
||| derivation, two located births, singleton withdrawal, and every ordinary CP3
||| replay-accounting law.  It calibrates dependent packaging and Refl
||| authentication but is explicitly not a concrete nontrivial producer fixture.
public export
record AbstractTwoBirthOneWithdrawalAssembly
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original)
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction))
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) where
  constructor MkAbstractTwoBirthOneWithdrawalAssembly
  fixtureEndpoint : CanonicalEndpointRelation name key world error value nameEq
    keyEq originalFinal (sortedFinal sorted)
  fixtureWithdrawnGeneration : RegistrationGeneration name
  0 fixtureOneWithdrawal : endpointWithdrawnGenerations fixtureEndpoint =
    [fixtureWithdrawnGeneration]
  0 fixtureWithdrawalMatchesReduction :
    endpointWithdrawnGenerations fixtureEndpoint =
      endpointWithdrawnGenerations (cumulativeEndpoint reduction)
  fixtureExternalInputs : SameExternalOrchestration nameEq original
    (sortedTrace sorted)
  fixtureFirstChild : name
  fixtureFirstParent : name
  fixtureFirstComponent : Component key value world error
  fixtureFirstBirth : LocatedGeneratedRegistration fixtureFirstChild
    fixtureFirstParent fixtureFirstComponent (sortedTrace sorted)
  fixtureSecondChild : name
  fixtureSecondParent : name
  fixtureSecondComponent : Component key value world error
  fixtureSecondBirth : LocatedGeneratedRegistration fixtureSecondChild
    fixtureSecondParent fixtureSecondComponent (sortedTrace sorted)
  0 fixtureOriginalBirthsDistinct : Not
    (registrationGeneration (replayGeneratedRegistrationOrigin
      (deletionSortingOccurrenceCorrespondence reduction sorted)
      fixtureFirstBirth) =
     registrationGeneration (replayGeneratedRegistrationOrigin
      (deletionSortingOccurrenceCorrespondence reduction sorted)
      fixtureSecondBirth))
  fixtureReplayAccountingLaws : CanonicalReplayAccountingLaws name key world
    error value original (sortedTrace sorted)
    (endpointWithdrawnGenerations fixtureEndpoint)
    (deletionSortingOccurrenceCorrespondence reduction sorted)

||| Construct the abstract assembly record from its complete raw telescope.
||| Neither the assembly nor final accounting is accepted as input, but the hard
||| deletion/sorting and CP3 laws remain premises.
public export
0 assembleAbstractTwoBirthOneWithdrawalAssembly :
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original} ->
  {ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)} ->
  {sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering} ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal (sortedFinal sorted)) ->
  (withdrawn : RegistrationGeneration name) ->
  endpointWithdrawnGenerations endpoint = [withdrawn] ->
  endpointWithdrawnGenerations endpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction) ->
  (external : SameExternalOrchestration nameEq original (sortedTrace sorted)) ->
  (firstChild, firstParent : name) ->
  (firstComponent : Component key value world error) ->
  (firstBirth : LocatedGeneratedRegistration firstChild firstParent firstComponent
    (sortedTrace sorted)) ->
  (secondChild, secondParent : name) ->
  (secondComponent : Component key value world error) ->
  (secondBirth : LocatedGeneratedRegistration secondChild secondParent
    secondComponent (sortedTrace sorted)) ->
  Not (registrationGeneration (replayGeneratedRegistrationOrigin
    (deletionSortingOccurrenceCorrespondence reduction sorted) firstBirth) =
    registrationGeneration (replayGeneratedRegistrationOrigin
      (deletionSortingOccurrenceCorrespondence reduction sorted) secondBirth)) ->
  (laws : CanonicalReplayAccountingLaws name key world error value original
    (sortedTrace sorted) (endpointWithdrawnGenerations endpoint)
    (deletionSortingOccurrenceCorrespondence reduction sorted)) ->
  AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol nameEq keyEq
    original reduction ordering sorted
assembleAbstractTwoBirthOneWithdrawalAssembly endpoint withdrawn one exact external
  firstChild firstParent firstComponent firstBirth secondChild secondParent
  secondComponent secondBirth distinct laws =
    MkAbstractTwoBirthOneWithdrawalAssembly endpoint withdrawn one exact external
      firstChild firstParent firstComponent firstBirth secondChild secondParent
      secondComponent secondBirth distinct laws

public export
0 abstractTwoBirthOneWithdrawalAccounting :
  (fixture : AbstractTwoBirthOneWithdrawalAssembly name key world error value protocol
    nameEq keyEq original reduction ordering sorted) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted
abstractTwoBirthOneWithdrawalAccounting {reduction} {ordering} {sorted} fixture =
  assembleOneTraceAccountingFromReplay reduction ordering sorted
    (fixtureEndpoint fixture) (fixtureWithdrawalMatchesReduction fixture)
    (fixtureExternalInputs fixture) (fixtureReplayAccountingLaws fixture)

public export
0 deletionSortingOrchestrationAccountingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (endpoint : CanonicalEndpointRelation name key world error value nameEq keyEq
    originalFinal (sortedFinal sorted)) ->
  endpointWithdrawnGenerations endpoint =
    endpointWithdrawnGenerations (cumulativeEndpoint reduction) ->
  CanonicalReplayAccountingLaws name key world error value original
    (sortedTrace sorted) (endpointWithdrawnGenerations endpoint)
    (deletionSortingOccurrenceCorrespondence reduction sorted) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted
deletionSortingOrchestrationAccountingSpike nameEq keyEq protocol original
  reduction ordering sorted endpoint exact laws =
    assembleOneTraceAccountingFromReplay reduction ordering sorted endpoint exact
      (sameExternalOrchestrationTransitiveSpike nameEq
        (reductionSameExternalInputs reduction) (sortedSameInputs sorted))
      laws

||| Recover the producer-owned history entry behind one membership in its
||| projected generation list.
0 canonicalElemMapPreimage :
  {source, target : Type} -> {project : source -> target} ->
  {selected : target} -> {entries : List source} ->
  Elem selected (map project entries) ->
  (entry : source ** (Elem entry entries, project entry = selected))
canonicalElemMapPreimage {entries = entry :: rest} Here =
  (entry ** (Here, Refl))
canonicalElemMapPreimage {entries = entry :: rest} (There later) =
  case canonicalElemMapPreimage later of
    (found ** (foundIn, exact)) => (found ** (There foundIn, exact))

0 canonicalAccountedGenerationInHistoryMap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original} ->
  {ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)} ->
  {sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering} ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations
    (accountedEndpoint accounting)) ->
  Elem generation (map
    DGamma.CP5ConfluenceDeletionChainSpike.classifiedGeneration
    (deletionGenerationHistory reduction))
canonicalAccountedGenerationInHistoryMap {reduction} accounting generation
  member =
    replace {p = \generations => Elem generation generations}
      (sym (deletionHistoryAligned reduction))
      (replace {p = \generations => Elem generation generations}
        (accountedWithdrawnExact accounting) member)

0 canonicalAccountedGenerationClassified :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, originalFinal : SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original} ->
  {ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)} ->
  {sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering} ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations
    (accountedEndpoint accounting)) ->
  DeletedGenerationClassification name key world error value nameEq original
    generation
canonicalAccountedGenerationClassified {reduction} accounting generation member =
  case canonicalElemMapPreimage
    {source = (candidate : RegistrationGeneration name **
      DeletedGenerationClassification name key world error value nameEq original
        candidate)}
    {target = RegistrationGeneration name}
    {project = DGamma.CP5ConfluenceDeletionChainSpike.classifiedGeneration}
    (canonicalAccountedGenerationInHistoryMap accounting generation member) of
    ((stored ** classification) ** (storedIn, exact)) =>
      replace
        {p = \candidate => DeletedGenerationClassification name key world error
          value nameEq original candidate}
        exact classification

||| Erased producer schedule used to seal the runtime schedule stored by the
||| bridge-facing capital.  All proof fields come from the exact indexed chain.
public export
0 producerCanonicalSchedule :
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (supportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal reduction)
      (cumulativeEndpoint reduction) (orderedSupportNames ordering)) ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  CanonicalSchedule name key world error value protocol nameEq keyEq original
producerCanonicalSchedule premises reduction ordering sorted supportTransport
  accounting =
    MkCanonicalSchedule
      (sortedFinal sorted)
      (sortedTrace sorted)
      (accountedExternalInputs accounting)
      (replayDiscipline (chainReplayCapital premises))
      (replayDiscipline (sortedPremises sorted))
      (orderedSupportNames ordering)
      (originalSupportLinearization supportTransport)
      (sortedBlock sorted)
      (sortedBlocksFollowOrder sorted)
      (sortedLifecycleCoverage sorted)
      (inputPlacementToOriginal supportTransport
        (sortedTrace sorted) (sortedInputPlacement sorted))
      (accountedEndpoint accounting)
      (accountedGeneratedRegistrations accounting)

||| Bridge-facing capital preserves the exact producer chain.  No canonical
||| schedule, occurrence correspondence, or authentication pair is freely stored:
||| every trusted consumer projection below is definitionally reconstructed from
||| these deletion, ordering, sorting, and accounting values.
public export
record IndependentCanonicalSchedule
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkIndependentCanonicalSchedule
  capitalPremises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original
  capitalReduction : ClosingFreeReduction name key world error value protocol
    nameEq keyEq original
  capitalOrdering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal capitalReduction)
  capitalSorted : SortedClosingFreeTrace name key world error value protocol
    nameEq keyEq (reducedTrace capitalReduction) capitalOrdering
  capitalSupportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal capitalReduction)
      (cumulativeEndpoint capitalReduction)
      (orderedSupportNames capitalOrdering)
  capitalAccounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original capitalReduction capitalOrdering capitalSorted
  capitalCanonicalSchedule : CanonicalSchedule name key world error value protocol
    nameEq keyEq original
  0 capitalCanonicalScheduleExact : capitalCanonicalSchedule =
    producerCanonicalSchedule capitalPremises capitalReduction capitalOrdering
      capitalSorted capitalSupportTransport capitalAccounting
  capitalWithdrawnClassified :
    (generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (accountedEndpoint capitalAccounting)) ->
    DeletedGenerationClassification name key world error value nameEq original
      generation

||| The public CP3 schedule is a projection of the exact producer chain, not a
||| constructor argument.  A coherent caller-selected `(tree,map)` pair has no
||| field through which it can enter this value.
public export
canonicalSchedule :
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original ->
  CanonicalSchedule name key world error value protocol nameEq keyEq original
canonicalSchedule capital = capitalCanonicalSchedule capital

public export
0 originalTraceIndependent :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  TraceIndependent name key world error value keyEq original
originalTraceIndependent capital =
  replayIndependent (chainReplayCapital (capitalPremises capital))

public export
0 canonicalReplayCorrespondence :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  RelationalReplayCorrespondence name key world error value original
    (canonicalTrace (canonicalSchedule capital))
canonicalReplayCorrespondence
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      composeRelationalReplayCorrespondence
        (reductionReplayCorrespondence reduction)
        (sortingReplayCorrespondence sorted)

public export
0 canonicalOccurrenceCorrespondence :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  ActionRegistrationReplayCorrespondence name key world error value original
    (canonicalTrace (canonicalSchedule capital))
canonicalOccurrenceCorrespondence
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      deletionSortingOccurrenceCorrespondence reduction sorted

public export
0 canonicalRegistrationAuthentication :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  AuthenticatedCanonicalRegistrationMap name key world error value original
    (canonicalTrace (canonicalSchedule capital))
    (endpointWithdrawnGenerations (canonicalEndpoint (canonicalSchedule capital)))
    (canonicalRegistrationTree (canonicalSchedule capital))
    (canonicalOccurrenceCorrespondence capital)
canonicalRegistrationAuthentication
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      accountedRegistrationAuthentication accounting

public export
0 canonicalReplayPremises :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq
    (canonicalTrace (canonicalSchedule capital))
canonicalReplayPremises
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) = sortedPremises sorted

public export
0 canonicalTraceIndependent :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  TraceIndependent name key world error value keyEq
    (canonicalTrace (canonicalSchedule capital))
canonicalTraceIndependent
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      replayIndependent (sortedPremises sorted)

public export
0 canonicalWithdrawnClassified :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  (generation : RegistrationGeneration name) ->
  Elem generation (endpointWithdrawnGenerations
    (canonicalEndpoint (canonicalSchedule capital))) ->
  DeletedGenerationClassification name key world error value nameEq original
    generation
canonicalWithdrawnClassified
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) = classified

||| Complete simultaneous-package constructor.  It merely seals the exact
||| producer values; all consumer-facing maps and schedules are derived above.
public export
0 assembleIndependentCanonicalSchedule :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (premises : CanonicalizationPremises name key world error value protocol
    nameEq keyEq original) ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  (supportTransport : CanonicalSupportTransport name key world error value
    nameEq keyEq originalFinal (reducedFinal reduction)
      (cumulativeEndpoint reduction) (orderedSupportNames ordering)) ->
  (accounting : OneTraceOrchestrationAccounting name key world error value
    protocol nameEq keyEq original reduction ordering sorted) ->
  ((generation : RegistrationGeneration name) ->
    Elem generation (endpointWithdrawnGenerations
      (accountedEndpoint accounting)) ->
    DeletedGenerationClassification name key world error value nameEq original
      generation) ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
assembleIndependentCanonicalSchedule nameEq keyEq protocol original premises
  reduction ordering sorted supportTransport accounting classified =
    MkIndependentCanonicalSchedule premises reduction ordering sorted
      supportTransport accounting
      (producerCanonicalSchedule premises reduction ordering sorted
        supportTransport accounting)
      Refl classified

||| The hard producer derives the typed cumulative classification from the
||| deletion history and returns the simultaneous package above.  Consumers no
||| longer receive an opaque schedule detached from replay indices.
public export
0 independentCanonicalScheduleSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  CanonicalizationPremises name key world error value protocol nameEq keyEq original ->
  (reduction : ClosingFreeReduction name key world error value protocol nameEq
    keyEq original) ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    (reducedFinal reduction)) ->
  (sorted : SortedClosingFreeTrace name key world error value protocol nameEq
    keyEq (reducedTrace reduction) ordering) ->
  CanonicalSupportTransport name key world error value nameEq keyEq originalFinal
    (reducedFinal reduction) (cumulativeEndpoint reduction)
      (orderedSupportNames ordering) ->
  OneTraceOrchestrationAccounting name key world error value protocol nameEq keyEq
    original reduction ordering sorted ->
  IndependentCanonicalSchedule name key world error value protocol nameEq keyEq
    original
independentCanonicalScheduleSpike nameEq keyEq protocol original premises
  reduction ordering sorted supportTransport accounting =
    assembleIndependentCanonicalSchedule nameEq keyEq protocol original premises
      reduction ordering sorted supportTransport accounting
      (canonicalAccountedGenerationClassified accounting)
