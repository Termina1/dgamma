module DGamma.CP5ConfluenceCanonicalSortSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP4Support
import DGamma.CP4SupportQuiescence
import DGamma.CP4SupportSolution
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
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

||| Construct the finite linearization from re-established Lemma-68 capital.
public export
0 supportOrderingSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  SupportOrderingCapital name key world error value nameEq keyEq finalState
supportOrderingSpike = ?supportOrderingSpike_rhs

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

||| Bubble actor blocks by repeated `AdjacentSwapResult`s.  The output itself is
||| the sorting-specific recursive transport package, rather than only final
||| schedule-shaped data.
public export
0 sortClosingFreeTraceSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq trace ->
  ClosingFreeTraceShape name key world error value nameEq keyEq trace ->
  (ordering : SupportOrderingCapital name key world error value nameEq keyEq
    finalState) ->
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
