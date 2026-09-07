module DGamma.CP5O20EpisodeSynchronizationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5AcceptedSupportTruthSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import DGamma.CP5O20SupportedEndpointCapitalSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Internal paired-cut invariant: ambient is GLOBAL, tables retain full ordered
||| bindings. This specification does not assert that canonical cuts satisfy it.
||| A canonical producer must instantiate the accepted fixed bijection itself.
public export
record RenamedRuntimeEffects
  (name, key, world : Type) (value : key -> Type)
  (renaming : NameBijection name)
  (left, right : EffectState name key value world) where
  constructor MkRenamedRuntimeEffects
  0 synchronizedAmbient : (effectAmbient left = effectAmbient right)
  0 synchronizedTables : (selected : name) ->
    (bindings (effectTables left selected) =
      bindings (effectTables right (renameForward renaming selected)))

||| Runtime binding equality, not equality of erased table certificates.
export
0 synchronizationLookupBindings :
  (key : Type) -> (value : key -> Type) -> (keyEq : DecEq key) ->
  (wanted : key) -> (left, right : CoeffectContext key value) ->
  (bindings left = bindings right) ->
  (lookupBinding @{keyEq} wanted left = lookupBinding @{keyEq} wanted right)
synchronizationLookupBindings key value keyEq wanted
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) same =
    cong (lookupEntries {key = key} {value = value} @{keyEq} wanted) same

||| R180 B4: observed-head prerequisite, NOT the exhausted general B3 lemma.
||| The producer must supply both equations for this exact Maybe VALUE.
export
0 synchronizationResolvedHeadObserved :
  (name, key, world : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (wanted : key) -> (rest : List key) ->
  (leftOwner, rightOwner : name) -> (leftTail, rightTail : View name rest) ->
  (left, right : EffectState name key value world) ->
  (headValue : Maybe (value wanted)) ->
  (lookupBinding @{keyEq} wanted (effectTables left leftOwner) = headValue) ->
  (lookupBinding @{keyEq} wanted (effectTables right rightOwner) = headValue) ->
  (resolveEffectValues @{keyEq} rest leftTail left =
    resolveEffectValues @{keyEq} rest rightTail right) ->
  (resolveEffectValues @{keyEq} (wanted :: rest)
    (ProviderView leftOwner leftTail) left =
      resolveEffectValues @{keyEq} (wanted :: rest)
        (ProviderView rightOwner rightTail) right)
synchronizationResolvedHeadObserved name key world value keyEq wanted rest
  leftOwner rightOwner leftTail rightTail left right Nothing leftHead rightHead
  tailSame = rewrite leftHead in rewrite rightHead in Refl
synchronizationResolvedHeadObserved name key world value keyEq wanted rest
  leftOwner rightOwner leftTail rightTail left right (Just observed) leftHead
  rightHead tailSame = rewrite leftHead in rewrite rightHead in
    cong (map (OneDepValue {key = key} {value = value} {k = wanted} {rest = rest}
      observed)) tailSame

||| Producer-owned observation: choose the ACTUAL left lookup value and derive
||| its equation at the renamed right provider, rather than assume availability.
export
0 synchronizationHeadValue :
  (name, key, world : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (wanted : key) -> (leftOwner, rightOwner : name) ->
  (left, right : EffectState name key value world) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  (renameForward renaming leftOwner = rightOwner) ->
  (headValue : Maybe (value wanted) **
    (lookupBinding @{keyEq} wanted (effectTables left leftOwner) = headValue,
     lookupBinding @{keyEq} wanted (effectTables right rightOwner) = headValue))
synchronizationHeadValue name key world value keyEq renaming wanted leftOwner
  rightOwner left right effects ownerSame =
    (lookupBinding {key = key} {value = value} @{keyEq} wanted
      (effectTables left leftOwner) **
      (Refl, sym (trans (synchronizationLookupBindings key value keyEq wanted
        (effectTables left leftOwner)
        (effectTables right (renameForward renaming leftOwner))
        (synchronizedTables effects leftOwner))
        (cong (\owner => lookupBinding {key = key} {value = value} @{keyEq}
          wanted (effectTables right owner)) ownerSame))))

||| Supervisor-authorized projection of B4+B5 along structural dependency
||| recursion. No direct attempt at the exhausted B3 suspended-case body.
||| This consumes an INTERNAL cut invariant; it does not produce that invariant.
export
0 synchronizationResolutionFromObservedHeads :
  (name, key, world : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (deps : List key) -> (leftView, rightView : View name deps) ->
  (left, right : EffectState name key value world) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  ViewRelatedBy renaming leftView rightView ->
  (resolveEffectValues @{keyEq} deps leftView left =
    resolveEffectValues @{keyEq} deps rightView right)
synchronizationResolutionFromObservedHeads name key world value keyEq renaming
  [] EmptyView EmptyView left right effects views = Refl
synchronizationResolutionFromObservedHeads name key world value keyEq renaming
  (wanted :: rest) (ProviderView leftOwner leftTail)
  (ProviderView rightOwner rightTail) left right effects views =
    case synchronizationHeadValue name key world value keyEq renaming wanted
      leftOwner rightOwner left right effects (fst (consInjective views)) of
      (headValue ** (leftHead, rightHead)) =>
        synchronizationResolvedHeadObserved name key world value keyEq wanted
          rest leftOwner rightOwner leftTail rightTail left right headValue
          leftHead rightHead
          (synchronizationResolutionFromObservedHeads name key world value keyEq
            renaming rest leftTail rightTail left right effects
              (snd (consInjective views)))

||| Exact evaluator-facing local source: global ambient plus the actor's
||| canonically restricted complete ordered table. No erased-proof equality.
export
0 synchronizationLocalSource :
  (name, key, world : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (provision : CoeffectSpec key) -> (selected : name) ->
  (left, right : EffectState name key value world) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  (MkLocalState (effectAmbient left)
    (restrictOwnedPreservingOrder @{keyEq} provision (effectTables left selected)) =
   MkLocalState (effectAmbient right)
    (restrictOwnedPreservingOrder @{keyEq} provision
      (effectTables right (renameForward renaming selected))))
synchronizationLocalSource name key world value keyEq renaming provision selected
  left right effects =
    cong2 (MkLocalState {key = key} {value = value} {world = world}
      {provision = provision}) (synchronizedAmbient effects)
      (canonicalNormalizationFromEqualBindings @{keyEq} provision
        (effectTables left selected)
        (effectTables right (renameForward renaming selected))
        (synchronizedTables effects selected))

||| Producer of the exact deterministic iterator result (including its undo
||| callback), once the INTERNAL paired-cut invariant and views are available.
||| Both capabilities are observed runtime values with evaluator equations.
export
0 synchronizationStepOutcome :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (deps : List key) -> (provision : CoeffectSpec key) -> (selected : name) ->
  (step : StepEffect key value world error deps provision) ->
  (leftView, rightView : View name deps) ->
  (left, right : EffectState name key value world) ->
  (leftCapability, rightCapability : DepValues key value deps) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  ViewRelatedBy renaming leftView rightView ->
  (resolveEffectValues @{keyEq} deps leftView left = Just leftCapability) ->
  (resolveEffectValues @{keyEq} deps rightView right = Just rightCapability) ->
  (runStepEffect step leftCapability
    (MkLocalState (effectAmbient left)
      (restrictOwnedPreservingOrder @{keyEq} provision (effectTables left selected))) =
   runStepEffect step rightCapability
    (MkLocalState (effectAmbient right)
      (restrictOwnedPreservingOrder @{keyEq} provision
        (effectTables right (renameForward renaming selected)))))
synchronizationStepOutcome name key world error value keyEq renaming deps provision
  selected step leftView rightView left right leftCapability rightCapability
  effects views leftResolved rightResolved =
    cong2 (runStepEffect step)
      (justInjective (trans (sym leftResolved)
        (trans (synchronizationResolutionFromObservedHeads name key world value
          keyEq renaming deps leftView rightView left right effects views)
          rightResolved)))
      (synchronizationLocalSource name key world value keyEq renaming provision
        selected left right effects)

||| Pointwise undo induction step consumes observed successful outcome equality,
||| rather than an accumulator-equality oracle. No function extensionality.
export
0 synchronizationPushedUndo :
  (key, world, error : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (provision : CoeffectSpec key) ->
  (leftOlder, rightOlder : LocalState key value world provision ->
    LocalState key value world provision) ->
  (leftAfter, rightAfter : LocalState key value world provision) ->
  (leftUndo, rightUndo : LocalState key value world provision ->
    LocalState key value world provision) ->
  AccumulatorRelated leftOlder rightOlder ->
  (the (Either error (LocalState key value world provision,
    LocalState key value world provision -> LocalState key value world provision))
      (Right (leftAfter, leftUndo)) = Right (rightAfter, rightUndo)) ->
  AccumulatorRelated
    (pushLocalUndo @{keyEq} provision leftOlder leftUndo)
    (pushLocalUndo @{keyEq} provision rightOlder rightUndo)
synchronizationPushedUndo key world error value keyEq provision leftOlder
  rightOlder leftAfter rightAfter leftUndo rightUndo older observedSame input =
    case observedSame of
      Refl => older (normalizeLocal @{keyEq} provision
        (rightUndo (normalizeLocal @{keyEq} provision input)))

||| Executable empty-origin observations at arbitrary queried names. Only the
||| runtime registry bindings are observed; proof certificates remain erased.
export
0 synchronizationEmptyObservations :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (bindings fibers = []) -> (selected : name) ->
  (bindings (effectTables (projectEffectState {name = name} {key = key}
      {value = value} {world = world} {error = error} @{nameEq}
      (MkSystemState {name = name} {key = key} {value = value} {world = world}
        {error = error} ambient fibers)) selected) =
    bindings (effectTables (projectEffectState {name = name} {key = key}
      {value = value} {world = world} {error = error} @{nameEq}
      (MkSystemState {name = name} {key = key} {value = value} {world = world}
        {error = error} ambient fibers)) (renameForward renaming selected)),
   MaybeFiberRelatedBy {name = name} {key = key} {value = value} {world = world}
    {error = error} renaming
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} selected fibers)
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (renameForward renaming selected) fibers))
synchronizationEmptyObservations name key world error value nameEq renaming
  ambient (MkCoeffectContext [] unique) empty selected = (Refl, RenamedAbsent)
synchronizationEmptyObservations name key world error value nameEq renaming
  ambient (MkCoeffectContext (entry :: later) unique) empty selected =
    case empty of Refl impossible

||| Top-level dependent projection: no local proof lambda in the origin producer.
export
0 synchronizationEmptyTables :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (bindings fibers = []) -> (selected : name) ->
  (bindings (effectTables (projectEffectState {name = name} {key = key}
      {value = value} {world = world} {error = error} @{nameEq}
      (MkSystemState {name = name} {key = key} {value = value} {world = world}
        {error = error} ambient fibers)) selected) =
    bindings (effectTables (projectEffectState {name = name} {key = key}
      {value = value} {world = world} {error = error} @{nameEq}
      (MkSystemState {name = name} {key = key} {value = value} {world = world}
        {error = error} ambient fibers)) (renameForward renaming selected)))
synchronizationEmptyTables name key world error value nameEq renaming ambient
  fibers empty selected = fst (synchronizationEmptyObservations name key world
    error value nameEq renaming ambient fibers empty selected)

||| Invariant at ONE pair of actual cuts of supplied whole executions. The
||| bijection is fixed by accepted orchestration, never chosen by this record.
||| Its producer must recur along the paired supported episodes; a zero-cut
||| instance alone is NOT that induction or an O20 endpoint theorem.
public export
record SupportedCanonicalEpisodeSynchronization
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftOriginalFinal, rightOriginalFinal,
   leftExecutionFinal, rightExecutionFinal : SystemState name key value world error}
  (leftOriginal : Transitions initial leftOriginalFinal)
  (rightOriginal : Transitions initial rightOriginalFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftOriginal rightOriginal)
  (leftExecution : Transitions initial leftExecutionFinal)
  (rightExecution : Transitions initial rightExecutionFinal)
  (selected : name) (leftCut, rightCut : SystemState name key value world error)
  (leftPrefix : Transitions initial leftCut)
  (leftSuffix : Transitions leftCut leftExecutionFinal)
  (rightPrefix : Transitions initial rightCut)
  (rightSuffix : Transitions rightCut rightExecutionFinal) where
  constructor MkSupportedCanonicalEpisodeSynchronization
  0 synchronizedActorSupported : isSupported {name = name} {key = key}
    {value = value} {world = world} {error = error}
    @{nameEq} @{keyEq} selected leftOriginalFinal = True
  0 synchronizedLeftCutOccurrence : appendTransitions leftPrefix leftSuffix = leftExecution
  0 synchronizedRightCutOccurrence : appendTransitions rightPrefix rightSuffix = rightExecution
  0 synchronizedCutEffects : RenamedRuntimeEffects name key world value
    (expectedBridgeBijection sameInputs)
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} leftCut)
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} rightCut)
  0 synchronizedActorControls : MaybeFiberRelatedBy {name = name} {key = key}
    {value = value} {world = world} {error = error} (expectedBridgeBijection sameInputs)
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} selected (registry leftCut))
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (renameForward (expectedBridgeBijection sameInputs)
        selected) (registry rightCut))

||| Genuine ZERO-prefix producer. All runtime agreement is derived from the
||| actual common empty registry. No paired agreement is accepted as a premise.
export
0 synchronizationEmptyOrigin :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, leftOriginalFinal, rightOriginalFinal,
   leftExecutionFinal, rightExecutionFinal : SystemState name key value world error} ->
  (leftOriginal : Transitions initial leftOriginalFinal) ->
  (rightOriginal : Transitions initial rightOriginalFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftOriginal rightOriginal) ->
  (leftExecution : Transitions initial leftExecutionFinal) ->
  (rightExecution : Transitions initial rightExecutionFinal) ->
  (bindings (registry initial) = []) -> (selected : name) ->
  (isSupported {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} selected leftOriginalFinal = True) ->
  SupportedCanonicalEpisodeSynchronization name key world error value nameEq keyEq
    leftOriginal rightOriginal sameInputs leftExecution rightExecution selected
    initial initial NoTransitions leftExecution NoTransitions rightExecution
synchronizationEmptyOrigin name key world error value nameEq keyEq
  {initial = MkSystemState ambient fibers} leftOriginal rightOriginal sameInputs
  leftExecution rightExecution empty selected supported =
    MkSupportedCanonicalEpisodeSynchronization supported Refl Refl
      (MkRenamedRuntimeEffects Refl (synchronizationEmptyTables name key world
        error value nameEq (expectedBridgeBijection sameInputs) ambient fibers empty))
      (snd (synchronizationEmptyObservations name key world error value nameEq
        (expectedBridgeBijection sameInputs) ambient fibers empty selected))

||| Instantiate ZERO prefixes of the ACTUAL O19 operational replay and the
||| ACTUAL right canonical execution. Unique births/matched generation capital
||| remain threaded; no arbitrary replacement execution or bijection is chosen.
export
0 synchronizationOperationalOrigin :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 matched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching) ->
  (selected : name) ->
  (isSupported {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  SupportedCanonicalEpisodeSynchronization name key world error value nameEq keyEq
    leftTrace rightTrace sameInputs (operationalTargetTrace operational)
    (canonicalTrace (canonicalSchedule rightCapital)) selected initial initial
    NoTransitions (operationalTargetTrace operational)
    NoTransitions (canonicalTrace (canonicalSchedule rightCapital))
synchronizationOperationalOrigin name key world error value nameEq keyEq protocol
  leftTrace rightTrace sameInputs leftCapital rightCapital leftUnique rightUnique
  matched operational selected supported =
    synchronizationEmptyOrigin name key world error value nameEq keyEq leftTrace
      rightTrace sameInputs (operationalTargetTrace operational)
      (canonicalTrace (canonicalSchedule rightCapital))
      (replayInitialEmpty (operationalTargetPremises operational)) selected supported

||| R179's one-sided capital at BOTH actual canonical endpoints, with the
||| opposite support truth produced by accepted A9/unique-birth transport.
||| These two packets do NOT assert equal views, accumulators, or endpoints.
export
0 synchronizationSupportedCanonicalPackets :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 matched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  (selected : name) ->
  (isSupported {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} selected leftFinal = True) ->
  (SupportedCanonicalEndpointView name key world error value nameEq keyEq selected
    (canonicalFinal (canonicalSchedule leftCapital)),
   SupportedCanonicalEndpointView name key world error value nameEq keyEq
    (renameForward (expectedBridgeBijection sameInputs) selected)
    (canonicalFinal (canonicalSchedule rightCapital)))
synchronizationSupportedCanonicalPackets name key world error value nameEq keyEq
  protocol leftTrace rightTrace sameInputs leftCapital rightCapital leftUnique
  rightUnique matched selected supported =
    (canonicalSupportedEndpointView name key world error value nameEq keyEq protocol
      leftTrace leftCapital selected supported,
     canonicalSupportedEndpointView name key world error value nameEq keyEq protocol
      rightTrace rightCapital (renameForward (expectedBridgeBijection sameInputs) selected)
      (acceptedSupportedTruthForward name key world error value nameEq keyEq protocol
        leftTrace rightTrace sameInputs matched
        (replayAligned (chainReplayCapital (capitalPremises leftCapital)))
        (replayAligned (chainReplayCapital (capitalPremises rightCapital)))
        (replayDiscipline (chainReplayCapital (capitalPremises leftCapital)))
        (replayInitialEmpty (chainReplayCapital (capitalPremises leftCapital)))
        leftUnique rightUnique selected supported))
