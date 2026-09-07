module DGamma.CP5O20EpisodeSynchronizationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
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
