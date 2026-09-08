module DGamma.CP5O20InversionChildSafetySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SupportedReferenceSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| A genuine REPLAYED generated birth induces the supported parent edge in
||| the ORIGINAL fixed reference. Both origin maps and original raw freshness
||| are consumed; the replayed endpoint metadata is never guessed.
export
0 o20ReplayedBirthSupportPath :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, replayedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial replayedFinal) ->
  ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed ->
  (parent, child : name) -> (component : Component key value world error) ->
  LocatedGeneratedRegistration child parent component replayed ->
  (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry originalFinal) = Just fiber) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} parent originalFinal = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child originalFinal = True) ->
  O20SupportedPath name key world error value nameEq keyEq originalFinal parent child
o20ReplayedBirthSupportPath {name} {key} {world} {error} {value} nameEq keyEq protocol
  original capital unique replayed occurrences parent child component birth fiber found parentSupported childSupported =
    O20SupportedOne parentSupported childSupported (SupportParent (MkParentSupportEdge fiber found
      (sym (cong fst (canonicalGeneratedOriginMetadata name key world error value nameEq keyEq protocol
        original capital unique child parent component (replayGeneratedRegistrationOrigin occurrences birth) fiber found)))))

||| Eliminate an explicitly observed ORIGINAL child lookup. Absent contradicts
||| accepted support=active; present gives D1's exact original parent edge.
export
0 o20IncomparableBirthObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, replayedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial replayedFinal) ->
  ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed ->
  (parent, child : name) -> (component : Component key value world error) ->
  LocatedGeneratedRegistration child parent component replayed ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} parent originalFinal = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child originalFinal = True) ->
  Not (O20SupportedPath name key world error value nameEq keyEq originalFinal parent child) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry originalFinal) = observed) -> Void
o20IncomparableBirthObserved {name} {key} {world} {error} {value} {originalFinal} nameEq keyEq protocol
  original capital unique replayed occurrences parent child component birth parentSupported childSupported noPath Nothing found =
    absurd (trans
      (sym (the (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} child originalFinal = False)
        (rewrite found in Refl)))
      (trans (sym (replaySupportMatchesActive (chainReplayCapital (capitalPremises capital)) child)) childSupported))
o20IncomparableBirthObserved nameEq keyEq protocol original capital unique replayed occurrences parent child component birth
  parentSupported childSupported noPath (Just fiber) found =
    noPath (o20ReplayedBirthSupportPath nameEq keyEq protocol original capital unique replayed occurrences
      parent child component birth fiber found parentSupported childSupported)

||| Supported-reference incomparability excludes EVERY actual replayed birth
||| of this child by this parent. Original lookup is observed here, not supplied.
export
0 o20IncomparableReplayedBirth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, replayedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial replayedFinal) ->
  ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed ->
  (parent, child : name) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} parent originalFinal = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child originalFinal = True) ->
  Not (O20SupportedPath name key world error value nameEq keyEq originalFinal parent child) ->
  (component : Component key value world error) -> LocatedGeneratedRegistration child parent component replayed -> Void
o20IncomparableReplayedBirth {name} {key} {world} {error} {value} {originalFinal} nameEq keyEq protocol
  original capital unique replayed occurrences parent child parentSupported childSupported noPath component birth =
    o20IncomparableBirthObserved nameEq keyEq protocol original capital unique replayed occurrences parent child component birth
      parentSupported childSupported noPath (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry originalFinal)) Refl

||| Lift the SAME generated birth through one real preceding transition.
export
0 o20GeneratedBirthPrepend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  {child, parent : name} -> {component : Component key value world error} ->
  LocatedGeneratedRegistration child parent component rest ->
  LocatedGeneratedRegistration child parent component (MoreTransitions step rest)
o20GeneratedBirthPrepend step rest (MkLocatedGeneratedRegistration before afterState prior birth later action exact) =
  MkLocatedGeneratedRegistration before afterState (MoreTransitions step prior) birth later action (cong (MoreTransitions step) exact)

||| Extend a located birth by the actual following suffix without changing
||| its before-cut, action, or local occurrence.
export
0 o20GeneratedBirthAppend :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (trace : Transitions first middle) -> (following : Transitions middle finalState) ->
  {child, parent : name} -> {component : Component key value world error} ->
  LocatedGeneratedRegistration child parent component trace ->
  LocatedGeneratedRegistration child parent component (appendTransitions trace following)
o20GeneratedBirthAppend trace following (MkLocatedGeneratedRegistration before afterState prior birth later action exact) =
  MkLocatedGeneratedRegistration before afterState prior birth (appendTransitions later following) action
    (trans (sym (appendTransitionsAssociative prior (MoreTransitions birth later) following))
      (cong (\candidate => appendTransitions candidate following) exact))

||| Structural lifting through the actual preceding trace, never a scalar
||| position chosen independently of the occurrence's trace spine.
export
0 o20GeneratedBirthAfterTrace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (prior : Transitions first middle) -> (trace : Transitions middle finalState) ->
  {child, parent : name} -> {component : Component key value world error} ->
  LocatedGeneratedRegistration child parent component trace ->
  LocatedGeneratedRegistration child parent component (appendTransitions prior trace)
o20GeneratedBirthAfterTrace NoTransitions trace birth = birth
o20GeneratedBirthAfterTrace (MoreTransitions step rest) trace birth =
  o20GeneratedBirthPrepend step (appendTransitions rest trace) (o20GeneratedBirthAfterTrace rest trace birth)

||| A birth in the selected physical block is a birth of the SAME replayed
||| whole trace, authenticated by the decomposition owned by that block.
export
0 o20GeneratedBirthInBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {actor, child, parent : name} ->
  {component : Component key value world error} ->
  {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor trace) ->
  LocatedGeneratedRegistration child parent component (blockBody block) ->
  LocatedGeneratedRegistration child parent component trace
o20GeneratedBirthInBlock {child} {parent} {component} block birth =
  replace {p = \candidate => LocatedGeneratedRegistration child parent component candidate} (blockDecomposition block)
    (o20GeneratedBirthAfterTrace (traceBeforeBlock block)
      (MoreTransitions (beginTransition (blockOpening block)) (appendTransitions (blockBody block) (traceAfterBlock block)))
      (o20GeneratedBirthPrepend (beginTransition (blockOpening block)) (appendTransitions (blockBody block) (traceAfterBlock block))
        (o20GeneratedBirthAppend (blockBody block) (traceAfterBlock block) birth)))

||| The actor-only body grammar fixes every child-registration parent to the
||| selected actor. Structural induction turns excluded located births into
||| the complete NoGeneratedChild certificate demanded by actual O19 safety.
export
0 o20NoGeneratedFromActorBirth :
  {name, key, world, error : Type} -> {value : key -> Type} -> {actor, forbidden : name} ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> ActorLifecycleOnly actor trace ->
  ((component : Component key value world error) -> LocatedGeneratedRegistration forbidden actor component trace -> Void) ->
  NoGeneratedChild forbidden trace
o20NoGeneratedFromActorBirth NoTransitions ActorLifecycleEnd excluded = NoGeneratedChildEnd
o20NoGeneratedFromActorBirth (MoreTransitions step rest) (ActorLifecycleStep step rest lifecycle owned only) excluded =
  NoGeneratedChildStep step rest
    (\parent, component, same => absurd (trans (sym (cong isLifecycleAction same)) lifecycle))
    (o20NoGeneratedFromActorBirth rest only
      (\component, birth => excluded component (o20GeneratedBirthPrepend step rest birth)))
o20NoGeneratedFromActorBirth (MoreTransitions step rest) (ActorYieldedRegistrationStep step rest yielded only) excluded =
  NoGeneratedChildStep step rest
    (\parent, component, same => case trans (sym yielded) same of
      Refl => excluded component (MkLocatedGeneratedRegistration _ _ NoTransitions step rest same Refl))
    (o20NoGeneratedFromActorBirth rest only
      (\component, birth => excluded component (o20GeneratedBirthPrepend step rest birth)))

||| Supported incomparability now PRODUCES one physical block's complete
||| child-exclusion clause, using actual body grammar and both origin maps.
export
0 o20IncomparableBlockChildSafety :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, originalFinal, replayedFinal : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (replayed : Transitions initial replayedFinal) ->
  ActionRegistrationReplayCorrespondence name key world error value (canonicalTrace (canonicalSchedule capital)) replayed ->
  (parent, child : name) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq parent replayed) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} parent originalFinal = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} child originalFinal = True) ->
  Not (O20SupportedPath name key world error value nameEq keyEq originalFinal parent child) ->
  NoGeneratedChild child (blockBody block)
o20IncomparableBlockChildSafety nameEq keyEq protocol original capital unique replayed occurrences
  parent child block parentSupported childSupported noPath =
    o20NoGeneratedFromActorBirth (blockBody block) (blockActorOnly block)
      (\component, birth => o20IncomparableReplayedBirth nameEq keyEq protocol original capital unique replayed occurrences
        parent child parentSupported childSupported noPath component (o20GeneratedBirthInBlock block birth))
