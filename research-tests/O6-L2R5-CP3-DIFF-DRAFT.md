# L2R5 — CP3 DIFF DRAFT for owner signature

## Signature status (one-page decision table)

**NO production edit authorized or performed. NOT YET SIGNABLE AS A COMPLETE CURE.** Tier 1 below is exact proposed text obtained from checked research declarations by the disclosed renamings; it has NOT been compiled in CP3. Tier 2 is explicitly UNCHECKED specification text with unresolved connector parameters. A signature today could approve the Tier-1 candidate design and rebuild plan, **not** certify a normalizer, all-role retirement replay, general gap coverage, O19 adjacency or Theorem 73.

| Proposed CP3 change | Checked backing | Unchecked / blocked by |
|---|---|---|
| Move transitionCount / LocatedActionOccurrence / locatedActionOrdinal before grammar | Existing CP3 declarations, byte-exact move below | New ordering/typecheck not performed; no semantic change intended |
| ActorLifecycleOnly becomes extended core + forced-root bundle | L2R3 4974a6f9; old→extended→attached d2b26a9a / 0f19676d | Global last-release assignment, forced closure linkage, actual R191 whole relocation |
| Own-child Retire/Remove in core | R192 971fedfc (grammar); block-copy file later changed d3e6d73e; source lookup + parent witnesses | L2R5 B5 provider wall prevents lifecycle/full R191 replay |
| Full LocatedOpenEpisodeBlock / BlockBefore rehome | L2R3 a7799047 / ce0c13bd; real small/barrier blocks 1b7e1eeb / 224988a1 | Maximal nonoverlap/decomposition globally; quantities change explicitly listed |
| CanonicalInputPlacement inherited availability-aware clauses | R178 4e1043fe; L2R2 smallRootEarliest; L2R5 5822f06e / cb60b7d7 current-cut facts | Terminal earliest on all births, front-normal and last-release connectors below |
| Least forced set, trace-linked classifier, anchor assignment | Generic leastness 7737a019; local KeyReleased / EarlierForcedRoot | TIER 2: no compiled global classifier/assignment |
| CanonicalSchedule.inputPlacement original-trace index | Inherited research placement record shape | In-file constructor and all callers must be adapted/rechecked; no constructor proof here |
| RootInputsBeforeLifecycle replacement scope | Barrier-order impossibility 9c7c0a7c; old strict reading cannot hold | TIER 2 front-normal; non-insert root-action/generation disposition remains explicit |
| O19 safetyBlocksAdjacent over full attached blocks | L2R4 exact unchanged fixture applications 58b71b4f / b042b76e | General selector zero-gap still open; do not remove/assume this field |
| Normalizer endpoint relation and iteration | RegistryExtensional 0fbc3d33, snapshot embedding 21453f7c, two-insert endpoint algebra 71f6de67, Retire transport c60f315a | Native Insert/Insert applicability, remaining action transport, swap existence/distance iteration OPEN |
| Raw catalog generated from actual traces | L2R5 ef9b9f9b; both full fixtures 8c603e3b | NOT AttachedNormalForm; catalog→placed-bundle assignment still open |

## Frozen baseline and exact edit coordinates

All coordinates are OLD line numbers in this lane's unchanged CP3 at 769d332d. CP3 git blob: **2c697e532e83989de8591fa6a4378747c6a501c0**. Main worktree was never accessed. R196's concurrent changes are not silently imported into this proposal. No evaluator, O-Insert provision guard, registration scanner, vestigial relation, effect/control equivalence or confluence conclusion changes are proposed.

1. MOVE CP3:2093–2096 (transitionCount), :2098–2115 (LocatedActionOccurrence, including docstring), :2117–2119 (locatedActionOrdinal), preserving the separating blank lines through2120, to immediately BEFORE the grammar at1781. All bytes unchanged. These declarations depend only on existing transition/state primitives and appendTransitions, not block types. This avoids a forward-reference cycle when AttachedRelease is rehomed from a research module that previously imported CP3.
2. REPLACE :1781–1804 with T1.1. New core keeps the research own-child lookup/parent witnesses; attached wrapper keeps actual checked root bundle and empty initial barrier history.
3. REPLACE full record text :1821–1846 and :1871–1889 with T1.2 in their respective original locations. Keep NoLifecycleBy, prefixToBlockOpening (:1848–1858) and prefixThroughBlock (:1860–1869) under their existing names; their bodies are unchanged. Do not paste both records across/deleting those intervening definitions.
4. REPLACE :3152–3195 with T1.3's final record; insert its preceding helper declarations before that record, after RootOrchestrationStep/SameExternalOrchestration/located-occurrence definitions. Avoid importing a research module back into production. T1.4 support declarations can precede the placement record after block definitions.
5. In CanonicalSchedule:3265–3266, use the exact replacement field below. canonicalBlock (:3256–3257), blocksFollowOrder (:3258–3263), lifecycleCoverage (:3264), sameInputs (:3249), registration/endpoint/tree fields retain their text; their types now refer to the rehomed grammar. ConfluenceResult (:3756ff), confluenceTheorem (:3785ff) retain their text and endpoint relations.

```idris
  inputPlacement : CanonicalInputPlacement name key world error value nameEq keyEq
    originalFinal supportOrder original canonicalTrace
```

### Renaming and quantity fidelity

`ActorLifecycleOnlyExtended` → `ActorLifecycleCore`; Extended* constructors → Core*. `ActorLifecycleOnlyAttached` → `ActorLifecycleOnly`; AttachedWithoutRoots/AttachedWithRoots → ActorWithoutForcedRoots/ActorWithForcedRoots. Located/order record names and accessor names map back to their existing CP3 names (full machine map in REHOME-MANIFEST). No reverse coercion to the old grammar is introduced, and no legacy compatibility alias is silently preserved.

The full attached research block copy erases installedness, actor grammar, no-earlier/no-later and active-at-final specification fields, whereas old CP3:1838–1843 stored those proofs unrestricted. **This proposed quantity change is explicit and needs call-site review**; runtime body/states/opening/trace decomposition data remain. The inherited placement record also erases trace/state indices and adds an explicit original trace. These are checked-backed research choices, NOT already validated production changes. Existing old-grammar induction constructors are removed/replaced: exhaustive consumers need new cases, not wildcard forwarding.

## Tier 1 — exact checked-backed proposed text

The source-origin table is: core = CP5ActorLifecycleOnlyExtended:17–65; AttachedRelease/AttachedReason/OrderedForcedRootBundle/ActorLifecycleOnlyAttached = L2R3Attached:20–122; located/order copies = L2R3Attached:147–168 /173–193; placement helpers/record = CP5AvailabilityAwarePlacement:17–148; least family/theorem = L2R3ForcedClosure:14/27; bundle/NF records = L2R3AttachedGap:21/48. See exact current locations/hashes in the manifest. Comments copied from research retain their historical qualifications; they must not be read as production proof claims.
### T1.0 — unchanged forward dependency relocation (CP3:2093–2120)

```idris
public export
transitionCount : Transitions first finalState -> Nat
transitionCount NoTransitions = 0
transitionCount (MoreTransitions transition rest) = S (transitionCount rest)

||| One action occurrence located by its dependent prefix. Canonical placement
||| uses these locations rather than raw action membership so two births of the
||| same raw name remain distinct.
public export
record LocatedActionOccurrence
  {initial, finalState : SystemState name key value world error}
  (action : Action name key value world error)
  (global : Transitions initial finalState) where
  constructor MkLocatedActionOccurrence
  actionBeforeState : SystemState name key value world error
  actionAfterState : SystemState name key value world error
  beforeActionOccurrence : Transitions initial actionBeforeState
  locatedTransition : Transition actionBeforeState actionAfterState
  afterActionOccurrence : Transitions actionAfterState finalState
  0 locatedAction : transitionAction locatedTransition = action
  0 actionOccurrenceDecomposition :
    appendTransitions beforeActionOccurrence
      (MoreTransitions locatedTransition afterActionOccurrence) = global

public export
locatedActionOrdinal : LocatedActionOccurrence action global -> Nat
locatedActionOrdinal occurrence = transitionCount (beforeActionOccurrence occurrence)

```

### T1.1 — actor core + attached grammar (replace CP3:1781–1804)

```idris
public export
data ActorLifecycleCore :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  CoreLifecycleEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} -> {state : SystemState name key value world error} ->
    ActorLifecycleCore nameEq selected (NoTransitions {state})
  CoreLifecycleStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 lifecycle : isLifecycleAction (transitionAction step) = True) ->
    (0 owned : transitionActor step = selected) ->
    (0 only : ActorLifecycleCore nameEq selected rest) ->
    ActorLifecycleCore nameEq selected (MoreTransitions step rest)
  CoreYieldedRegistrationStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected, child : name} ->
    {component : Component key value world error} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 yielded : transitionAction step = OInsert child (ChildOf selected) component) ->
    (0 only : ActorLifecycleCore nameEq selected rest) ->
    ActorLifecycleCore nameEq selected (MoreTransitions step rest)
  CoreChildRetireStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (child : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf selected) ->
    (0 action : transitionAction step = ORetire child) ->
    (0 only : ActorLifecycleCore nameEq selected rest) ->
    ActorLifecycleCore nameEq selected (MoreTransitions step rest)
  CoreChildRemoveStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (child : name) -> (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first) = Just fiber) ->
    (0 parent : fiberParent fiber = ChildOf selected) ->
    (0 action : transitionAction step = ORemove child) ->
    (0 only : ActorLifecycleCore nameEq selected rest) ->
    ActorLifecycleCore nameEq selected (MoreTransitions step rest)

public export
record AttachedRelease
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  {first, coreEnd : SystemState name key value world error}
  (core : Transitions first coreEnd)
  (component : Component key value world error) where
  constructor MkAttachedRelease
  releasedChild : name
  releasedFiber : Fiber name key value world error
  releaseOccurrence : LocatedActionOccurrence (ORemove releasedChild) core
  0 releaseFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    releasedChild (registry (actionBeforeState releaseOccurrence)) = Just releasedFiber
  0 releaseParent : fiberParent releasedFiber = ChildOf selected
  sharedProvision : key
  0 childDeclares : Elem sharedProvision (dependencies (componentProvisions (fiberComponent releasedFiber)))
  0 rootDeclares : Elem sharedProvision (dependencies (componentProvisions component))

||| Key-forced locally, or barrier-forced by a root already consumed by the
||| same ordered bundle. The initially empty history is supplied only by the
||| attached wrapper; arbitrary prior roots cannot seed an attached body.
public export
data AttachedReason :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, coreEnd : SystemState name key value world error} ->
  (core : Transitions first coreEnd) -> (priorRoots : List name) ->
  (component : Component key value world error) -> Type where
  KeyReleased :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    {component : Component key value world error} ->
    AttachedRelease name key world error value nameEq selected core component ->
    AttachedReason nameEq selected core priorRoots component
  EarlierForcedRoot :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected, earlier : name} ->
    {first, coreEnd : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    {component : Component key value world error} ->
    (0 earlierInBundle : Elem earlier priorRoots) ->
    AttachedReason nameEq selected core priorRoots component

||| A contiguous trail of checked root OInsert transitions in physical (hence
||| external orchestration) order. History grows only after consuming an
||| authenticated root edge; every new root has actual release/barrier evidence.
||| No arbitrary orchestration or lifecycle edge is admitted to this trail.
public export
data OrderedForcedRootBundle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, coreEnd : SystemState name key value world error} ->
  (core : Transitions first coreEnd) -> (priorRoots : List name) ->
  {bundleStart, finalState : SystemState name key value world error} ->
  Transitions bundleStart finalState -> Type where
  ForcedBundleEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, state : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    OrderedForcedRootBundle nameEq selected core priorRoots (NoTransitions {state})
  ForcedBundleStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, before, middle, finalState : SystemState name key value world error} ->
    {core : Transitions first coreEnd} -> {priorRoots : List name} ->
    (root : name) -> (component : Component key value world error) ->
    (step : Transition before middle) -> (rest : Transitions middle finalState) ->
    (0 inserted : transitionAction step = OInsert root Root component) ->
    (0 forced : AttachedReason nameEq selected core priorRoots component) ->
    (0 tail : OrderedForcedRootBundle nameEq selected core (root :: priorRoots) rest) ->
    OrderedForcedRootBundle nameEq selected core priorRoots (MoreTransitions step rest)

||| Research counterpart of CP3 ActorLifecycleOnly:1786. An extended actor
||| core, optionally followed by an ordered forced-root bundle starting with
||| EMPTY history. Release witnesses lie in that same core, hence physically
||| before every bundled root. No reverse coercion or normalization is claimed.
public export
data ActorLifecycleOnly :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  ActorWithoutForcedRoots :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, finalState : SystemState name key value world error} ->
    (core : Transitions first finalState) ->
    (0 extended : ActorLifecycleCore nameEq selected core) ->
    ActorLifecycleOnly nameEq selected core
  ActorWithForcedRoots :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {selected : name} ->
    {first, coreEnd, finalState : SystemState name key value world error} ->
    (core : Transitions first coreEnd) ->
    (0 extended : ActorLifecycleCore nameEq selected core) ->
    (bundle : Transitions coreEnd finalState) ->
    (0 orderedForced : OrderedForcedRootBundle nameEq selected core [] bundle) ->
    ActorLifecycleOnly nameEq selected (appendTransitions core bundle)
```

### T1.2 — full located/order records (replace CP3:1821–1846 and 1871–1889)

```idris
public export
record LocatedOpenEpisodeBlock
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) where
  constructor MkLocatedOpenEpisodeBlock
  blockPreStart : SystemState name key value world error
  blockStart : SystemState name key value world error
  blockEnd : SystemState name key value world error
  traceBeforeBlock : Transitions initial blockPreStart
  blockOpening : BeginStep nameEq keyEq selected blockPreStart blockStart
  blockBody : Transitions blockStart blockEnd
  0 blockBodyInstalled : InstalledTrace name key world error value nameEq keyEq selected blockBody
  0 blockActorOnly : ActorLifecycleOnly nameEq selected blockBody
  traceAfterBlock : Transitions blockEnd finalState
  0 noEarlierLifecycle : NoLifecycleBy selected traceBeforeBlock
  0 noLaterLifecycle : NoLifecycleBy selected traceAfterBlock
  0 blockActiveAtFinal : supportedActiveAt @{nameEq} selected finalState = True
  0 blockDecomposition : appendTransitions traceBeforeBlock
    (MoreTransitions (beginTransition blockOpening)
      (appendTransitions blockBody traceAfterBlock)) = global

||| CP3:1873 via CP5L2R1ExtendedZeroGap:19, retaining the same exact
||| physical-order equation. The gap starts AFTER the complete attached body;
||| it is not required to be empty.
public export
record BlockBefore
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) (earlierName, laterName : name)
  (earlier : LocatedOpenEpisodeBlock name key world error value nameEq keyEq earlierName global)
  (later : LocatedOpenEpisodeBlock name key world error value nameEq keyEq laterName global) where
  constructor MkBlockBefore
  betweenBlocks : Transitions (blockEnd earlier) (blockPreStart later)
  0 blocksOrderedInGlobal :
    appendTransitions (traceBeforeBlock later)
      (MoreTransitions (beginTransition (blockOpening later)) NoTransitions) =
    appendTransitions
      (appendTransitions (traceBeforeBlock earlier)
        (MoreTransitions (beginTransition (blockOpening earlier)) (blockBody earlier)))
      (appendTransitions betweenBlocks
        (MoreTransitions (beginTransition (blockOpening later)) NoTransitions))
```

### T1.3 — availability-aware predicates and placement (replace CP3:3152–3195; helpers before record)

```idris
public export
rootDeclaredProvisionsFree :
  (name, key, world, error : Type) -> (value : key -> Type) -> (keyEq : DecEq key) ->
  Component key value world error -> SystemState name key value world error -> Bool
rootDeclaredProvisionsFree name key world error value keyEq component state =
  provisionsDisjointFrom {name = name} {key = key} {value = value} {world = world} {error = error} @{keyEq}
    (componentProvisions component)
    (registryFibers {name = name} {key = key} {value = value} {world = world} {error = error} (registry state))

||| Root classification uses the ACTUAL source state for retire/remove.
public export
rootInputAtSource :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  Action name key value world error -> SystemState name key value world error -> Bool
rootInputAtSource name key world error value nameEq (OInsert actor Root component) state = True
rootInputAtSource name key world error value nameEq (OInsert actor (ChildOf parent) component) state = False
rootInputAtSource name key world error value nameEq (ORetire actor) state =
  case lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry state) of
    Nothing => False
    Just fiber => case fiberParent fiber of Root => True; ChildOf parent => False
rootInputAtSource name key world error value nameEq (ORemove actor) state =
  case lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} actor (registry state) of
    Nothing => False
    Just fiber => case fiberParent fiber of Root => True; ChildOf parent => False
rootInputAtSource name key world error value nameEq (LBegin actor) state = False
rootInputAtSource name key world error value nameEq (LAdvance actor) state = False
rootInputAtSource name key world error value nameEq (LDivert actor) state = False
rootInputAtSource name key world error value nameEq (LLeave actor) state = False
rootInputAtSource name key world error value nameEq (LUnload actor) state = False

||| Executable, proof-indexed snapshots. States/actions are runtime data; the
||| exact trace index and duplicate tail token are erased. A false snapshot
||| cannot be attached to a transition whose source has a different state.
public export
data AvailabilityTrace :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {0 first, finalState : SystemState name key value world error} -> (0 trace : Transitions first finalState) -> Type where
  AvailabilityEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    (state : SystemState name key value world error) ->
    AvailabilityTrace name key world error value (NoTransitions {state = state})
  AvailabilityStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {0 middle, finalState : SystemState name key value world error} ->
    (first : SystemState name key value world error) -> (step : Transition first middle) ->
    (0 rest : Transitions middle finalState) -> AvailabilityTrace name key world error value rest ->
    AvailabilityTrace name key world error value (MoreTransitions step rest)

||| A compatible cut preserves declaration availability at EVERY crossed
||| state and crosses NO root input. The endpoint state is checked too;
||| off-end positions reject. This is stricter than a snapshot insertion guard.
public export
rootCutCompatible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> Component key value world error -> Nat ->
  {0 first, finalState : SystemState name key value world error} -> {0 trace : Transitions first finalState} ->
  AvailabilityTrace name key world error value trace -> Bool
rootCutCompatible name key world error value nameEq keyEq component Z (AvailabilityEnd state) =
  rootDeclaredProvisionsFree name key world error value keyEq component state
rootCutCompatible name key world error value nameEq keyEq component (S position) (AvailabilityEnd state) = False
rootCutCompatible name key world error value nameEq keyEq component Z (AvailabilityStep first (Fired _ _ action _ _) rest later) =
  rootDeclaredProvisionsFree name key world error value keyEq component first &&
  not (rootInputAtSource name key world error value nameEq action first) &&
  rootCutCompatible name key world error value nameEq keyEq component Z later
rootCutCompatible name key world error value nameEq keyEq component (S position) (AvailabilityStep first step rest later) =
  rootCutCompatible name key world error value nameEq keyEq component position later

||| Earliest means admissible HERE and no strictly earlier compatible cut in
||| this ACTUAL located birth's prefix, not an arbitrary executable schedule.
public export
record EarliestAvailableRootBirth
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {0 initial, finalState : SystemState name key value world error}
  (0 trace : Transitions initial finalState) (0 root : name)
  (0 component : Component key value world error)
  (0 birth : LocatedActionOccurrence (OInsert root Root component) trace) where
  constructor MkEarliestAvailableRootBirth
  rootAvailabilityTrail : AvailabilityTrace name key world error value (beforeActionOccurrence birth)
  0 rootCurrentCutAvailable : rootCutCompatible name key world error value nameEq keyEq component
    (locatedActionOrdinal birth) rootAvailabilityTrail = True
  0 noEarlierCompatibleRootCut : (earlier : Nat) -> LT earlier (locatedActionOrdinal birth) ->
    rootCutCompatible name key world error value nameEq keyEq component earlier rootAvailabilityTrail = False

||| R178 A8 REPLACEMENT specification, not an adapter to frozen CP3.
||| Integration needs an OWNER choice of research-tower fork or production
||| unfreeze. No conversion to the old strict CanonicalInputPlacement exists.
public export
record CanonicalInputPlacement
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (supportState : SystemState name key value world error) (order : List name)
  {0 initial, originalFinal, finalState : SystemState name key value world error}
  (0 original : Transitions initial originalFinal) (0 trace : Transitions initial finalState) where
  constructor MkCanonicalInputPlacement
  0 placementExternalInputsSame : SameExternalOrchestration nameEq original trace
  0 rootGenerationEarliestAvailable :
    {root : name} -> {component : Component key value world error} ->
    (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
    EarliestAvailableRootBirth name key world error value nameEq keyEq trace root component birth
  0 rootGenerationFresh :
    {root : name} -> {component : Component key value world error} ->
    (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error} root (registry (actionBeforeState birth)) = Nothing
  0 rootGenerationBeforeOwnLifecycle :
    {root : name} -> {component : Component key value world error} ->
    (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
    {action : Action name key value world error} ->
    (lifecycle : LocatedActionOccurrence action trace) ->
    isLifecycleAction action = True -> actionOwner action = root ->
    LT (locatedActionOrdinal birth) (locatedActionOrdinal lifecycle)
  ||| The frozen child-generation clause is retained without strengthening.
  0 childGenerationBeforeOwnLifecycle :
    (n, parent : name) -> Elem n order ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} n (registry supportState) = Just fiber ->
    fiberParent fiber = ChildOf parent ->
    (component : Component key value world error **
     birth : LocatedGeneratedRegistration n parent component trace **
     (lookupFiber @{nameEq} {key = key} {value = value} {world = world}
       {error = error} n (registry (registrationBefore birth)) = Nothing,
      (action : Action name key value world error) ->
      (lifecycle : LocatedActionOccurrence action trace) ->
      isLifecycleAction action = True -> actionOwner action = n ->
      LT (registrationOrdinal birth) (locatedActionOrdinal lifecycle)))
```

### T1.4 — generic least closure and bundle-membership support types (new canonical-definition support)

```idris
public export
data ForcedRootInput : (rootInput, keyForced : Nat -> Type) -> Nat -> Type where
  KeyForces : {rootInput, keyForced : Nat -> Type} -> {ordinal : Nat} ->
    (0 root : rootInput ordinal) -> (0 released : keyForced ordinal) ->
    ForcedRootInput rootInput keyForced ordinal
  OrderForces : {rootInput, keyForced : Nat -> Type} -> {earlier, later : Nat} ->
    (0 prior : ForcedRootInput rootInput keyForced earlier) ->
    (0 root : rootInput later) -> (0 ordered : LT earlier later) ->
    ForcedRootInput rootInput keyForced later

||| Leastness: every set containing key-forced actual roots and closed under
||| strictly later actual roots contains ForcedRootInput. Instantiate rootInput
||| with native root OInsert occurrences, not lifecycle positions or raw names.
export
0 forcedRootLeast : {rootInput, keyForced : Nat -> Type} ->
  (candidate : Nat -> Type) ->
  (0 seeds : (n : Nat) -> rootInput n -> keyForced n -> candidate n) ->
  (0 closed : (earlier, later : Nat) -> candidate earlier -> rootInput later ->
    LT earlier later -> candidate later) ->
  {ordinal : Nat} -> ForcedRootInput rootInput keyForced ordinal -> candidate ordinal
forcedRootLeast candidate seeds closed (KeyForces {ordinal} root released) = seeds ordinal root released
forcedRootLeast candidate seeds closed (OrderForces {earlier} {later} prior root ordered) =
  closed earlier later (forcedRootLeast candidate seeds closed prior) root ordered

public export
record AttachedBundleOccurrence
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState)
  (action : Action name key value world error) (ordinal : Nat) where
  constructor MkAttachedBundleOccurrence
  bundleActor : name
  containingBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq bundleActor global
  coreEnd : SystemState name key value world error
  memberCore : Transitions (blockStart containingBlock) coreEnd
  0 memberExtended : ActorLifecycleCore nameEq bundleActor memberCore
  memberBundle : Transitions coreEnd (blockEnd containingBlock)
  0 memberForced : OrderedForcedRootBundle nameEq bundleActor memberCore [] memberBundle
  0 memberSplit : appendTransitions memberCore memberBundle = blockBody containingBlock
  bundleOccurrence : LocatedActionOccurrence action memberBundle
  bundleOffset : Nat
  0 offsetExact : bundleOffset = transitionCount (traceBeforeBlock containingBlock) + S (transitionCount memberCore)
  0 memberOrdinal : ordinal = bundleOffset + locatedActionOrdinal bundleOccurrence
  0 memberLowerBound : LTE bundleOffset ordinal
  0 memberUpperBound : LT ordinal (bundleOffset + transitionCount memberBundle)

||| Attached normal-form COVERAGE: every actual root-orchestration occurrence
||| in the gap region belongs to an authenticated bundle at the same physical
||| ordinal. This does not postulate NoRootOrchestration. Nonoverlap of bundles
||| and the residual gap is a SEPARATE schedule/decomposition obligation.
public export
record AttachedNormalForm
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState, gapFirst, gapFinal : SystemState name key value world error}
  (global : Transitions initial finalState)
  (gap : Transitions gapFirst gapFinal) (gapOffset : Nat) where
  constructor MkAttachedNormalForm
  0 rootInBundle : (action : Action name key value world error) ->
    (occurrence : LocatedActionOccurrence action gap) ->
    RootOrchestrationStep nameEq (locatedTransition occurrence) ->
    AttachedBundleOccurrence name key world error value nameEq keyEq global action
      (gapOffset + locatedActionOrdinal occurrence)
```

---

# Tier 2 — UNCHECKED specification clauses

**NOT YET SIGNABLE — no compiled definition exists for the connectors below.**
These are proposed Idris record/field TEXT, not checked source, not postulates, and not replacements for a frozen hole. Names introduced here are proposed API names. The generic predicate parameters deliberately expose unresolved links instead of pretending that the current research variants already define them. The owner must sign both their eventual precise instantiation and the producers. No such instantiation/producer is claimed here.

## T2.1 Trace-linked least forced set

`ForcedRootInput` and `forcedRootLeast` are checked in L2R3, but their two predicates are generic. The root predicate must be inhabited only by actual native births, not arbitrary ordinals or raw names. Proposed connector:

```idris
public export
record RootBirthAtOrdinal
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) (ordinal : Nat) where
  constructor MkRootBirthAtOrdinal
  rootName : name
  rootComponent : Component key value world error
  rootOccurrence : LocatedActionOccurrence (OInsert rootName Root rootComponent) trace
  0 rootOrdinalExact : locatedActionOrdinal rootOccurrence = ordinal

public export
record ForcedTraceClassification
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (0 KeyForcedAt : Nat -> Type) where
  constructor MkForcedTraceClassification
  forcedAt : Nat -> Bool
  0 keySeedsAreActual : (ordinal : Nat) -> KeyForcedAt ordinal ->
    RootBirthAtOrdinal name key world error value trace ordinal
  0 forcedSound : (ordinal : Nat) -> forcedAt ordinal = True ->
    ForcedRootInput (RootBirthAtOrdinal name key world error value trace)
      KeyForcedAt ordinal
  0 forcedComplete : (ordinal : Nat) ->
    ForcedRootInput (RootBirthAtOrdinal name key world error value trace)
      KeyForcedAt ordinal -> forcedAt ordinal = True
```

**Unresolved parameter, not a hidden assumption:** `KeyForcedAt` must be instantiated with actual declaration-occupancy/release evidence plus orchestration-order constraints. It cannot be the predicate `forcedAt n = True`, an arbitrary supplied seed set, or the raw catalog membership predicate. L2R5 C8 supplies raw birth lookup completeness; it does not compute `KeyForcedAt`. L2R3 leastness supplies minimality only AFTER this predicate linkage. Stable original occurrence/generation identities must survive the outer normalizer. A classifier indexed by CURRENT ordinals must be transported, not recomputed and silently treated as the original classifier.

## T2.2 Last-release/anchor assignment (key roots and barriers)

The following proposed certificate shape separates the already checked local `AttachedRelease` from the missing global last-release proof. `FreeAtCut` is an **unimplemented executable cut observation** which must be defined by a total scan of the supplied actual AvailabilityTrace (including its endpoint); its correctness is owed. It must test declaration occupancy, not activity or current owned values.

```idris
public export
record LastReleaseCut
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (component : Component key value world error)
  {initial, cutState : SystemState name key value world error}
  (prefixTrace : Transitions initial cutState)
  (trail : AvailabilityTrace name key world error value prefixTrace)
  (FreeAtCut : Nat -> Bool) where
  constructor MkLastReleaseCut
  removedChild : name
  release : LocatedActionOccurrence (ORemove removedChild) prefixTrace
  anchorCut : Nat
  0 anchorIsRemovalEnd : anchorCut = S (locatedActionOrdinal release)
  0 occupiedBefore : rootDeclaredProvisionsFree name key world error value keyEq component
    (actionBeforeState release) = False
  0 availableAfter : rootDeclaredProvisionsFree name key world error value keyEq component
    (actionAfterState release) = True
  0 remainsAvailable : (cut : Nat) -> LTE anchorCut cut ->
    LTE cut (transitionCount prefixTrace) -> FreeAtCut cut = True
```

**Not sufficient in isolation:** tie `FreeAtCut` to `trail`, `release` to the SAME own-child `AttachedRelease`/parent block, and the chosen cut to the least legal position after all earlier external inputs. Occupied-before → available-after plus continuous availability rules out a later reoccupation; it is not alone a complete global selector. Multiple declared keys released by different parents attach to the last releasing block. A barrier root shares a preceding forced root's anchor unless its own later key release raises that anchor. The native L2R4 annotator's `S ordinal` Remove markers cannot be reused as stable IDs when a swap changes removal ordinals; stable release identities need producer-owned transport.

Proposed assignment linkage (the generic obligation parameters are deliberately explicit):

```idris
public export
record ForcedAnchorAssignment
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (0 KeyForcedAt : Nat -> Type)
  (classification : ForcedTraceClassification name key world error value trace KeyForcedAt)
  (0 KeyAnchorCorrect : Nat -> Nat -> Type)
  (0 BarrierAnchorCorrect : Nat -> Nat -> Type) where
  constructor MkForcedAnchorAssignment
  assignedAnchor : Nat -> Maybe Nat
  0 noUnforcedAnchor : (ordinal : Nat) -> forcedAt classification ordinal = False ->
    assignedAnchor ordinal = Nothing
  0 keyAnchor : (ordinal : Nat) -> KeyForcedAt ordinal ->
    (anchor : Nat ** (assignedAnchor ordinal = Just anchor,
                     KeyAnchorCorrect ordinal anchor))
  0 barrierAnchor : (ordinal : Nat) -> forcedAt classification ordinal = True ->
    (KeyForcedAt ordinal -> Void) ->
    (anchor : Nat ** (assignedAnchor ordinal = Just anchor,
                     BarrierAnchorCorrect ordinal anchor))
```

`KeyAnchorCorrect` must consume the trace-authenticated last-release certificate above, not merely a chosen Nat. `BarrierAnchorCorrect` must identify an earlier forced native root, preserve external order, and choose the proper shared/later anchor. These are unresolved connector predicates, **not compiled implementation claims**. L2R3's `KeyReleased`/`EarlierForcedRoot` prove LOCAL justification in a selected core/bundle, not either global predicate.

## T2.3 Front-normal form, including non-insert root orchestration

The front predicate cannot just quantify over OInsert. RootOrchestrationStep also classifies root Retire/Remove. Associate every root action with its actual birth GENERATION through the accepted scanner/origin correspondence; raw-name equality is insufficient after reuse. That association is not implemented by the root-insert catalog.

```idris
public export
record FrontNormalClassification
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (0 KeyForcedAt : Nat -> Type)
  (classification : ForcedTraceClassification name key world error value trace KeyForcedAt)
  (0 RootActionOriginAt : Nat -> Nat -> Type) where
  constructor MkFrontNormalClassification
  0 nonForcedRootActionsFirst :
    {action : Action name key value world error} ->
    (rootAction : LocatedActionOccurrence action trace) ->
    RootOrchestrationStep nameEq (locatedTransition rootAction) ->
    (birthOrdinal : Nat) -> RootActionOriginAt (locatedActionOrdinal rootAction) birthOrdinal ->
    forcedAt classification birthOrdinal = False ->
    {lifeAction : Action name key value world error} ->
    (life : LocatedActionOccurrence lifeAction trace) ->
    isLifecycleAction lifeAction = True ->
    LT (locatedActionOrdinal rootAction) (locatedActionOrdinal life)
```

`RootActionOriginAt` is an unresolved generation-origin relation to be linked to the accepted scanner. The outer normalization induction must PRODUCE this front-normal certificate, not accept its desired conclusion disguised as a new hypothesis. For inter-block coverage, a further **non-insert root-action disposition** is needed: prove root Retire/Remove cannot remain inside the designated gaps. Do not silently infer that every forced root action is a root insertion. The grammar has no constructor attaching root Retire/Remove to a trailing insertion bundle. The exact disposition of forced-root controls is still an owner/research obligation; this draft does not settle it by an over-strong universal front clause.

## T2.4 Bundle-placement linkage and selector projection

Do not redefine RootInputsBeforeLifecycle to mean 'zero gap'. Replace its old unqualified use by front-normal classification plus trace-authenticated assignment/placement. Proposed field extensions to the Tier-1 availability-aware CanonicalInputPlacement (all referenced connectors here remain UNCHECKED):

```idris
  -- Existing original/trace indices and all Tier-1 clauses retained.
  -- The following are candidate specification fields, NOT compiled fields.
  0 forcedClassification : ForcedTraceClassification name key world error value
    trace KeyForcedAt
  anchorAssignment : ForcedAnchorAssignment name key world error value trace
    KeyForcedAt forcedClassification KeyAnchorCorrect BarrierAnchorCorrect
  0 frontNormal : FrontNormalClassification name key world error value nameEq
    trace KeyForcedAt forcedClassification RootActionOriginAt
  0 forcedBirthPlacement :
    {root : name} -> {component : Component key value world error} ->
    (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
    forcedAt forcedClassification (locatedActionOrdinal birth) = True ->
    AttachedBundleOccurrence name key world error value nameEq keyEq trace
      (OInsert root Root component) (locatedActionOrdinal birth)
  0 placementUsesAssignedAnchor :
    {root : name} -> {component : Component key value world error} ->
    (birth : LocatedActionOccurrence (OInsert root Root component) trace) ->
    (forced : forcedAt forcedClassification (locatedActionOrdinal birth) = True) ->
    AnchorMatchesMember anchorAssignment birth (forcedBirthPlacement birth forced)
```

`KeyForcedAt`, `KeyAnchorCorrect`, `BarrierAnchorCorrect`, `RootActionOriginAt`, and `AnchorMatchesMember` require explicit binding/definitions in the eventual complete record. They are **intentionally unresolved parameters in this draft**, not globally available Idris declarations. `AnchorMatchesMember` must connect the SAME catalog member's actual core/bundle decomposition to the assigned stable release. Core ending immediately after the last freeing Remove and ordered bundled births are structural obligations, not just an arithmetic label. An owner cannot sign this fragment as a typechecked patch.

Additional proposed selector input shape, separate from CanonicalInputPlacement until derivable:

```idris
  0 gapRootAssignments :
    (action : Action name key value world error) ->
    (occurrence : LocatedActionOccurrence action gap) ->
    RootOrchestrationStep nameEq (locatedTransition occurrence) ->
    AttachedBundleOccurrence name key world error value nameEq keyEq global action
      (gapOffset + locatedActionOrdinal occurrence)
```

This is precisely the missing all-occurrence assignment obligation, not a produced field in L2R5. It must follow from front-normal form, non-insert-root disposition, actual placed bundles and authenticated gap embedding; it cannot be justified by C8's raw catalog alone. Then use unchanged L2R3 `attachedZeroGapInNormalForm` with residual-head coverage, physical/offset equations, AttachedNormalForm and UNIVERSAL interval separation. L2R4 discharges those premises only for the two specified fixture gaps. No general selector zero-gap theorem closes here.

## Iteration type/measure status

There is **NO compiled iteration theorem** in L2R5. Proposed obligation shape, not a declaration or an assumed callback:

```idris
  normalizeAttached :
    (input : AdmissibleFrontNormalizationInput name key world error value nameEq keyEq) ->
    AttachedNormalizationResult name key world error value nameEq keyEq input
```

Both proposed types are UNDEFINED connectors. The input must authenticate the real original trace, external-order root enumeration, generation/release assignment and admissible-current-cut facts. The result must own an actual checked output trace; RegistryExtensional endpoint; preserved external order/origins; produced front-normal form, legal terminal earliest births, placed bundles/coverage and anchor-zero proof. A function from an assumed per-step swap oracle or supplied zero result is NOT this theorem.

Outer induction: root inputs in orchestration order. Inner induction: actual physical DISTANCE to the allowed front/bundle position, decreasing for each permitted native crossed edge. Do not drive this with anchor inversions alone (`Life; unrelated Retire; Birth`), and do not forbid child inserts merely to recover ordered snapshot equality. L2R5 proved the faithful pointwise endpoint relation and fresh-insert endpoint algebra, but not original-edge-only Insert/Insert alternate applicability, general extensional evaluator transport, swap existence or distance iteration. Thus neither direction of a zero ⇔ attached-normal-form theorem for iteration-produced traces is proved. Existing fixture zeros and actual local swaps retain their original exact scope.


## Root orchestration and O19 reading (statements not silently weakened)

CP3:2000–2034 RootOrchestrationStep and :2055–2091 SameExternalOrchestration are **UNCHANGED**, including root Retire/Remove classification and exact relative order. Child Insert/Retire/Remove remain internal only with their existing provenance disciplines. Forced roots are still external root inputs even when physically attached to a parent's block. Never reverse R/S to manufacture all-root-first placement. CP3:2048–2053 old RootInputsBeforeLifecycle is NOT simply relabeled: its unrestricted canonical use must be replaced by Tier-2 front-normal scope. Keep it as the strict predicate while old statements remain frozen; eventual removal/replacement requires the owner-approved dependent migration, not a false coercion.

O19 source `research/DGamma/CP5O19SurfaceSpike.idr:113–145` contains the exact field:

```idris
  0 safetyBlocksAdjacent : (transitionCount (betweenBlocks safetyBlocksOrdered) = 0)
```

**Keep this text and its strength.** After rehome, `safetyBlocksOrdered` (:130–133) compares the FULL attached bodies. `betweenBlocks` begins after the trailing forced bundle, never after only the lifecycle core. List adjacency alone is not physical adjacency. `safetyRightOpeningEarly` (:140–144), no-generated-child constraints (:134–139), registration provenance and native replay remain required. The rehome does not prove their preservation for forced roots. Do not edit O19 this shift; migration must recheck every consumer. L2R4 small/barrier applications use actual physical offsets, universal no-straddling and honest residual-gap NF; arbitrary selector zero-gap remains open.

## Statement-fidelity table and frozen declaration inventory

`O6-L2R5-CP3-STATEMENT-FIDELITY.json` enumerates **DIRECT signature** references to changed canonical types/predicates in src/, research/, and retained L2R1–L2R4 source trees, with file, declaration, old line, referenced canonical names and statement SHA256. The extraction excludes body-only references; it is not an exhaustive transitive typechecker. No listed statement was edited. After owner approval, regenerate against the exact production base and include transitive import rebuild coverage.

| Frozen declaration/family | Fidelity under proposed rehome | Required disposition (no edit here) |
|---|---|---|
| CP3 ActorLifecycleOnly + its constructors | INCOMPATIBLE API/domain: new nameEq index, core + bundled roots, new constructors | No old theorem body may be counted as proved without new cases |
| CP3 LocatedOpenEpisodeBlock / prefixToBlockOpening / prefixThroughBlock / BlockBefore | Same physical decomposition meaning, enlarged body; explicit proof erasure delta | Recheck every construction/structural induction; no zero by definition |
| CP3 CanonicalInputPlacement / CanonicalSchedule | Original-trace index added; strict global-before-lifecycle replaced by current availability/terminal earliest + pending front-normal connectors | Exact signature migration; no implicit coercion from revised to strict placement |
| CP3 ConfluenceResult / confluenceTheorem | Text unchanged; canonical schedule field semantics change transitively; final pointwise/vestigial relations unchanged | Revalidate theorem correspondence and call sites; no new proof claim |
| CP3StatementChecks canonical constructors/projections (:3398–3445,3548–3549,3586–3738) | Constructor fields/grammar matches become incompatible | Adapt only under owner signature, then serialized recheck |
| CP5ConfluenceCanonicalSortSpike root-hoist/initial-placement/O17 statements | Canonical schedule/input-placement references change; frozen holes remain holes | Availability + outer-order/distance proof required; do not relabel a conditional fold |
| CP5O19SurfaceSpike ActorBlockDecomposition / AdjacentActorSwapSafety / actorBlockTrace | Larger attached blocks; adjacency field exact strength unchanged | Native safety and selector projections must use entire block; general zero-gap debt visible |
| CP5O19OriginalBlockClassSpike / CP5O19ReachedBlocksSpike | Old grammar inductions no longer exhaustive | Own-child controls and forced-root bundle cases need proofs |
| CP5O20InversionChildSafetySpike / CP5O20RightOpeningTransportSpike | Frozen O20 statements indirectly reference new blocks; old two-constructor inductions incompatible | Do not weaken statements or consume unproved cases; distinct main-lane owner gate |
| CP5ConfluenceCrossTraceSpike / CP5ConfluenceRenamingCompositionSpike canonical-capital references | Transitive schedule meaning changes, endpoint historical/current-name distinction unchanged | A11 supported/history repair remains separate; no fresh current-name equation for removed births |
| CP5ActorLifecycleOnlyExtended.actorLifecycleOnlyIntoExtended and L2R3Attached.oldIntoAttached | Their domain currently names the OLD ActorLifecycleOnly; rehome changes that name's meaning | Cannot blindly reuse forward inclusion as a reverse attached→core coercion; owner must revise research migration strategy |
| All remaining direct frozen signatures | See machine inventory, one row per declaration | Typechecked revalidation required; byte equality here is not future proof validity |

## Serialized seeded rebuild plan / R196 coordination

Pointer: `O6-R192-CP3-REBUILD-INVENTORY.json` (old PLAN ONLY: 163 src,90 research,154 research-tests affected-module entries; baseline34b21c9, frozen CP3 blob recorded there), plus the protocol in `O6-R192-A8-A10-DECISION-MEMO.md`. This is not evidence of any L2R5 compiler series. R196 main-lane LocalDiamond producer-contract work and its expected241-module serialized recheck are concurrent; **no completed R196 receipt is available to this draft**. Obtain the owner's exact R196 experience/peak/failed-module/resume receipts before scheduling CP3 unfreeze. Do not access/build the main worktree from this lane.

Before owner-signed production change: refresh the import/signature inventory at the actual base; freeze old/new CP3 hashes, exact symbol/quantity/statement map and leaf-before-dependent plan; preserve build/ and seeded TTCs. Acquire shared `/tmp/dgamma-heavy.lock` with JSON owner for ≥19GiB checks. Run one detached/monitored compiler at a time,48GiB hard RSS stop, exact target Building line/hash/mtime receipt, no mass touch/deletion/cold rebuild. Compile changed CP3 with seeded prerequisites, then affected production modules, then research consumers in dependency order. If a single module approaches48GiB, stop/gate and redesign rather than retry a from-scratch package (historical ~138GiB wall). Negative fixtures require frozen symbol+diagnostic contracts, not exit-only acceptance. A monitored seeded package pass is only a final separately authorized validation, not a fallback.

**Main-lane fix candidate, NOT a lane edit:** lifecycle replay roles need an observed retired-head guard at the source. L2R4 B7 and L2R5 B5 both exhausted3/3; the new explicit-Bool observation record still cannot produce the native retired-head equation due to hidden dependent projection indices. A base-module producer-owned observed guard (not another wrapper) needs an owner-gated source design/change and its serialized dependent rebuild, informed by R196. No requested source edit is made here.

## Review/owner decision

Tier 1 is proposed exact syntax backed by the cited variant declarations, not a fresh CP3 PASS. Tier 2 remains a design/specification debt. Do not sign this as a complete production unfreeze until native normalizer existence/transport, trace-linked classification/assignment, lifecycle replay, full front-normal/placed-gap coverage and general selector zero-gap are resolved or the owner explicitly narrows what the production specification promises. No frozen theorem or conclusion is silently weakened in this draft.
