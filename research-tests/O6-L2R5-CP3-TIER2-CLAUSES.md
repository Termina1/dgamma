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
