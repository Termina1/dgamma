# Revision-22 quietness/no-failure audit — invalid R20 source fixture stop

Authorized base: `cp5-thm73-scoping@3871d53`.

## Stop decision

The pointwise control relation is sufficient to reconstruct target-domain
membership one binding at a time; it does not immediately require a new detached
registry-domain premise.  Lifecycle controls also preserve the local
no-failure predicate constructively.

The R20 whole-bundle checkpoint nevertheless cannot proceed to quietness for a
more fundamental reason: its alleged authenticated **source** trace is not
quiet.  The local pair inserts actors 1 and 2 as fresh `Inactive Nothing` roots,
and the suffix retires only actor 0.  For an empty-dependency component,
`targetFiber` of each non-retired fresh root resolves to `Just EmptyView`.
`quietFiber` for `Inactive Nothing` requires `isNothing targetFiber`, so actors 1
and 2 are not quiet.

`r22R20SourceBundleImpossible` proves constructively that no
`ReplayInvariantBundle` can index the exact R20 source trace.  This is earlier
than any target quietness transport obligation.  Per the field-by-field and
no-output-capital rules, work stops here.  No combined interface gate is issued.

## 1. Pointwise target-domain reconstruction passes

`R22QuietnessDomainAuditPositive` defines
`ControlledSourceForTarget`. Given:

```idris
controls : ControlEquivalent ... source target
lookupFiber selected (registry target) = Just targetFiber
```

`controlEquivalentTargetHasSource` rewrites the exact pointwise relation at
`selected` to a right-`Just` index. The only inhabitable constructor is
`SomeControlFibers`, yielding:

```idris
sourceFiber : Fiber ...
lookupFiber selected (registry source) = Just sourceFiber
FiberControlRelated sourceFiber targetFiber
```

Thus a target-list induction can recover a source witness for every target head
without caller-supplied list correspondence. `NoControlFibers` is eliminated by
the dependent right-`Just` index, not by proof irrelevance.

This closes the specific hard-stop question about raw registry-domain
membership: pointwise controls already encode presence/absence equivalence for
every name. No new endpoint domain field is justified by this checkpoint.

## 2. Lifecycle case audit

`lifecycleQuietUsesTarget` classifies all lifecycle constructors:

| Lifecycle | Executable quiet branch | Needs target resolution? |
|---|---|---|
| `Inactive (Just error)` | `True` | no |
| `Inactive Nothing` | `isNothing targetFiber` | yes |
| `Reloading ...` | `False` | no |
| `Active ... view` | `targetMatches targetFiber view` | yes |
| `Unloading ...` | `False` | no |

`lifecycleControlPreservesQuietTargetMode` checks all four
`LifecycleControlRelated` constructors and proves both related sides select the
same branch class. In particular, outcome equality distinguishes failed from
clean inactive states, and view equality is retained for active states.

A complete generic quietness theorem would still need target-resolution
agreement in the two marked cases. That proof would use:

- shared component/dependency indices from `FiberControlRelated`;
- retirement equality;
- exact per-actor effect tables from `EffectStateRelated`;
- pointwise active/lifecycle controls;
- both registry well-formedness proofs, especially pairwise provision
  disjointness; and
- the target-domain witness above.

This bridge remains worthwhile for later valid fixtures, but it cannot repair a
source trace that violates its own `replayQuiet` premise.

## 3. No-failure local and domain probes pass

`fiberControlPreservesNotFailed` checks every lifecycle relation constructor:

- equal inactive outcomes preserve failure/non-failure exactly;
- reloading, active, and unloading are all non-failed on both sides.

`targetEntryNotFailedFromSource` combines target-domain reconstruction with
`noFailureFromState` and the per-fiber equality. For any concrete target lookup,
source whole-state no-failure yields target-fiber no-failure.

Therefore no-failure's local lifecycle and per-target-head obligations are
constructible from current pointwise controls. A routine finite target-list fold
would finish the global Boolean once a valid source bundle exists. No-failure is
not advanced as a `ReplayInvariantBundle` field here because quietness fails
first and strict declaration order is retained.

## 4. Exact R20 counterexample

The R20 schedule is:

```text
OInsert 0 Root
OInsert 1 Root
OInsert 2 Root
ORetire 0
```

All three insertions use the empty-dependency component. The final registry
starts with actor 2's fresh non-retired fiber, followed by actor 1 and retired
actor 0.

`r21FreshFiberNotQuietAtOriginal` checks:

```idris
quietFiber r20Fiber (registry r20OriginalFinal) = False
```

The proof is executable reduction after importing `Data.Maybe`: the fiber is
`Inactive Nothing`, not retired, and resolution of `[]` is
`Just EmptyView`.

`r21OriginalRetireFinalNotQuiet` lifts that false head through the concrete
`allRecursive` registry fold:

```idris
quiet r20OriginalFinal = False
```

`r22OriginalWholeTrace` is the exact four-node source trace. Finally:

```idris
r22R20SourceBundleImpossible :
  ReplayInvariantBundle ... r22OriginalWholeTrace -> Void
```

combines `replayQuiet bundle : quiet r20OriginalFinal = True` with the checked
false equality to derive `True = False`.

This is a positive total impossibility theorem, stronger than an elaboration
failure. It accepts no desired target field and relies on no postulate or escape
hatch.

## 5. Consequences for prior checkpoints

The revision-21 record `R21WholeBundleThroughFinalWellFormed` remains accurate:
it packages exactly the first five field **shapes** after assuming the future
producer-carried O5 alignment. It did not claim or consume a source bundle.
Revision 22 shows that it cannot be extended to `ReplayInvariantBundle` for this
concrete schedule.

`R21WholeBundleQuietTransportNegative` is retained as a historical generic
shape pin only. Its `source and target` mismatch is no longer the active R20
blocker; source quietness is unavailable before endpoint transport is relevant.

The earlier cross-state retire replay remains genuine and useful. What fails is
the choice of final source schedule for a whole-bundle fixture, not checked
cross-state applicability, RAR, endpoint, occurrence, or ordinal capital.

## 6. Required fixture correction

A valid replacement fixture must end quiescently on both source and replayed
sides while preserving the same authenticated local pair and cross-state replay
standard. The smallest plausible correction extends the suffix so actors 1 and
2 also reach quiet, non-failed states, for example by checked retirement of both
fresh roots:

```text
... local pair ...
ORetire 0
ORetire 1
ORetire 2
```

Retired clean inactive fibers have `targetFiber = Nothing`, hence are quiet and
non-failed. Each additional suffix action must be replayed cross-state with the
same producer standard as the existing actor-0 retire: checked transition,
RAR, relational endpoint, action/generated occurrence correspondence, relative
ordinal, and exact outer alignment at whole-bundle construction time.

This is only a candidate. Before implementation, the corrected fixture must
also be checked against revision-18 pair-local `SameExternalOrchestration`.
The current distinct root/root local transposition is known not to preserve the
external root subsequence. If that relation rejects the fixture—as expected
from the R17 root/root impossibility—the local pair must instead be replaced by
an O6-applicable internal crossing rather than passing whole external order as
caller capital.

No desired quietness, no-failure, domain relation, or external-order field may
be accepted as a loose premise.

## 7. Combined package status

The prepared combined package remains unchanged and blocked:

A. erased exact `movedPairAligned` on `LocalRelationalDiamond`;
B. promoted bundle-free `SealedSuffixReplaySpine`;
C. opaque nine-plus-two `AdjacentSwapResult`; and
D. false generic occurrence-fold hole retirement with
   `adjacentSwapSuffixSpike` byte-for-byte unchanged.

All genuine moved-alignment producers remain closed. No new domain field is
added to the package because pointwise target-domain reconstruction passed.
The package cannot be issued until a corrected O6-applicable fixture constructs
the entire whole `ReplayInvariantBundle` end-to-end.

Hole count remains 21. The forecast remains suspended at 21 -> 20 -> 19.

## 8. Re-estimate

The prior 21–35 band assumed the R20 four-node schedule was a valid source
bundle. Replacing it with a quiescent, revision-18-applicable fixture and replaying
additional checked suffix heads adds a distinct fixture-redesign phase.
Remaining O6 estimate is revised to **25–42 implementation shifts**:

| Phase | Shifts |
|---|---:|
| Corrected quiet/non-failed and external-order-applicable fixture design | 3–6 |
| Additional checked cross-state suffix heads and sealed spine | 3–5 |
| Generic quiet/target-resolution transport for recursive cases | 3–5 |
| Remaining whole-bundle fields after no-failure | 5–8 |
| Combined atomic boundary and manifest migration | 3–5 |
| Arbitrary suffix integration and remaining action families | 5–8 |
| Adversarial review closure | 3–5 |
| **Total** | **25–42** |

The next checkpoint is an authenticated source `ReplayInvariantBundle` for a
quiescent O6-applicable adjacent pair, before any target bundle transport.

## 9. Scope closure

No frozen declaration, O6 body, manifest, production file, CP3 file, or package
file changes in this phase. The only fixture changes are checked diagnostics and
test-local probes. The combined gate is not requested.

## Status

- Target-domain reconstruction from pointwise controls: passed.
- Lifecycle quiet branch classification: passed.
- Per-fiber no-failure preservation: passed.
- Per-target-head no-failure reconstruction: passed.
- R20 source quietness: constructively false.
- R20 source `ReplayInvariantBundle`: constructively impossible.
- Target quietness transport: not applicable until fixture correction.
- Combined interface gate: prepared but not issued.
- Remaining estimate: 25–42 shifts.
