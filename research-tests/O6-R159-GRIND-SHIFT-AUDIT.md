# O6 R159 — generalized seam grind-shift stop audit

## Coordinate, ruling, and scope

R159 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`234b0a04ec8ddd7ddd6a98a3e4d6712b5c074fca`.  The tracked tree was clean; the
only initial untracked paths were the permitted `paper/` directory and
`review-o6-body-adversarial.md`.  Both remain untouched and untracked.

`O6-R158-GRIND-SHIFT-AUDIT.md` was read first, followed by the governing
`O6-R146-STRATEGY-MEMO.md`.  The R158 diagnostic trail was resumed at the
public import/signature boundary and advanced through the retained-lifecycle
body.  All retained Idris changes are research-side in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`; production `src/` and
`dgamma.ipkg` remain byte-identical to the frozen production coordinate.

No retained declaration calls `deletionTheoremProof`, derives or casts
`NoDependentClosingEpisode` from `NoDependentClosingEpisodeForGeneration`, or
casts the scoped seam to the frozen raw provider-evidence interface.  O14,
O17, O19, and the O21 withdrawal branches were not edited.  No build artifact
or `build/` path was deleted.  Every compiler invocation was preceded by an
orphan-process kill, and only one Idris process ran at a time.  Fresh checks
were forced only by source timestamps.

## Unit A — retained lifecycle seam completed

### Direct public-surface closure

The R158 terminal diagnostic named `ForeignRetainedEpisodeStep`, but resolving
that result exposed several more transitive names used by the body.  Each
direct import was landed and checked as its own one-invocation micro-unit:

- `CP4DeletionSelectedForeignLifecycleStep` (`be8803d`);
- `CP4DeletionControlPlan` (`f63aa8c`);
- `CP4DeletionBoundaryLifecycleCore` (`34d0acd`);
- `CP4DeletionBoundaryRetained` (`b9d8e7e`);
- `CP4DeletionSelectedForeignOrchestrationStep` (`b88d7e7`);
- `CP4DeletionGenerationFilter` (`8f00b7c`);
- `CP4DeletionSelectedForeignControlCore` (`dcb0d71`);
- `CP4DeletionSelectedForeignTables` (`aa6cf7d`);
- `CP4DeletionSelectedEffectCore` (`033c6a8`);
- `CP4DeletionNoEpisodeReplay` (`0d5d5fd`); and
- `CP4RecoveryTrace` (`da47255`).

The diagnostics advanced monotonically from the R158 chain through
`ForeignRetainedEpisodeStep`, `namedAfter`, `namedFireProjectsRaw`, and
`modelFiber`.  No semantic proposition was rejected.

### Checked retained replay

`ScopedForeignLifecycleExclusion` (`d8e14ae`) names the fully explicit,
zero-hidden specialized callback.  In particular its `action`, `before`,
`survivor`, whole trace, and boundary indices are explicit at use sites; this
closed a real hidden-index mismatch found by the checker.

`retainedForeignLifecycleFromScopedOwner` (`42c1adc`) is the one-elimination
continuation after the plan-side owner has been located.  It:

- obtains the survivor owner from the ordered control relation;
- reconstructs exact source and selected lookup equations from the inactive
  deletion plan;
- invokes `scopedForeignLifecycleControlsFromExclusion` with the direct Boolean
  leaf;
- transports the survivor state index exactly; and
- packages the checked `ForeignRetainedEpisodeStep`.

The owner continuation used its complete 3-invocation budget: the first
attempt exposed the missing public `modelFiber` surface, the second exposed an
unconstrained implicit `action` in the initial alias use, and the third passed
after importing `CP4RecoveryTrace` and making every alias index explicit.

`retainedForeignLifecycleFromScopedExclusion` (`4fff03d`) then passed in one
invocation.  It performs only the owner-presence elimination and delegates to
the checked continuation.  This closes the exact R158 retained-lifecycle
clause without a raw dependency predicate.

## Unit B retained prefix — generalized local fold infrastructure

The following checked micro-units remain as a safe prefix toward the
generalized selected fold:

- direct `CP4DeletionSelectedEpisodeFoldCore` import (`3eba99e`);
- `ScopedLocatedRegistrationStep` (`17f0e1b`), retaining the exact suffix and
  occurrence-local `RegistrationStepDiscipline`;
- `scopedRegistrationDisciplineAtOccurrence` (`ec7f175`);
- direct `CP4RecoveryModelTrace` import (`0941a9f`);
- research-side `scopedSelectedPlanExactBoundary` (`93e1980`), re-derived
  because the frozen defining helper is private;
- `scopedRetainedNoEpisodeBoundaryStep` (`fe9f81f`), which passed on attempt
  3/3 after the occurrence-embedding import and private-helper re-derivation;
- `scopedForeignRetainedHead` (`7883f08`);
- direct `CP4DeletionRetainedAction` import (`fea03f9`);
- `scopedSelectedSourceOutsidePlan` (`ba7a618`);
- `scopedLifecycleNonInsert` (`41e7d08`);
- direct `CP4DeletionIndependenceRestriction` import (`65a164e`);
- `scopedForeignLifecycleRetainedHead` (`fe54642`), passing on attempt 2/3
  after its direct independence-restriction import;
- `scopedForeignOrchestrationRetainedHead` (`bc1629a`);
- exhaustive eight-action `scopedDispatchForeignRetainedHead` (`3491e4a`);
  and
- `scopedFalseNotTrue` (`667888a`), the checked Boolean contradiction needed
  by the next selected-owner insertion clause.

Every retained helper has a fully explicit top-level signature.  There is no
retained local `let`, `where`, or `with` definition; the helpers use at most
one explicit elimination each.  The eight action clauses are top-level
constructor clauses.  No nonlinear pattern or inferred local view was added.

### Clause map after R159

| Generalized seam clause | Status |
|---|---|
| occurrence-scoped provider surface | checked in R158 |
| direct scoped exclusion control dispatcher | checked in R158 |
| exact state/control transports and L-Advance outcomes | checked in R158 |
| raw-free retained foreign lifecycle replay | **checked in R159** |
| occurrence-local registration discipline and exact retained plan step | **checked in R159** |
| foreign orchestration/lifecycle retained dispatch | **checked in R159** |
| selected-owner retained dispatch | stopped at first insertion contradiction helper |
| assembled `SelectedEpisodeLocalReplayer` | not reached |
| generalized selected interior/closed fold | not reached |
| raw-free post-close lifecycle/fold | not reached |
| combined generalized deletion theorem | not reached |

## Binding stop micro-unit — selected insertion contradiction failed 3/3

The next top-level helper was the research-side analog of the frozen private
`insertAbsentNotInstalled`.  It was needed to close the selected-owner
`OInsert` branch without a local `with` block.  Its proposition is the direct
computational contradiction between

```text
lookupFiber actor source = Nothing
```

and

```text
installedAt actor (MkSystemState ambient source) = True.
```

The strict three-invocation budget was exhausted:

1. Rewriting the installed proof by the lookup equation was rejected because
   the elaborated target had already been constrained to `False = True`; the
   rewrite reported that it did not change that target.
2. Passing the installed proof directly to `scopedFalseNotTrue` exposed the
   unresolved reduction from `installedAt`'s lookup case to `False`.
3. An explicit `replace` over the lookup result reached the precise eta wall:
   the checker would not identify the lookup in
   `registry (the (SystemState ...) (MkSystemState ambient source))` with the
   lookup over `source` in the replacement motive.

The uncommitted helper was restored immediately after attempt 3.  No failed
source or probe remains.  This is an exact state-eta/elaboration wall in a
tractable selected-owner clause, not structural-impossibility evidence for
route B and not evidence against the scoped lifecycle proposition.  The next
shift should first land a one-elimination state/lookup eta helper (or a
fully-instantiated installed-at projection) as its own micro-unit, then resume
the selected-owner dispatcher.  R159 therefore does not invoke the memo's
semantic-route-change condition.

Because Unit B stopped before an assembled selected fold, the ordered protocol
correctly left the post-close fold and O9/O10/O11 unopened.

## Micro-unit ledger

| Declaration / surface | Attempts | Commit | Outcome |
|---|---:|---|---|
| eleven Unit-A direct imports listed above | 1 each | `be8803d`..`da47255` | retained |
| pre-factoring retained lifecycle monolith diagnostics | 2 | — | advanced import/name closure; reverted |
| `ScopedForeignLifecycleExclusion` | 1 | `d8e14ae` | retained |
| `retainedForeignLifecycleFromScopedOwner` | 3 | `42c1adc` | retained |
| `retainedForeignLifecycleFromScopedExclusion` | 1 | `4fff03d` | retained; Unit A complete |
| Unit-B fold-core import | 1 | `3eba99e` | retained |
| `ScopedLocatedRegistrationStep` | 1 | `17f0e1b` | retained |
| `scopedRegistrationDisciplineAtOccurrence` | 1 | `ec7f175` | retained |
| occurrence-embedding import | 1 | `0941a9f` | retained |
| `scopedSelectedPlanExactBoundary` | 1 | `93e1980` | retained |
| `scopedRetainedNoEpisodeBoundaryStep` | 3 | `fe9f81f` | retained |
| `scopedForeignRetainedHead` | 1 | `7883f08` | retained |
| retained-action import | 1 | `fea03f9` | retained |
| `scopedSelectedSourceOutsidePlan` | 1 | `ba7a618` | retained |
| `scopedLifecycleNonInsert` | 1 | `41e7d08` | retained |
| independence-restriction import | 1 | `65a164e` | retained |
| `scopedForeignLifecycleRetainedHead` | 2 | `fe54642` | retained |
| `scopedForeignOrchestrationRetainedHead` | 1 | `bc1629a` | retained |
| `scopedDispatchForeignRetainedHead` | 1 | `3491e4a` | retained |
| `scopedFalseNotTrue` | 1 | `667888a` | retained |
| selected insertion absence contradiction | 3 | — | reverted; binding stop |
| selected local replayer / generalized selected fold | 0 | — | not reached |
| generalized post-close replay/fold | 0 | — | not reached |
| O9 `enrichDeletionChainStepSpike` body | 0/3 | — | not opened |
| O10 `deleteClosingEpisodesCoreSpike` body | 0/3 | — | not opened |
| O11 `assembleClosingFreeAccountingSpike` body | 0/3 | — | not opened |

Every passing declaration was checked before commit.  No micro-unit exceeded
three compiler invocations.

## O9/O10/O11 and hole census

The generalized selected/post-close fold producer is still incomplete, so O9
was not opened.  The mandatory order consequently kept O10 and O11 unopened.
There is no audited structural-impossibility park of O9: the retained lifecycle
seam and all foreign retained dispatch clauses now typecheck.

Hole delta is **0**.  The canonical census remains **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

The DeletionChain holes remain exactly:

- `enrichDeletionChainStepSpike`;
- `deleteClosingEpisodesCoreSpike`; and
- `assembleClosingFreeAccountingSpike`.

## Fresh checks and frozen invariants

Freshness was forced by source timestamps only.

```text
Idris 2, version 0.8.0

DeletionChain direct check:
  2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
  exit 0

R11DeletionCertificateProjectionPositive:
  1/1: Building DGamma.R11DeletionCertificateProjectionPositive
  exit 0

R11DirectDeletionStepCloneNegative:
  compiler exit 1
  intended diagnostics present:
    cloneDeletionStepWithAlternateMap
    occurrences and alternate

seeded production package closure:
  207/207: Building DGamma.CP4ProgressProof
  exit 0

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

dgamma.ipkg blob:
  da0c007ee08c4648e459296eb6f0e72a40e2ac89

DeletionChain research blob before this audit:
  843274c893cd9933a85fe2138b15b006857a5dc4

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (git diff --quiet exit 0)

local-diamond diff from R159 start 234b0a0:
  empty (git diff --quiet exit 0)

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The adjacent hashes were freshly recomputed with the frozen R128 convention.
`git diff --check` passes.  The retained R159 delta contains no `believe_me`,
`assert_total`, postulate, unsafe operation, `partial`/`covering` annotation,
local `let`, or `with` block.  `%default total` remains in force.  Apart from
this audit before commit, the only untracked paths are the two permitted
initial artifacts.

## Gate verdict

**STOP in Unit B at the selected-owner insertion contradiction after its strict
3/3 budget.**  Unit A is complete.  R159 also retains the exact registration,
plan, and foreign retained-dispatch prefix needed by the generalized selected
fold, but it did not assemble the selected local replayer or selected fold.
The post-close fold and O9/O10/O11 were therefore correctly left unopened.
The stop is an elaboration/eta boundary and does not justify a semantic route
change or an owner-level production unfreeze request.
