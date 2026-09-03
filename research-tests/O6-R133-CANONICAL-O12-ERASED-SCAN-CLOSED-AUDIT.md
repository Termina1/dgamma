# O6 revision 133: Canonical O12 erased-scan closure audit

## Coordinate and ruling

This continuation began at the supervisor-accepted R132 stop gate
`1f9b19bc3c416c5a05a0ce71ef8bd3eb3edb6a70` on
`cp5-thm73-scoping`.  R132's disposable copy-probe was ruled dispositive:
`Transitions.MoreTransitions` hides its middle state at quantity 0, so an
executable/runtime scan cannot repackage that state.  All further runtime scan
designs for O12 were banned.

The authorized replacement was one fully erased proof-level scan/view unit,
with no runtime-relevant consumer, zero `with` blocks in the scan, dedicated
top-level decision eliminators, and complete telescopes.  If that route landed,
O12 could proceed in normal CanonicalSort dependency order.

## Retained erased scan

Commit `15380a3` (`add erased canonical lifecycle view`) adds:

- public indexed family `ErasedFirstLifecycleView`;
- exact `End`, `Here`, actor-skip, and non-lifecycle-skip constructors;
- constructor arguments at quantity 0, retaining the exact indexed transition,
  its hidden middle and stored dictionaries through the transition value, and
  the exact suffix/decomposition through the family index;
- erased ordinal projection `erasedLifecycleViewOrdinal`; and
- total quantity-0 covering producer `erasedFirstLifecycleView`, with owner and
  lifecycle decisions split into `erasedLifecycleActorDecision` and
  `erasedLifecycleActionDecision`.

The scan region contains no `with (` syntax.  The covering producer checked on
attempt **1/3**, confirming the R132 quantity diagnosis.

## Ordinal and episode bridge

The proof-level scan was connected to O12 in four lemma-sized commits:

1. `6f92d53` (`locate erased lifecycle view ordinal`) proves the head,
   excluded-head, recursive opening, and arbitrary-decomposition ordinal
   lemmas.  Attempt 1 exposed only a duplicated indexed `rest` pattern; erased
   wildcards corrected it and attempt **2/3** passed.
2. `c0b462b` (`pin erased lifecycle view to open episodes`) proves
   `erasedLifecycleOrdinalAtOpenEpisode`; every
   `LocatedInterleavedOpenEpisode` pins the single erased view of the global
   trace to `transitionCount openPrefix`.  It passed on attempt **1/3**.
3. `b7cc2e1` (`derive canonical supported open episode`) proves
   `canonicalSupportedOpenEpisode`.  It uses Lemma-70 support/active equality,
   endpoint installedness, `extractLastOpening`, exact aligned decomposition,
   and the retained lifecycle exclusion fold.  Attempts 1 and 2 exposed the
   intentionally distinct opaque definitions `activeAt` and
   `supportedActiveAt`; a direct total
   `canonicalSupportedActiveImpliesInstalled` observation resolved the public
   interface mismatch.  Attempt **3/3** passed.
4. `ef4721c` (`prove canonical open ordinal uniqueness`) proves
   `canonicalOpenEpisodeOrdinalUnique` by injectivity of `Just` over the shared
   erased-view ordinal.  It passed on attempt **1/3**.

No executable scan result, runtime middle-state record, postulate,
`believe_me`, `assert_total`, partial definition, or escape hatch was introduced.
All new functions live in the research module and every proof-relevant scan
consumer is quantity 0.

## O12 fill

The actual O12 hole-fill budget remained untouched throughout preparation.
`closingFreeTraceShapeSpike_rhs` was then replaced by a total construction of
`MkClosingFreeTraceShape`:

- supported actors receive `canonicalSupportedOpenEpisode`;
- competing open episodes receive
  `canonicalOpenEpisodeOrdinalUnique`; and
- unsupported actors receive `NoLifecycleBy` from the retained aligned
  occurrence-exclusion fold and quiet-endpoint support/active contradiction.

The direct fill passed on attempt **1/3** and was committed as `874b3fb`
(`prove canonical closing-free trace shape`).  CanonicalSort therefore drops
from six holes to five.  The complete project census is now **18**, split
**5/4/8/0/1** (CanonicalSort/CrossTrace/DeletionChain/LocalDiamond/
RenamingComposition).

## Per-commit validation

Every retained proof commit above was followed by a fresh CanonicalSort check
that deleted its TTC/TTM first and visibly reported:

```text
3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike
exit 0; no Error: diagnostic
```

Only one Idris process ran at a time.  A pre-commit `git diff --check` detected
two whitespace-only lines after the first view edit; they were removed before
staging or committing.  This was not an elaborator attempt and changed no proof.

## Frozen surfaces and terminal gate

The terminal R133 gate rechecks:

- seeded production closure after deleting only terminal
  `CP4ProgressProof.ttc/.ttm`, requiring visible `207/207`;
- CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0`;
- empty production diff from `34b21c9` across `src/` and `dgamma.ipkg`;
- adjacent-swap full definition, 1470 bytes,
  `2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf`;
- adjacent statement prefix, 1154 bytes,
  `3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf`;
- exact hole split `5/4/8/0/1`; and
- no staged files and only the two permitted untracked paths, `paper/` and
  `review-o6-body-adversarial.md`.

O14 and later CanonicalSort obligations were not opened in this shift.  O12 is
closed at a committed, independently rebuildable boundary; the next dependency
is O14 (`supportOrderingSpike`).
