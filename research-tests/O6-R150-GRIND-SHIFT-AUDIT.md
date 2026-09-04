# O6 R150 — first-seam telescope stop audit

## Coordinate and ordered scope

R150 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`57b47faee6f6eac5f078ccd6d6b1964f3ebc5cb8`.  The initial tree contained only
the two permitted untracked paths, `paper/` and
`review-o6-body-adversarial.md`; neither was touched.

The shift obeyed the R150 probe cascade and the ratified route-B order from
`O6-R146-STRATEGY-MEMO.md`.  In particular, a disposable minimal probe for the
`before | episode` append seam was opened before either later append seam and
before any composed `deletionStepOperationalOccurrenceFoldSpike` body.  Its
local budget was exactly three compiler attempts.  The first seam did not pass,
so the binding stop fired immediately and no later proof budget was opened.

No production source, package manifest, retained research theorem, O14, O17,
O19, or O21 withdrawal branch was edited.

## Probe 1 — `before | episode` append seam (failed 3/3)

The disposable module `DGamma.R150BeforeEpisodeSeamProbe` tested the narrow
producer required at the first append boundary.  Its intended output was a
dependent `R150LocatedAppendClassification`: every located occurrence in
`appendTransitions before episode` carries either a producer-owned occurrence
in `before` with exact local ordinal, or one in `episode` with the exact
`transitionCount before` offset.  Separate top-level occurrence-prefix and
left/right append embeddings kept the transition occurrence structural rather
than searching by raw action equality.

The probe verdict is **failed at 3/3**.

### Attempt 1/3 — direct-import scope

The probe initially imported the deletion-chain module but not the defining
production modules directly.  Idris imports are not transitive re-exports, so
elaboration stopped before the seam family:

```text
3/3: Building DGamma.R150BeforeEpisodeSeamProbe
Error: While processing type of r150PrependLocated. Undefined name SystemState.
...
Error: While processing type of r150BeforeEpisodeSeamProbe. Undefined name Transitions.
exit 1
```

`DGamma.Calculus` and `DGamma.CP3` were then imported directly.  This was a
probe spelling repair only; the strict attempt was nevertheless consumed.

### Attempt 2/3 — action index not constructor-owned

With direct imports fixed, the classifier reached its first dependent
constructor and exposed the first missing constructor-owned index:

```text
3/3: Building DGamma.R150BeforeEpisodeSeamProbe
Error: While processing constructor R150LocatedInLeft. Can't bind implicit
DGamma.R150BeforeEpisodeSeamProbe.{action:2951} of type
(DGamma.Calculus.Action ...)
exit 1
```

The action and whole occurrence were made explicit constructor telescope
arguments.  This is consistent with the ratified cure: a seam view must own its
exact boundary indices rather than asking Idris to recover them from unrelated
projections.

### Attempt 3/3 — right branch needs the full append telescope

The explicit action/occurrence repair advanced to the right constructor, where
the left start state remained absent from the constructor's recoverable
indices:

```text
3/3: Building DGamma.R150BeforeEpisodeSeamProbe
Error: While processing constructor R150LocatedInRight. Can't bind implicit
DGamma.R150BeforeEpisodeSeamProbe.{first:3053} of type
(DGamma.Calculus.SystemState ...)
exit 1
```

The right local occurrence fixes the seam and final states, while its global
whole occurrence mentions the appended trace only through the family result;
that is not enough for Idris to infer the left start state while checking the
constructor.  The next mechanical repair would be the memo's exact cure:
thread `first`, `middle`, `finalState`, and the remaining type telescope
explicitly through both constructors.  The local three-attempt budget was
already exhausted, so that repair was not attempted and no self-extension was
taken.

The probe source and any named TTC/TTM artifacts were fully removed.  No probe
artifact is retained in the tree or build cache.

## Ordered stop and downstream disposition

Because the first mandatory seam probe failed 3/3, the R150 stop rule applied
before every later unit:

- `episode | after` seam probe: **0/3**, not opened;
- whole-trace recomposition seam probe: **0/3**, not opened;
- fresh composed `deletionStepOperationalOccurrenceFoldSpike` body unit:
  **0/3**, not opened;
- `deletedClassificationForcesLeftScannerDiscardSpike`: **0/3**, not opened;
- right scanner mirror: **0/3**, not opened;
- `enrichDeletionChainStepSpike` steps (b)–(d): **0/3**, not opened.

Accordingly there is no composed-body result and no retained helper commit in
this shift.  The ratified capital at `788caab` and `d961e62` is unchanged.

The R146 semantic route-change condition did **not** fire.  The failed probe
examined only append-family index ownership; it did not expose any accepted
`L-Unload` coexisting with an installed committed consumer, and it did not test
or refute production of a located activation/generation.  This is an Idris
telescope elaboration stop, not semantic evidence against route B.

## Holes, restrictions, and final evidence

The research-hole census is unchanged at **13**, split exactly:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 6
- LocalDiamond: 0
- RenamingComposition: 1

No hole was filled or added.  No postulate, `believe_me`, `assert_total`,
`partial`/`covering` annotation, unsafe operation, retained `let`, `with` block,
nonlinear pattern, or hidden signature was introduced.  `%default total` and
the existing quantity discipline remain unchanged.

After probe removal, the seeded final checks were forced by source timestamps
only; no `build/` directory or build artifact was deleted:

```text
Idris 2, version 0.8.0

DeletionChain seeded direct check:
  2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
  exit 0

seeded package closure:
  207/207: Building DGamma.CP4ProgressProof
  exit 0

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (git diff --quiet exit 0)

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The full-definition and statement-prefix hashes were freshly recomputed using
the frozen R128 byte conventions.  `git diff --check` passes.  Apart from this
audit before it is committed, the only untracked paths are the two permitted
initial paths; there are no stray research probe files.  One Idris process ran
at a time, with an orphan-process check before each fresh invocation.

## Gate verdict

**STOP at the first append seam.**  R150 consumed exactly 3/3 attempts in its
first disposable seam probe and 0 attempts everywhere else.  Any continuation
must be freshly authorized; the mechanically indicated next spelling is a
constructor-owned full append telescope, followed by a new probe cascade only
under a new budget.
