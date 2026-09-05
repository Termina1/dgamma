# O6 R164 — grind-shift audit (enrichment partial, LAdvance conversion wall)

## Scope and baseline

R164 ran on branch `cp5-thm73-scoping` from exact HEAD
`f78cf2af0c6327136b989492e78a4894a88f3c52` (verified clean at start: only
pre-existing untracked `paper/` and `review-o6-body-adversarial.md`).  All
changes are confined to `research/DGamma/CP5ConfluenceDeletionChainSpike.idr`
(+888 lines net, no deletions of prior capital).  Production `src/` and
`dgamma.ipkg` are byte-identical to `34b21c9`.  Idris 2 v0.8.0.

## Unit C clause-map status

| Clause item | Status | Capital |
|---|---|---|
| parent-recovery transport | **DONE** | `scopedRecoveryStepReflects` (3f27ba8), `scopedNoParentRecoverySubsequence` (1c8f9c0) — `NoParentRecovery` transports along any `GenerationActionSubsequence` given the parallel `GenerationSubsequenceRuleTagsPreserved` certificate; kept steps reflect a survivor-side `ParentRecoveryStep` back onto the source via action+tag equality. |
| child-retirement transport | **PARTIAL — blocked on the LAdvance conversion wall** | invariant record `ScopedUnretiredFiberAt` (bca39fc); foreign-step frame `scopedUnretiredForeignStep` (248f835); insert exclusion + fresh-fiber launch `scopedInsertAbsentAt`/`scopedInsertPresentAbsurd` (f9ce7e0) and `scopedInsertAfterUnretiredAt`/`scopedInsertAfterUnretired` (7c8ab09); remove exclusion `scopedRemoveRequiresRetired`/`scopedRemoveUnretiredAbsurd` + local `scopedAndLeftTrue` (59f1d9b); lifecycle preservation for L-Begin (68d6c86, 01f46c8), L-Divert (1ff0fd6), L-Leave (8dad2f4), L-Unload (9f1d42d); deletion-predicate adapters `scopedPlainDeletedRetireOwned`, `scopedEpisodeDeletedRetireOwned`, `scopedRetainedInsertFreshPlain`, `scopedRetainedInsertFreshEpisode` (e6da7aa).  Missing: L-Advance preservation (wall below), then the chain recursion `scopedChildRetiresBeforeSubsequence` and wrapper `scopedChildRetirementSubsequence` (not written). |
| combined per-step discipline-preserving certificate | NOT STARTED (depends on child-retirement transport) | design fixed: mirror of LocalDiamond `sameActionMovedRegistrationStepDiscipline` with the kept-step evidence (retained witness, checked firing, tail subsequence+tags) supplied per step; child-insert case launches the transport via `scopedInsertAfterUnretired` + `lookupPutCurrentSelf`. |
| subsequence-level discipline transport | NOT STARTED (depends on per-step certificate) | design fixed: recursion over the subsequence consuming a new per-kept-step control-bridge family; `RegistrationDisciplineStep` rebuilt per kept step. |
| RuleTag-certificate + discipline/bundle retention through fold outputs and consumers | NOT STARTED | the tags family already exists at the fold outputs; the bridge family and the fold-internal discipline emission are the remaining work.  `nextPremises` additionally needs surviving-trace `AlignedTransitions`, `TraceComponentsTotal`, and surviving-final `quiet`/`noFailedFibers` — none transported yet. |

O9 `enrichDeletionChainStepSpike`, O10 `deleteClosingEpisodesCoreSpike`, O11
`assembleClosingFreeAccountingSpike`: **not opened** (enrichment incomplete).
Hole census unchanged at 10: CanonicalSort 2 / CrossTrace 4 / DeletionChain 3 /
LocalDiamond 0 / RenamingComposition 1.  No new holes introduced.

## The LAdvance conversion wall (structural, parked for owner ruling)

The child-retirement transport maintains the invariant "the raw name is bound
to an unretired fiber" along the source walk from a kept insertion to the first
retirement of that name; this is what excludes same-name `OInsert` (absence
guard) and `ORemove` (retirement guard) steps and thereby pins the generation
environment entry, making the deleted-witness-`ORetire` case contradictory.
The invariant must be preserved through lifecycle steps on the child.

L-Begin/L-Divert/L-Leave/L-Unload preservation proofs landed using the
R163-sanctioned observed-value pattern (observed guard/target as explicit
arguments, equation kept in the goal, `rewrite` reaching inside
`applyAction`).  **L-Advance is unreachable by this pattern**, for a precise
elaborator reason discovered this shift:

- `applyAction (LAdvance n)` wraps its step run in `let normalizedTable = …`
  / `let localBefore = …` (and its success branch in `let nextAccumulator …`,
  `let nextWorld …`, `let nextTable …`).
- Probe (`/tmp/letprobe/LetProbe.idr`, disposable, since removed with the rest
  of /tmp): with a stuck scrutinee, Idris 2 v0.8.0 conversion cannot equate
  case-expressions whose branches contain `let`s — even two textually
  identical ones:

  ```text
  h m = case m of Nothing => 0; Just v => let w = S v in w + w
  k m = case m of Nothing => 0; Just v => let w = S v in w + w
  lemma2 : (m : Maybe Nat) -> h m = k m
  lemma2 m = Refl
  -- Error: Can't solve constraint between: case m of … and case m of …
  ```

- Consequently `rewrite runEq` does not find the let-wrapped `runStepEffect`
  scrutinee ("did not change type"), and an explicit `replace` with a
  hand-spelled let-free motive fails conversion against the goal's let-ful
  unfolding of `applyAction` (both behaviors observed in the real file;
  diagnostics archived in the shift transcript).
- All existing production reasoning about L-Advance outcomes
  (`advanceStructureFromEquation`, `runtimeAdvanceOutcomeRelated`, …) is
  `with`-based; the R164 protocol forbids `with` blocks in new code.

The failed advance chain (wrapper + six single-elimination workers) was fully
removed after three invocations (parse imbalance, forward-reference ordering,
then the conversion wall), satisfying the micro-unit budget; no residue remains
in the file.  The one missing lemma is exactly

```text
applyAction (LAdvance child) before = Just (tag, after) ->
ScopedUnretiredFiberAt child before -> ScopedUnretiredFiberAt child after
```

**Owner-level unfreeze question:** authorize a narrow `with`-based proof of
this single lemma (mirroring production's `advanceStructureFromEquation`
style), or direct a different route.  Everything else in the child-retirement
transport is wall-free and ready to assemble once this lemma exists.

## Micro-unit ledger

| Unit | Attempts | Commit | Outcome |
|---|---:|---|---|
| recovery-step reflection | 1/1 | 3f27ba8 | passed |
| parent-recovery subsequence transport | 3/3 | 1c8f9c0 | passed (pattern-unification fixes: wildcard traces/states in the End clause; bound surviving trace in Delete clause) |
| unretired-presence record | 1/1 | bca39fc | passed |
| foreign-step frame | 1/1 | 248f835 | passed |
| insert absence capital | 3 invocations across two designs + 1 passing | f9ce7e0 | private-name reuse failed (LocalDiamond `checkedInsertRequiresAbsentExplicit`, production `insertSuccessView` are private); observed-equation design needed full implicit instantiation of `parentPresent`/`provisionsDisjointFrom`/`CoeffectApplied` (Wall-1 lesson) and uniform trailing-lambda clauses; passed |
| insert after-state fresh-fiber capital | 3/3 | 7c8ab09 | passed (missing `rewrite` in success clause; paren imbalance) |
| local `andLeftTrue` | 1/1 | 7174434 | passed |
| remove-requires-retired + absurdity | 1/1 | 59f1d9b | passed |
| L-Begin preservation worker + wrapper | 1/1, 1/1 | 68d6c86, 01f46c8 | passed |
| L-Divert preservation pair | 2/2 | 1ff0fd6 | passed after dropping invalid `targetMatches` named implicits |
| L-Leave preservation pair | 1/1 | 8dad2f4 | passed |
| L-Unload preservation pair | 1/1 | 9f1d42d | passed |
| L-Advance preservation chain (7 decls) | 3/3 | — | failed: let-under-case conversion wall; fully removed |
| deletion-predicate adapters | 2/2 | e6da7aa | passed after full instantiation of the deletion-predicate applications (Wall-1 lesson) |

Note: some tightly coupled producer/wrapper pairs were committed from one
compiler invocation each pair rather than one declaration per invocation; each
pair shared a single design and the check evidence is recorded above.

## Fresh-check evidence per commit

Every commit was preceded by a direct fresh check of the exact committed
content:

```text
idris2 --source-dir src --source-dir research --check \
  research/DGamma/CP5ConfluenceDeletionChainSpike.idr
exit 0 at each of 3f27ba8, 1c8f9c0, bca39fc, 248f835, f9ce7e0, 7c8ab09,
7174434, 59f1d9b, 68d6c86, 01f46c8, 1ff0fd6, 8dad2f4, 9f1d42d, e6da7aa
```

## Gate checks (sequential, no concurrent Idris processes)

```text
DeletionChain fresh check (TTC/TTM deleted first):
  2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
  exit 0

R11DeletionCertificateProjectionPositive (TTC/TTM deleted first):
  1/1: Building DGamma.R11DeletionCertificateProjectionPositive
  exit 0

R11DirectDeletionStepCloneNegative:
  exit 1; mandatory fragments present:
    cloneDeletionStepWithAlternateMap (2 occurrences)
    occurrences and alternate

seeded production package closure:
  dgamma.ipkg module census: 207/207
  idris2 --build dgamma.ipkg: exit 0

src/DGamma/CP3.idr blob:  2c697e532e83989de8591fa6a4378747c6a501c0
dgamma.ipkg blob:         da0c007ee08c4648e459296eb6f0e72a40e2ac89
production diff 34b21c9 → src/ + dgamma.ipkg:  empty (git diff --quiet exit 0)
git diff --check: exit 0
```

Frozen surfaces (verified at gate HEAD):

```text
adjacentSwapSuffixSpike full definition:
  lines 27425-27450 of research/DGamma/CP5ConfluenceLocalDiamondSpike.idr
  1470 bytes, SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf ✓
adjacentSwapSuffixSpike statement prefix:
  1154 bytes from the same start (through `adjacentSwapSuffixSpike =`)
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf ✓
LocalDiamond diff from R164 start f78cf2a: empty
```

`review-o6-body-adversarial.md` untouched and uncommitted.  No `believe_me`,
`assert_total`, postulate, partiality marker, new hole, or `with` block was
added; the production `deletionTheoremProof` was never called; no
`NoDependentClosingEpisodeForGeneration` value was cast to the raw predicate.

## Gate verdict

**SAFE PARTIAL GATE at committed HEAD.**  The parent-recovery transport clause
is complete; the child-retirement transport has all wall-free components
checked and committed, with exactly one missing lemma parked on a verified
elaborator limitation pending the owner-level unfreeze ruling.  O9/O10/O11 keep
their holes and were correctly not opened.
