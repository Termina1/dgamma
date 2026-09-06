# O6 R169 — B48 cured; operational and registration accounting complete; O9 external-input frontier remains

## Baseline, scope, and safe partial gate

Started **2026-09-06 00:31:20 UTC**, branch `cp5-thm73-scoping`, at the required
HEAD **`a8ed0d562666a57d1f3be3c7067327c39507b324`**. The initial tree contained
only permitted untracked `paper/` and `review-o6-body-adversarial.md`; the
process scan found no Idris compiler. Idris reports **0.8.0**. Before the first
check, `idris2 --help` verified `--source-dir <dir>` and `--check`. Read R168
first, including all three B48 failure diagnostics and the remaining producer
chain, then the complete R167/R166 audits and R146 strategy memo. Read the
entire extracted paper in bounded chunks, continuing where output truncated.

**Safe partial proof gate at `0412eaf`, last implementation check completed
03:38:42 UTC.** B48's primary simultaneous-construction cure succeeded. Full
unchanged operational capital is produced at the live enriched deletion
result. The exact canonical endpoint, selected-birth classifications, strict
trace-length decrease, and full bidirectional canonical registration accounting
are also now produced. **O9 itself remains unfilled:** the live assembler still
requires **`SameExternalOrchestration`** for the exact surviving trace. O10/O11
remain unopened. No theorem-73 hole was closed; census delta **0**.

The no-new-attempt boundary is **03:51:20 UTC**, mandatory safe-gate deadline
**04:16:20 UTC**, four-hour timeout **04:31:20 UTC**. With roughly twelve minutes
left before the attempt guard, no new state-sensitive root-role preservation
and fold-retention migration was opened. Gate validation began at 03:39:27.
This is a **time-budget partial gate**, not an exhausted 3/3 stop, a semantic
counterexample, or permission to change the R146 route. No proof attempt
followed `0412eaf`.

Changed paths only:

- `research/DGamma/CP5ConfluenceDeletionChainSpike.idr` — **1647 inserted lines**,
  106 new top-level declarations; no existing declaration changed;
- this audit.

Removing the single new block before O9 reconstructs the entire baseline
DeletionChain file **byte-for-byte**. LocalDiamond is likewise **byte-identical
to `a8ed0d5`**: no export, body, signature, ordering, or declaration change.
Production `src/` and `dgamma.ipkg` remain byte-identical to `34b21c9`.
No frozen `deletionTheoremProof` call, raw-name-global exclusion cast,
O14/O17/O19 body, O21 withdrawal branch, or semantic route change. No retained
new `with`, let alias, nonlinear pattern, hole, postulate, `believe_me`,
`assert_total`, or partial declaration. `%default total` remains in force.
The nine inherited DeletionChain with-blocks are unchanged. No subagent launched.

## Unit A — B48 PRIMARY cure complete

**`scopedOrdinalSpineWitness` (`7fda38e`) constructs a
`ScopedOrdinalSpinePermutationWitness spine` by one recursion on the spine.**
Each constructor produces its permutation and its explicit `forwardOnPath`
field together. Consumers project this field rather than proving a theorem
about a separately computed permutation.

The `spinePermutation` field is the already-checked `ScopedOrdinalPermutation`,
which itself stores executable forward/backward maps and both erased inverse
laws. Thus the inverse laws are retained inside the permutation field, not
removed or reasserted as an unchecked premise. `forwardOnPath` is an explicit
erased field of the outer witness.

| Clause | Producer-owned construction | Commit |
|---|---|---|
| Empty | No path exists; identity permutation | `ad08412`, `7fda38e` |
| Keep-Here | Explicit lifted map fixes zero | `2fdbaee` |
| Keep-Later | Apply `cong S` to the tail's stored field | `2fdbaee` |
| Delete-Later | Explicit rotation of the lifted tail, using the tail's field and bounded successor law | `d0fe239` |
| Keep packaging | Constructor stores lifted map and exact path proof together | `5136af1` |
| Delete packaging | Constructor stores rotated map and exact path proof together | `7efc02a` |
| Recursive root | One structural recursion; no post-hoc computed-map elimination | `7fda38e` |

A1–A7 all passed **1/3**, including Delete-Later. **Fallback not used**; no
count-index surface replacement was needed. The old checked
`scopedOrdinalSpinePermutation` and its inverse algebra remain untouched.
R168's removed `scopedOrdinalPermutationPath` theorem was not attempted a fourth
time under another spelling.

## Unit B — unchanged operational capital COMPLETE

### Exact numeric shapes and whole-origin equation

`ScopedOrdinalOriginWitness` stores a shape and an exact path producer at an
origin map. `scopedGenerationOrdinalWitness` (`6ee18b8`) recursively constructs
both from each **actual** generation subsequence. Keep handles the exact
zero/successor observation separately; Delete uses `scopedMapSuccEliminate` to
retain explicit count equalities instead of identifying existential indices.
The frozen `generationSubsequenceSourceOrdinal` function is unchanged.

`ScopedOrdinalAppendWitness` stores the joined shape plus both path inclusions,
including their exact source and target count offsets. Its recursive producer
`scopedOrdinalAppendWitness` (`be3f1e7`) constructs those fields simultaneously,
so it introduces no new post-hoc computed-shape reduction wall.
`ScopedDeletionOrdinalSegments` retains before/center/after origin witnesses
and the two actual append joins. `scopedDeletionEmbeddedOrdinalPath`
(`341357d`) turns each `DeletionSurvivingOrdinalEmbedding` constructor into the
whole path at exactly its frozen offsets.

`scopedDeletionWholeOrdinal` (`8128630`) consumes the frozen whole origin's
**stored embedding** and projects `forwardOnPath`. It does not replace that
origin with a newly chosen source occurrence. Numeric maps are lifted to
`RegistrationGeneration` by preserving the raw name and permuting its birth
ordinal; both inverse laws are checked in `scopedOrdinalGenerationBijection`
(`dba15db`). Separate source/target occurrence-adapter equations retain exact
birth ordinals without equating erased transition proof terms.

**`scopedDeletionGeneratedOrdinal` (`42b1255`) proves the generated-registration
equation at THAT frozen origin and THAT bijection.** It is not an identity-map
placeholder, a filler occurrence, or a caller-supplied correspondence.

The numeric permutation is built by finite spine recursion and finite ordinal
rotations. The implemented generation bijection is the uniform raw-name-preserving
lift required by this design. No separate finite-support theorem was added:
finite ordinal support does not imply finite support on all `name × Nat` when
`name` is infinite, and `RegistrationGenerationBijection` does not assert that
stronger property. Both global inverse laws and the exact live generated-birth
seal are proved.

### Unchanged operational package assembled

`scopedOperationalFromOrdinalSegments` (`a80de01`) combines the twelve inherited
readiness/subsequence-tag clauses, the inherited exact whole RuleTag seal,
and the new generation bijection/ordinal seal in the **unchanged**
`MkDeletionProducerOperationalCapital` constructor.
`scopedDeletionOperationalCapital` produces the ordinal segments itself.
**`scopedEnrichedOperationalCapital` (`c39facd`) additionally produces all
readiness seals from the live folds**, so no extra seal or generation-map premise
remains at the enriched result.

B1–B28 used **29 invocations**, all within budget: B23 passed 2/3 after replacing
the reserved identifier `prefix` in its uncommitted pattern; every other B unit
passed 1/3. That rejected spelling is absent from retained source.

## Unit C — substantial O9 capital; exact external-input preservation still missing

### Completed O9 fields

| Field / obligation | Checked producer | Commit |
|---|---|---|
| Exact live `DeletionResult` | Inherited enriched producer, unchanged | `a38854d` (inherited) |
| Full operational certificate | `scopedEnrichedOperationalCapital` | `c39facd` |
| Full semantic replay | Inherited live head producer/assembler, unchanged | `6b3c777`, `fb52b0d` (inherited) |
| Full TARGET `ReplayInvariantBundle` / `nextPremises` | Inherited unconditional bundle, passed to `MkCanonicalizationPremises` by the new step assembler | `dc46b7f`, `72528e0` |
| Canonical endpoint and exact selected withdrawn list | `scopedDeletionCanonicalEndpoint`; `ScopedCanonicalDeletionEndpoint` stores the list equation | `6c09426` |
| Strict decrease of actual whole `traceLength` | `scopedDeletionStrictlyShorter` | `8288bb5` |
| Every selected generation's original child occurrence and later parent close | `scopedDeletionGenerationClassified` | `a76ebc6` |
| Original registration accounted | `scopedOriginalRegistrationAccounted` | `d3cf5f0` |
| Canonical occurrence injectivity | `scopedCanonicalOccurrenceInjective` | `85ebf4a` |
| No withdrawn generation has a retained frozen origin | `scopedWithdrawnGeneratedOriginExcluded` | `f31a123` |
| Full unchanged `CanonicalRegistrationCorrespondence` | `scopedDeletionRegistrationAccounting` | `4fc824a` |
| Whole live step assembly except external inputs | `scopedEnrichedStepFromExternal` | `0412eaf` — **conditional, not O9 closure** |

### Endpoint census and measure

`ScopedWithdrawalCensus` is derived by recursively consuming the actual
`WithdrawnGenerationResult` values. Current withdrawn generations contribute
their genuinely omitted names; historical closed generations do **not** exempt
later reissues of those raw names. The actual three scans prove the final
environment is stamped. `currentGenerationEntryFromLookup` plus that stamping
connects a lookup's key to the stored generation name, rather than guessing a
birth from raw-name membership. The final canonical endpoint retains exact
effects, outside controls, actual raw omissions, historical selected births,
and justification of each omitted raw name by a selected birth.

The length proof is independent of occurrence accounting. Every generation
subsequence weakly decreases length, and the center's selected opening is
necessarily deleted: a Keep contradicts `DeleteEpisodeGenerationLifecycle`.
Explicit append count equations and the located source decomposition carry
that strict decrease through both seams to the exact whole source trace.

### Bidirectional registration accounting

`scopedSubsequenceBirthCoverage` gives every original O-Insert either exact
selected-generation membership or a retained target occurrence with its exact
numeric origin equation. The three whole-source coverage clauses keep the
actual scan offsets; `scopedWholeBirthCoverage` (`432e975`) transports them
through the original located decomposition. This includes root insertions as
well as generated child insertions, though it does **not** establish the
state-sensitive classification of later root O-Retire/O-Remove actions.

The ordinal permutation's inverse law gives source-position uniqueness for a
whole target embedding. Consequently the covered source position is the position
of the **frozen** source occurrence, not just some equal-action occurrence.
`scopedRetainedGeneratedOriginExact` connects that equation through the exact
generated/action adapters. This discharges the `originalRegistrationAccounted`
clause of the unchanged canonical registration record.

In the other direction, `scopedSubsequenceKeptBirthFresh` proves that a kept
insertion's exact source stamp cannot belong to the selected deleted births.
`scopedWholeKeptBirthFresh` assembles this through the actual three target cuts,
retaining source embedding and exclusion together. Source-ordinal uniqueness
then seals the exclusion at the frozen whole origin; it is not inferred merely
from final endpoint absence. Combined with the actual selected birth/later
parent-close classification, this supplies the complete
`withdrawnRegistrationRemoved` clause.

`scopedRegistrationAccountingFromExclusion` is a checked intermediate assembler
with an explicit remaining exclusion premise. **`scopedDeletionRegistrationAccounting`
now discharges that premise itself.** Its canonical-to-original function is
exactly `deletionProducerGeneratedOrigin` at the same result and capital; source
coverage, injectivity and withdrawal removal are all at that function.

### C48/C49 covering cure and exact budget accounting

The first two C48 spellings specialized a three-way indexed classifier directly
to computed episode projections. All RHS clauses elaborated, but coverage
checking rejected every constructor (attempt 1), or its generated case block
(attempt 2). This was a coverage/elaboration wall, not evidence of a missing
semantic constructor.

**Attempt 3 generalized the same in-flight eliminator**: all four source states,
the three source traces, the action and the ordinal predicate are explicit;
three continuation arguments supply the per-segment results. It performs one
classifier elimination and transports only its stored ordinal field. This
retained declaration is a generic eliminator, **not a claim that the removed
specialized declaration passed**. It checked at `0c5c453` on **3/3**.

C49 is the separate exact producer: it supplies those continuations from the
already-checked C44–C47 and C35 producers and invokes the existing actual
classifier. It does not repeat the failed elimination, change the semantic
route, or reset the C48 budget. C49's generated continuation indentation
initially caused a parse error; corrected on **2/3** at `5b5e06e`. Every new
compiler invocation still contained just one new top-level declaration. Both
failed C48 bodies and the first C49 spelling were fully removed; all four
failed diagnostics in the shift are quoted below.

### Remaining producer chain — do not mislabel the conditional assembler

`scopedEnrichedStepFromExternal` emits the full unchanged `DeletionChainStep`,
including exact operational occurrence correspondence and **full TARGET**
`nextPremises`, but still takes:

```text
SameExternalOrchestration nameEq global
  (survivingTrace (scopedEnrichedDeletionResult ... folds
    (replayAligned (chainReplayCapital premises))))
```

This is a genuine remaining obligation, not a discharged source-only producer.
The exact O9 signature/hole is unchanged; no new public O9 assumption was added.
To discharge the last input, the next shift must:

1. prove root-orchestration classification is preserved at each actual kept
   head, using the local producer's exact owner/parent lookups (root O-Retire
   and O-Remove are state-sensitive; same action/tag alone is insufficient);
2. prove each deleted head is non-root orchestration, authenticating any R
   actor's exact child generation and parent rather than its raw name alone;
3. retain these clauses through selected/post-close/relational folds and the
   before/center/after join, deriving `SameExternalOrchestration` at the actual
   live result;
4. apply `scopedEnrichedStepFromExternal` using
   `scopedEnrichedDeletionFoldsFromPremises`, then open the original O9 body;
5. only after O9 closes, open O10 and O11 in order.

No part of this field follows merely from the new generation bijection or
registration accounting. There was not enough safe attempt window to begin
that multi-producer migration after C71. The R146 verbatim route-change
condition was not met.

## O9 / O10 / O11 and fresh census

| Unit | Body attempts | Outcome |
|---|---:|---|
| O9 `enrichDeletionChainStepSpike` | **0/3** | Unfilled. Conditional full live step assembler exists; exact external-input producer still missing. |
| O10 `deleteClosingEpisodesCoreSpike` | **0/3** | Unopened; depends on O9. |
| O11 `assembleClosingFreeAccountingSpike` | **0/3** | Unopened; depends on O10. |

No O9/O10/O11 closure commit exists. Fresh hole census:
**10 = CanonicalSort 2 / CrossTrace 4 / DeletionChain 3 / LocalDiamond 0 /
RenamingComposition 1**, delta **0**. All original hole names and statements
are unchanged. This prefix does not prove Theorem 73 or a complete deletion chain.

## Incremental protocol and fresh-check ledger

There are **106 immediate checked proof commits**, **110 implementation
invocations**: 106 successes and four corrected failed spellings. There are
**106 new top-level declarations**. A declaration-set audit of each commit
verified exactly one new declaration; each failed invocation likewise held
only its one in-flight declaration. No uncommitted multi-declaration probe,
standalone proof module, hidden signature, local let alias, or new with-block
was used. Temporary scripts, snippets and logs live under `/tmp/dgamma-r169*`,
not untracked repository research paths.

All compiler windows are sequential. Process inspection preceded every check;
no orphan was encountered, so none required killing. No build directory or
TTC/TTM was deleted, no from-scratch rebuild, and no concurrent Idris process.
Every implementation success has its own fresh
`Building DGamma.CP5ConfluenceDeletionChainSpike` marker and exit 0. Source and
fixture mtimes were touched for fresh target checks; production was not edited
or touched. Maximum sampled RSS across checks was **5,064,160 KiB (~4.83 GiB)**,
not an OS-measured exact peak. LocalDiamond needed no invocation or visibility
change. Its hole count remains **0**.

Common direct implementation command (verified CLI spelling):

```sh
idris2 --source-dir src --source-dir research --check \
  research/DGamma/CP5ConfluenceDeletionChainSpike.idr
```

The only inherited compiler warning reported by these direct checks is the
unchanged `surviving` shadowing warning. A non-proof `rg -n -E` search command
was rejected for incorrect CLI flag use; no source or compiler invocation was
involved, and the search was rerun correctly. The C60 draft was simplified
before its first invocation; only its retained one-declaration spelling was
compiled. These preparation corrections do not conceal proof attempts.

Every row below identifies the immediate checked commit. Times are successful
check end times in UTC on 2026-09-06. Attempts include all rejected spellings.

| Unit | New declaration | Attempts | Commit | Fresh check ended UTC |
|---|---|---:|---|---|
| A1 | `ScopedOrdinalSpinePermutationWitness` | 1/3 | `a5a7a3f` | 00:34:17 |
| A2 | `scopedOrdinalEndPath` | 1/3 | `ad08412` | 00:35:38 |
| A3 | `scopedOrdinalKeepForward` | 1/3 | `2fdbaee` | 00:36:55 |
| A4 | `scopedOrdinalDeleteForward` | 1/3 | `d0fe239` | 00:38:16 |
| A5 | `scopedOrdinalKeepWitness` | 1/3 | `5136af1` | 00:39:44 |
| A6 | `scopedOrdinalDeleteWitness` | 1/3 | `7efc02a` | 00:41:02 |
| A7 | `scopedOrdinalSpineWitness` | 1/3 | `7fda38e` | 00:42:19 |
| B1 | `ScopedOrdinalOriginWitness` | 1/3 | `3e3b2cc` | 00:44:39 |
| B2 | `scopedKeptOrdinalOrigin` | 1/3 | `e4bba72` | 00:45:59 |
| B3 | `scopedKeptOriginPath` | 1/3 | `f3ec5b4` | 00:47:17 |
| B4 | `scopedKeptOriginWitness` | 1/3 | `d3fcc6f` | 00:48:36 |
| B5 | `scopedDeletedOriginWitness` | 1/3 | `b0bcd0b` | 00:50:10 |
| B6 | `scopedKeptSubsequenceOriginExact` | 1/3 | `ee2966e` | 00:52:08 |
| B7 | `scopedOrdinalOriginTransport` | 1/3 | `8430242` | 00:53:24 |
| B8 | `scopedGenerationOrdinalWitness` | 1/3 | `6ee18b8` | 00:54:57 |
| B9 | `ScopedOrdinalAppendWitness` | 1/3 | `8868109` | 00:56:47 |
| B10 | `scopedOrdinalAppendKeepLeft` | 1/3 | `8b070fa` | 00:58:02 |
| B11 | `scopedOrdinalAppendDeleteLeft` | 1/3 | `a7aea5b` | 00:59:25 |
| B12 | `scopedOrdinalAppendKeepWitness` | 1/3 | `c29c7aa` | 01:00:43 |
| B13 | `scopedOrdinalAppendDeleteWitness` | 1/3 | `b63f00d` | 01:01:58 |
| B14 | `scopedOrdinalAppendWitness` | 1/3 | `be3f1e7` | 01:03:27 |
| B15 | `ScopedDeletionOrdinalSegments` | 1/3 | `080a135` | 01:05:25 |
| B16 | `scopedAssembleDeletionOrdinalSegments` | 1/3 | `46f68b5` | 01:07:11 |
| B17 | `scopedDeletionOrdinalSegments` | 1/3 | `bf2dbc2` | 01:08:45 |
| B18 | `scopedDeletionEmbeddedOrdinalPath` | 1/3 | `341357d` | 01:10:15 |
| B19 | `scopedDeletionWholeOrdinal` | 1/3 | `8128630` | 01:12:06 |
| B20 | `scopedGenerationOrdinalMap` | 1/3 | `eeeab5c` | 01:13:38 |
| B21 | `scopedGenerationOrdinalInverse` | 1/3 | `8a352fa` | 01:14:54 |
| B22 | `scopedOrdinalGenerationBijection` | 1/3 | `dba15db` | 01:16:12 |
| B23 | `scopedGeneratedActionOrdinal` | 2/3 | `5492772` | 01:17:58 |
| B24 | `scopedActionGeneratedOrdinal` | 1/3 | `577206e` | 01:19:18 |
| B25 | `scopedDeletionGeneratedOrdinal` | 1/3 | `42b1255` | 01:20:57 |
| B26 | `scopedOperationalFromOrdinalSegments` | 1/3 | `a80de01` | 01:22:58 |
| B27 | `scopedDeletionOperationalCapital` | 1/3 | `b563be1` | 01:24:20 |
| B28 | `scopedEnrichedOperationalCapital` | 1/3 | `c39facd` | 01:25:45 |
| C1 | `ScopedWithdrawalCensus` | 1/3 | `28f13c7` | 01:30:44 |
| C2 | `scopedElemConsEliminate` | 1/3 | `523744b` | 01:32:02 |
| C3 | `scopedWithdrawalJustificationPrepend` | 1/3 | `3aca592` | 01:33:25 |
| C4 | `scopedWithdrawalCensusCurrent` | 1/3 | `ee9638a` | 01:34:54 |
| C5 | `scopedWithdrawalCensusHistorical` | 1/3 | `9cde394` | 01:36:24 |
| C6 | `scopedWithdrawalCensusHead` | 1/3 | `48d910c` | 01:37:45 |
| C7 | `scopedWithdrawalCensus` | 1/3 | `9782549` | 01:39:07 |
| C8 | `scopedWithdrawalCensusOutside` | 1/3 | `1fff99e` | 01:41:06 |
| C9 | `scopedGenerationBirthMember` | 1/3 | `058aca5` | 01:42:31 |
| C10 | `scopedWithdrawalBirthJustification` | 1/3 | `19a4e84` | 01:43:59 |
| C11 | `ScopedCanonicalDeletionEndpoint` | 1/3 | `3792ac3` | 01:45:17 |
| C12 | `scopedCanonicalEndpointFromCensus` | 1/3 | `39e97a5` | 01:46:39 |
| C13 | `scopedDeletionCanonicalEndpoint` | 1/3 | `6c09426` | 01:48:04 |
| C14 | `scopedGenerationSubsequenceLength` | 1/3 | `5afb836` | 01:50:45 |
| C15 | `scopedAppendTraceLength` | 1/3 | `a32111e` | 01:52:05 |
| C16 | `scopedDeletedHeadStrictLength` | 1/3 | `069cec3` | 01:53:33 |
| C17 | `scopedAppendLengthBound` | 1/3 | `a8fb131` | 01:55:37 |
| C18 | `scopedDeletionCenterShorter` | 1/3 | `a8ccbd7` | 01:57:06 |
| C19 | `scopedDeletionSuffixShorter` | 1/3 | `595b6b1` | 01:58:55 |
| C20 | `scopedDeletionStrictlyShorter` | 1/3 | `8288bb5` | 02:00:27 |
| C21 | `scopedSelectedBirthClosing` | 1/3 | `24f18bd` | 02:05:40 |
| C22 | `scopedSelectedBirthGeneration` | 1/3 | `c9554bd` | 02:07:05 |
| C23 | `scopedSelectedGeneratedClassification` | 1/3 | `6f05da0` | 02:08:37 |
| C24 | `scopedDeletionGenerationClassified` | 1/3 | `a76ebc6` | 02:09:57 |
| C25 | `scopedDeletionStepFromAccounting` | 1/3 | `dc46b7f` | 02:12:40 |
| C26 | `scopedEnrichedStepFromAccounting` | 1/3 | `72528e0` | 02:14:19 |
| C27 | `ScopedLocatedOrdinalOrigin` | 1/3 | `c5b8aff` | 02:16:56 |
| C28 | `scopedPrependLocatedOrdinalOrigin` | 1/3 | `b7bd8d6` | 02:18:23 |
| C29 | `ScopedBirthCoverage` | 1/3 | `203eb87` | 02:20:02 |
| C30 | `scopedBirthCoverageOriginTransport` | 1/3 | `ce5ba6b` | 02:21:23 |
| C31 | `scopedBirthCoverageKeepLater` | 1/3 | `784e614` | 02:22:48 |
| C32 | `scopedBirthCoverageDeleteLater` | 1/3 | `1b2a9ef` | 02:24:16 |
| C33 | `scopedBirthCoverageKeepView` | 1/3 | `19772f5` | 02:25:57 |
| C34 | `scopedBirthCoverageDeleteView` | 1/3 | `84fc4f1` | 02:27:36 |
| C35 | `scopedSubsequenceBirthCoverage` | 1/3 | `8cd2ef2` | 02:29:42 |
| C36 | `scopedOwnedInsertionRegistered` | 1/3 | `a8a2c30` | 02:32:00 |
| C37 | `scopedEpisodeInsertionRegistered` | 1/3 | `67f7bdd` | 02:33:22 |
| C38 | `scopedLocatedAppendLeftOrigin` | 1/3 | `9a3ebd4` | 02:34:47 |
| C39 | `scopedLocatedAppendRightOrigin` | 1/3 | `0fbb986` | 02:36:07 |
| C40 | `scopedLocatedAppendRightWitness` | 1/3 | `96f310c` | 02:38:01 |
| C41 | `ScopedWholeRetainedOrigin` | 1/3 | `bfffded` | 02:39:22 |
| C42 | `scopedWholeRetainedAt` | 1/3 | `b798d18` | 02:40:50 |
| C43 | `ScopedWholeBirthCoverage` | 1/3 | `e03e78e` | 02:42:30 |
| C44 | `scopedWholeBirthBefore` | 1/3 | `93958c1` | 02:44:07 |
| C45 | `scopedWholeBirthCenter` | 1/3 | `797bcb8` | 02:45:42 |
| C46 | `scopedWholeBirthAfter` | 1/3 | `d59a6ee` | 02:47:20 |
| C47 | `scopedDeletionScanCountOffsets` | 1/3 | `c815467` | 02:49:07 |
| C48 | `scopedWholeBirthCoverageView` | 3/3 | `0c5c453` | 02:55:55 |
| C49 | `scopedWholeBirthCoverageSegments` | 2/3 | `5b5e06e` | 02:58:09 |
| C50 | `scopedLocatedPredicateTransport` | 1/3 | `4bc090e` | 02:59:41 |
| C51 | `scopedWholeBirthCoverage` | 1/3 | `432e975` | 03:01:12 |
| C52 | `scopedOrdinalForwardInjective` | 1/3 | `ad60ba8` | 03:03:06 |
| C53 | `scopedEmbeddedOrdinalsUniqueAt` | 1/3 | `3ae6764` | 03:04:47 |
| C54 | `scopedDeletionEmbeddedOrdinalsUnique` | 1/3 | `edab793` | 03:06:16 |
| C55 | `scopedWholeRetainedSourceOrdinal` | 1/3 | `40d8524` | 03:07:59 |
| C56 | `scopedRetainedGeneratedOriginExact` | 1/3 | `fb06c7d` | 03:09:42 |
| C57 | `scopedOriginalRegistrationAccountedAt` | 1/3 | `86a75c8` | 03:11:23 |
| C58 | `scopedOriginalRegistrationAccounted` | 1/3 | `d3cf5f0` | 03:12:49 |
| C59 | `scopedCanonicalOccurrenceInjective` | 1/3 | `85ebf4a` | 03:15:24 |
| C60 | `scopedWithdrawnRegistrationWitness` | 1/3 | `f030a09` | 03:17:54 |
| C61 | `scopedRegistrationAccountingFromExclusion` | 1/3 | `bea9e8c` | 03:19:39 |
| C62 | `scopedBirthFreshShift` | 1/3 | `8d26b4c` | 03:21:51 |
| C63 | `scopedKeptBirthHeadFresh` | 1/3 | `5f3ecf3` | 03:23:24 |
| C64 | `scopedKeptBirthFreshView` | 1/3 | `b66b47a` | 03:25:10 |
| C65 | `scopedSubsequenceKeptBirthFresh` | 1/3 | `f7edac6` | 03:26:55 |
| C66 | `ScopedWholeFreshOrdinal` | 1/3 | `85f3fb1` | 03:29:51 |
| C67 | `scopedWholeKeptBirthFresh` | 1/3 | `b46e702` | 03:31:46 |
| C68 | `scopedFrozenBirthFreshAt` | 1/3 | `ebc73ce` | 03:33:39 |
| C69 | `scopedWithdrawnGeneratedOriginExcluded` | 1/3 | `f31a123` | 03:35:28 |
| C70 | `scopedDeletionRegistrationAccounting` | 1/3 | `4fc824a` | 03:37:05 |
| C71 | `scopedEnrichedStepFromExternal` | 1/3 | `0412eaf` | 03:38:42 |

## Exact failed compiler diagnostics

All four spellings were corrected within their original micro-unit budgets.
Repeated inherited warnings and wrapper timestamps are omitted below; full error
diagnostics are quoted. No micro-unit exhausted three unsuccessful attempts.

### B23-1

```text
Error: Couldn't parse declaration.

DGamma.CP5ConfluenceDeletionChainSpike:26663:1--26663:29
 26659 |   (initial, finalState : SystemState name key value world error) -> (trace : Transitions initial finalState) ->
 26660 |   (child, parent : name) -> (component : Component key value world error) ->
 26661 |   (occurrence : LocatedGeneratedRegistration child parent component trace) ->
 26662 |   (locatedActionOrdinal (generatedRegistrationActionOccurrence occurrence) = registrationOrdinal occurrence)
 26663 | scopedGeneratedActionOrdinal name key world error value initial finalState trace child parent component
         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### C48-1

```text
Error: scopedWholeBirthCoverageView is not covering.

DGamma.CP5ConfluenceDeletionChainSpike:27475:1--27490:167
 27475 | 0 scopedWholeBirthCoverageView :
 27476 |   (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
 27477 |   (initial, finalState : SystemState name key value world error) -> (global : Transitions initial finalState) ->
 27478 |   (candidate : DeletableClosingEpisode name key world error value nameEq keyEq global) ->
 27479 |   (result : DeletionResult name key world error value nameEq keyEq global (selectedActor candidate) (selectedEpisode candidate)
 27480 |     (selectedRegistrations candidate) (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->

Missing cases:
    scopedWholeBirthCoverageView arg arg arg arg arg arg arg arg arg arg arg arg arg arg arg arg (DeletionWholeBefore _ _)
    scopedWholeBirthCoverageView arg arg arg arg arg arg arg arg arg arg arg arg arg arg arg arg (DeletionWholeEpisode _ _)
    scopedWholeBirthCoverageView arg arg arg arg arg arg arg arg arg arg arg arg arg arg arg arg (DeletionWholeAfter _ _)
```

### C48-2

```text
Error: scopedWholeBirthCoverageView is not covering.

DGamma.CP5ConfluenceDeletionChainSpike:27475:1--27490:167
 27475 | 0 scopedWholeBirthCoverageView :
 27476 |   (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
 27477 |   (initial, finalState : SystemState name key value world error) -> (global : Transitions initial finalState) ->
 27478 |   (candidate : DeletableClosingEpisode name key world error value nameEq keyEq global) ->
 27479 |   (result : DeletionResult name key world error value nameEq keyEq global (selectedActor candidate) (selectedEpisode candidate)
 27480 |     (selectedRegistrations candidate) (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->

Calls non covering function DGamma.CP5ConfluenceDeletionChainSpike.case block in scopedWholeBirthCoverageView
```

### C49-1

```text
Error: Expected ')'.

DGamma.CP5ConfluenceDeletionChainSpike:27512:1--27512:2
 27508 |     (ScopedWholeBirthCoverage name key world error value nameEq keyEq initial finalState global candidate result child parent component)
 27509 |     initial (locatedPreStart (selectedEpisode candidate)) (locatedAfter (selectedEpisode candidate)) finalState
 27510 |     (traceBeforeOpening (selectedEpisode candidate)) (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate)))) (closedTransitions (locatedEpisode (selectedEpisode candidate)))) (traceAfterClosing (selectedEpisode candidate)) (OInsert child parent component)
 27511 |     (\localOccurrence => (scopedWholeBirthBefore name key world error value nameEq keyEq initial finalState global candidate result child parent component (locatedActionOrdinal localOccurrence)
 27512 | (scopedSubsequenceBirthCoverage name key world error value nameEq (selectedRegistrations candidate) (GenerationOwnedActor nameEq (selectedRegistrations candidate))
         ^
```

## Final fresh seeded gate evidence

All final checks below are at proof HEAD **`0412eaf`**, after the last source
change, and were run sequentially. The target mtimes were touched, and each
non-package log contains a fresh `Building` marker. Package closure used the
retained production seed and intentionally was not a fresh rebuild.

| Check | Start–end UTC, 2026-09-06 | Exit | Result |
|---|---|---:|---|
| gate-deletion | 03:39:27–03:40:32 | 0 | Fresh direct DeletionChain check passed |
| gate-positive | 03:40:32–03:40:38 | 0 | Positive projection fixture passed |
| gate-direct-negative | 03:40:38–03:40:43 | 1 | Expected rejection; required fragments verified |
| gate-filler-negative | 03:40:43–03:40:48 | 1 | Expected rejection; required fragments verified |
| gate-map-negative | 03:40:48–03:40:53 | 1 | Expected rejection; required fragments verified |
| gate-seeded | 03:40:53–03:41:08 | 0 | `idris2 --build dgamma.ipkg`, seeded 207/207 |

An earlier four-fixture batch also passed/rejected as intended at
**01:26:11–01:26:31 UTC**, after Unit B completed and before O9-capital work.
The final batch above supersedes it for final-source acceptance.

No fixture was added or modified. Exact fixtures and diagnostic boundaries:

- `R11DeletionCertificateProjectionPositive` — passed;
- `R11DirectDeletionStepCloneNegative` — rejected at
  `cloneDeletionStepWithAlternateMap`, with `occurrences and alternate`;
- `R11DeletionFillerMapCertificateNegative` — rejected at
  `fillerMapCannotConstructDeletionCertificate`, with
  `generationSubsequenceSourceOrdinal`;
- `R10DeletionStepMapCloneNegative` — rejected at
  `replaceDeletionStepOccurrenceMap`, with
  `alternate and step .deletionOccurrenceCorrespondence`.

Reproduce each fixture check using its exact filename:

```sh
idris2 --source-dir src --source-dir research --source-dir research-tests \
  --check research-tests/DGamma/R11DeletionCertificateProjectionPositive.idr
idris2 --source-dir src --source-dir research --source-dir research-tests \
  --check research-tests/DGamma/R11DirectDeletionStepCloneNegative.idr
idris2 --source-dir src --source-dir research --source-dir research-tests \
  --check research-tests/DGamma/R11DeletionFillerMapCertificateNegative.idr
idris2 --source-dir src --source-dir research --source-dir research-tests \
  --check research-tests/DGamma/R10DeletionStepMapCloneNegative.idr
idris2 --build dgamma.ipkg
```

Run only one compiler at a time and retain the existing seed. The last three
fixture commands are **supposed to exit 1** with the diagnostic fragments above.
The wider R11 suite was not rerun. No executable runtime test or new fixture is
claimed. Total compiler **check/build invocations: 120** = 110 implementation +
four mid-shift fixtures + six final checks. Of these, 110 exited 0, six exited 1
as expected negative fixtures, and four were the budgeted failed spellings.

### Frozen surfaces and independent asserting self-validation

The frozen extraction starts at `0 adjacentSwapSuffixSpike :`, excludes the
preceding `public export` and following newline, verifies that next newline,
and takes the statement prefix through `adjacentSwapSuffixSpike =`.

```text
proofHEAD: 0412eaf
fullSurfaceBytes: 1470
fullSurfaceSHA: 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
statementBytes: 1154
statementSHA: 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
seeded: 207/207
missingTTC: []
CP3Blob: 2c697e532e83989de8591fa6a4378747c6a501c0
ipkgBlob: da0c007ee08c4648e459296eb6f0e72a40e2ac89
productionDiffVs34b21c9: EMPTY (src/ and dgamma.ipkg)
reviewSHA: 61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8
holes: CanonicalSort 2 / CrossTrace 4 / DeletionChain 3 / LocalDiamond 0 / RenamingComposition 1
holeDelta: 0
withCountsBaselineAndCurrent: 9 / 9
proofCommits: 106
newDeclarations: 106
implementationInvocations: 110
implementationFailures: B23-1, C48-1, C48-2, C49-1
allCompilerWindowsSequential: True
LocalDiamondDiffVsA8ed0d5: EMPTY, complete byte equality
LocalDiamondExports: NONE (no visibility exception invoked)
DeletionChainBaselineReconstruction: exact byte equality after removing the new block
Added believe_me/assert_total/postulate/partial/with/let/hole/deletionTheoremProof: NONE
%default total: retained
Whitespace: PASS
NoStagedFilesAtProofGate: True
UntrackedAtProofGate: paper/ and review-o6-body-adversarial.md only
```

The asserting validator checks every package module's TTC path, working-tree
CP3 blob, complete production diff, both frozen SHA ranges, full LocalDiamond
byte equality, unchanged hole names, per-commit declaration counts, matching
fresh-check logs, prohibited additions, whitespace, and index cleanliness.
The compiler ledger also verifies that no two check windows overlap. These are
reproducible **self-checks**, not an independent acceptance review.

The adversarial review file was never modified, staged, committed, or deleted.
No stray untracked research artifact is present. This audit is committed
separately after source validation; after its commit the index must remain clean
and only the two permitted untracked paths may remain. No README, NOTES,
production, LocalDiamond or fixture file changed.

## Status

**Fully proved this shift:** B48 primary simultaneous permutation/path witness;
actual generation-subsequence numeric spines and exact paths; producer-owned
append shape/path offset joins; whole ordinal and generated-registration seals
at the frozen whole-origin function; total two-sided registration-generation
bijection; full unchanged live operational capital; stamped current-generation
withdrawal census; exact canonical endpoint and selected-list equation;
whole-trace strict length decrease; selected original birth/later-parent-close
classification; exact original birth coverage across all three cuts;
source-ordinal uniqueness; every original generated registration accounted;
canonical occurrence injectivity; exact whole kept-birth exclusion; and complete
unchanged `CanonicalRegistrationCorrespondence` at the operational origin.

**Partial:** O9. `scopedEnrichedStepFromExternal` constructs every full O9 field
but still requires exact `SameExternalOrchestration` at the live enriched result.
All registration-accounting and target-bundle premises of its supporting
assemblers are now discharged by live producers. The remaining external-input
premise is **not** discharged and has **not** been silently added to O9 or its
caller. No complete deletion step from the original premises, deletion chain,
or Theorem-73 proof is claimed.

**Merely stated:** the same ten research holes, split **2/4/3/0/1**. Original
O9/O10/O11 bodies remain unchanged at **0/3**. No new escape hatch or hole.
The finite-support qualification above is explicit, not a hidden theorem claim.

**Next after reviewer/owner gate:** derive and retain the actual kept/deleted
root-orchestration classification through live folds, assemble
`SameExternalOrchestration`, and apply `scopedEnrichedStepFromExternal`. Then
open O9, O10 and O11 in order under fresh body budgets. Do not equate action/tag
agreement with state-sensitive root-role agreement, infer a birth from raw-name
membership, cast the scoped exclusion to the raw predicate, call frozen
`deletionTheoremProof`, weaken the full TARGET bundle, add a with-block, or
widen production. Reviewer/owner acceptance remains **required**.
