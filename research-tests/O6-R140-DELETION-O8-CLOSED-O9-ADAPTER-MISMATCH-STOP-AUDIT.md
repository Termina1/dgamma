# O6 R140 — Deletion O8 closed / O9 adapter-mismatch stop audit

## Scope and verdict

**Verdict: ACCEPT O8 / STOP BEFORE O9.**

R140 resumed at the required `c7900c4da0a853fbbb0ecf1f77dfdf1fa8f9ae56`
coordinate on `cp5-thm73-scoping`. The tracked index and worktree were clean;
the only initial untracked paths were the permitted `paper/cordis-paper.pdf`,
`paper/cordis-paper.txt`, and `review-o6-body-adversarial.md`. The R139, R138,
and R137 audits were read before editing. The review file was read but never
modified, staged, deleted, or committed.

The dependent `value` binder was probed first. The disposable copy reproduced
`Can't bind implicit ... value`; an explicitly typed `Nothing` together with
fully explicit `applyAction` type arguments solved the probe. The probe source
and generated TTC/TTM artifacts were removed. The resulting exact-equation
producer was then landed in checked increments.

The complete `selectedChildrenHaveNoEpisode` chain is now proved, and O8
`selectMaximalClosingEpisodeSpike` is filled. O8 passed on its first body
attempt. O9 was not edited or attempted. The research-hole census decreased
exactly once, from 17 to **16**, split **5/4/6/0/1**
(CanonicalSort/CrossTrace/DeletionChain/LocalDiamond/RenamingComposition).

## Checked proof chain

Every retained proof increment was committed only after a visible direct check
of `research/DGamma/CP5ConfluenceDeletionChainSpike.idr`, and every commit was
followed by another fresh check after deleting its terminal TTC/TTM.

### Unit A — dependent binder and retirement producer

- `9dc4391` — explicitly type the missing retirement lookup equation.
- `db53281` — produce the exact retired transition target view.
- `83c407b`, `7dc70c4` — propagate exact retired lookup evidence through local
  updates and arbitrary action traces.
- `2104165`, `9b729ec` — show retired quiet fibers are uninstalled and locate
  eventual uninstallation.
- `d5e3ff1`, `a7eee17`, `8b7b860`, `8d8eac1` — normalize future retirement,
  extract the corresponding closed episode, and extend it across trailing
  traces.

The cure is evidence-backed and matches the authorized option: the dependent
`value` family is explicitly present in the telescope/application, while the
producer owns the exact lookup equation.

### Unit B — exact-generation `NoRegisteredEpisode`

The retained chain is:

- `5b4d10a`, `a711f24` — exclude registered episodes after exact-generation
  currentness is lost and before generation birth.
- `32aa51c`, `52d471f` — globalize future closing episodes and contradict the
  selected closing's maximal ordinal.
- `65ac17f`, `16c881c`, `7637674`, `04cedcd` — establish one-step inactive and
  retirement persistence, reject begin at a retired fiber, and close the
  post-retirement segment.
- `4161bd9`, `4a90ea7`, `daece8c` — advance global prefix decompositions,
  exclude a begin with a later retirement, and cover the complete interval up
  to the promised retirement.
- `88eb751` — compose `NoRegisteredEpisode` across scanner-aligned trace
  append and across the registered-generation list.
- `6bae273`, `c827d52`, `592e560`, `e433894`, `ce8b069`, `bf46ebb` — globalize
  generated-child birth/retirement evidence, build bounded complete scans,
  split at the exact registration, project aligned head/tail evidence, and
  establish exact insertion boundary facts.
- `aa85ffa`, `2e7c59b`, `4277b1f`, `9bf4691` — prove the singleton generation
  result, connect it to inventory soundness, fold it over the full child
  inventory, and expose the requested top-level
  `selectedChildrenHaveNoEpisode` theorem.

The proof is generation-indexed throughout. It does not revive the rejected raw
name predicate: later reissues are excluded by exact current-generation lookup,
not by claiming the raw actor name can never recur.

### Unit C — O8

- `0369007` — assemble a deletable maximal candidate from exact prefix-scan
  capital.
- `c61651d` — split the finite O7 occurrence inventory without a local `with`
  or inferred view.
- `d406675` — fill `selectMaximalClosingEpisodeSpike`.

The O8 fill is only the four-line delegation from the frozen signature to the
checked list splitter. The nonempty branch chooses `MaximumBy
scannedClosingOrdinal`; the chosen occurrence is complete by the O7 scan, its
candidate receives the new no-episode proof, and its ordinal membership is
transported back into the exact O7 list. The empty branch uses
`emptyScanIsClosingFree` through the existing `NoMaximalClosingEpisode`
constructor.

## Attempt accounting

Budgets were kept per independently checkable helper unit; there was no
self-extension of an exhausted spelling.

- Unit A disposable binder probe: the first check reproduced the dependent
  `value` failure; the explicit-family probe then passed and was removed.
- Exact not-current chain: passed on attempt 2/3.
- Pre-birth chain: passed on attempt 2/3.
- Globalized closing package: passed on attempt 3/3.
- Maximality contradiction package: passed on attempt 2/3.
- The first combined retired-begin helper spelling exhausted 3/3 and was
  removed. Independent checked one-step persistence capital was retained; a
  new producer-owned retired-source boundary was then proved separately.
- Post-retirement recursion: passed on attempt 3/3.
- The first combined future-retirement no-begin spelling exhausted 3/3 and was
  removed. Its independently checked later-retirement helper was retained; the
  structurally different trace recursion then passed on attempt 1/3.
- Global generated-child capital: passed on attempt 2/3.
- Complete bounded scan: passed on attempt 2/3.
- The first combined registration-scan/alignment package exhausted 3/3 at the
  abstract-transition alignment projection. The checked scan split was kept;
  the failed alignment record was removed and replaced by two generic
  producer-owned aligned head/tail projections, which passed on attempt 1/3.
- Singleton generated-child episode exclusion: passed on attempt 3/3.
- Maximal-selection assembly: passed on attempt 2/3.
- O8 body: **1/3**, passed. No retry was needed.
- O9 body: **0/3**, untouched.

No exhausted helper was silently respelled in place. Where useful independent
capital had already checked, it was separated and committed before a materially
different producer interface was attempted.

## Adversarial review

A field-by-field self-review found no blocker:

1. **Pre-birth segment.** Scanner boundedness makes a current exact generation
   impossible before its recorded birth ordinal.
2. **Birth boundary.** The exact located O-Insert is not an L-Begin, installs an
   Inactive fiber, and makes exactly the stamped generation current.
3. **Birth-to-retirement segment.** Any registered L-Begin while the exact
   generation remains current has a future O-Retire. Final quietness turns that
   retirement into a located close; globalizing the close places its opening
   after the selected opening, contradicting the O7 maximum.
4. **Post-retirement segment.** While the generation stays current, retired and
   Inactive evidence is preserved and directly rejects L-Begin. If currentness
   changes, scanner uniqueness and the old birth bound prevent the exact
   generation from becoming current again.
5. **Raw-name reuse.** A later insertion may reuse the actor name, but it creates
   a new birth ordinal. The proof then follows the not-current branch for the
   old exact generation, so the R137 countershape remains correctly accepted.
6. **List assembly.** `combineNoRegistered` dispatches the existential ownership
   witness by `Elem` head/tail membership; it does not erase which generation
   owned the action.
7. **Non-degeneracy.** The selected candidate carries the actual O7 located
   episode, its exact inventory, prefix scan, generation-scoped dependency
   exclusion, and the newly proved global no-episode certificate. No result is
   manufactured by an empty or impossible branch in the nonempty case.

The R137 ratification fixture and R7 deletion-boundary consumer both rebuild
successfully below. The preserved `review-o6-body-adversarial.md` concerns the
frozen adjacent-swap body; its surface/hash and hidden-escape checklist were
reapplied here.

## Mandatory O9 gate and adapter mismatch

R140 stopped before `enrichDeletionChainStepSpike`, as required. Three
`contact_supervisor` decision requests were issued after O8 and before any O9
edit; all timed out without a reply. The safe default was therefore to leave O9
byte-untouched and record the mismatch rather than guessing.

The immediate CP3/CP4 adapter is not currently type-correct from the O8
candidate:

- `DeletableClosingEpisode.selectedNoDependentClose` intentionally provides
  `NoDependentClosingEpisodeForGeneration`, scoped to the selected generation's
  activation interval.
- Frozen `src/DGamma/CP3.idr` defines `deletionTheorem` with the older,
  raw-name-global `NoDependentClosingEpisode selected global` premise.
- `DGamma.CP4DeletionTheorem.deletionTheoremProof` inhabits that frozen type and
  therefore still consumes the raw global predicate.
- R137 already demonstrated why the global raw-name claim is invalid under a
  later reissue of the same actor name. It cannot honestly be derived from the
  O8 candidate.

Consequently O9 requires an explicitly authorized production/API revision (or
an alternative CP4 adapter theorem whose premise is the generation-scoped
predicate and whose proof is rebuilt accordingly). Merely coercing the scoped
predicate into CP3's raw predicate would be unsound. O9 also depends on the
still-open `deletionStepOperationalOccurrenceFoldSpike`, so even after resolving
this interface mismatch its enriched occurrence certificate remains a separate
obligation.

## Fresh validation evidence

Toolchain:

```text
Idris 2, version 0.8.0
```

Final direct spike check, after deleting only its terminal TTC/TTM:

```text
idris2 --source-dir src --source-dir research \
  --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
exit 0
```

R7 boundary consumer:

```text
idris2 --source-dir src --source-dir research --source-dir research-tests \
  --check research-tests/DGamma/R7DeletionBoundariesPositive.idr
1/1: Building DGamma.R7DeletionBoundariesPositive
exit 0
```

R137 interval/raw-name-reuse ratification:

```text
idris2 --source-dir src --source-dir research --source-dir research-tests \
  --check research-tests/DGamma/R137O8GenerationIntervalRatification.idr
1/4: Building DGamma.R137O8RawNameReuseCountershape
2/4: Building DGamma.R137O8RawNameReuseCountershapeTrace
3/4: Building DGamma.R137O8RawNameReuseCountershapeProof
4/4: Building DGamma.R137O8GenerationIntervalRatification
exit 0
```

Seeded production closure, after deleting only
`CP4ProgressProof.ttc/.ttm`:

```text
idris2 --build dgamma.ipkg
207/207: Building DGamma.CP4ProgressProof (src/DGamma/CP4ProgressProof.idr)
exit 0
```

## Frozen surfaces, holes, and hygiene

```text
src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

production diff from 34b21c9 across src/ + dgamma.ipkg:
  empty; 0 bytes; git diff --exit-code = 0

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The O8 signature is unchanged; its diff replaces only the named hole RHS. The
O9 signature and RHS remain unchanged. The current hole split is:

- CanonicalSort: 5
- CrossTrace: 4
- DeletionChain: 6
- LocalDiamond: 0
- RenamingComposition: 1
- Total: **16**

The R140 source delta contains no `believe_me`, `assert_total`, postulate,
`unsafePerformIO`, `partial`/`covering` annotation, new `with` block, or local
`let` alias. `%default total` remains in force. `git diff --check` passes. No
probe source or probe TTC/TTM remains. At the audit commit gate there are no
staged files, and the only untracked files are the three permitted baseline
paths.

## Status

- **Fully proved in R140:** dependent retirement target production and
  persistence; future-retirement close extraction; exact-generation pre-birth,
  pre-retirement, and post-retirement episode exclusion; singleton-to-list
  combination; `selectedChildrenHaveNoEpisode`; O8 maximal selection.
- **Partial/stated:** the broader DeletionChain remains partial at O9 and later
  recursive/accounting holes.
- **Next action:** obtain supervisor authorization for a generation-scoped
  CP3/CP4 Lemma-72 interface or an equivalent checked adapter; only then open
  O9's independent 0/3 body budget.
