# CP5 revision-19 assembled-boundary scoped adversarial review

**Reviewed branch:** `cp5-thm73-scoping`  
**Reviewed HEAD:** `eef4d79e21fcc3c4da666ad8ef336d2fa3a0954c`  
**Landing range:** `17fc7df..eef4d79` (`04b1570..eef4d79`)  
**Probe root:** `/tmp/thm73-r19-probes/`  
**Verdict:** **ACCEPT-WITH-CHANGES**

The frozen Idris boundary itself passed the adversarial checks. One major
bookkeeping change is required: the current reconciliation section of
`THM73-PLAN.md` still reports the retired hole and contradicts both the actual
20-hole tree and the new release-boundary text. Per the review rules, I did not
edit the plan; this report is the only repository change.

## Numbered findings

### 1. [major] The plan's current hole reconciliation was not fully updated

The landed plan correctly says that the boundary retires the false fold and
leaves 20 holes with split `6/4/8/1/1` at `THM73-PLAN.md:415-436` and again at
`THM73-PLAN.md:861-877`. However, its purported current obligations/reconciliation
section still says:

- “21 obligations” (`THM73-PLAN.md:738-740`);
- “21 deliberate named research holes” (`THM73-PLAN.md:768-773`);
- local diamonds = 2 (`THM73-PLAN.md:775-779`);
- O6 = 3 (`THM73-PLAN.md:786-791`); and
- sum = 21 (`THM73-PLAN.md:793`).

The independent scan found the real split to be canonical/cross/deletion/local/
renaming = `6/4/8/1/1`, sum 20. The manifest also removes exactly the retired
fold. This is not a type-boundary defect, but it is a material contradiction in
the landed bookkeeping and is why the verdict is not unconditional ACCEPT.

**Required change:** update the current reconciliation prose/list/O-map in
`THM73-PLAN.md` to 20, local = 1, and O6 = 2. Historical revision-11 narrative
may remain explicitly historical.

### 2. [pass] A is both consumer-needed and producer-suppliable at all five constructor sites

`LocalRelationalDiamond.movedPairAligned` is erased and indexed by the exact two
moved projections (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:539-555`).
The live whole-alignment consumer uses that exact field rather than detached
capital (`research-tests/DGamma/R23CorrectedInternalFixturePositive.idr:1787-1790`).
My independent `R19OwnMovedAlignmentConsumerPositive` probe appended
`movedPairAligned diamond` to an arbitrary aligned replayed tail and elaborated.

All five non-declaration `MkLocalRelationalDiamond` sites supply the field:

1. A/A uses `alignedMovedPairWithCheckedTail ... earlyRightAligned ...`
   (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:8221-8226`);
2. A/O constructs an exact two-step `AlignedStep` value after rewriting the
   producer-owned checked endpoint (`...LocalDiamondSpike.idr:8450-8461`);
3. O/A uses `alignedMovedPairWithCheckedTail` (`...LocalDiamondSpike.idr:8661-8665`);
4. O/O uses the same helper on `earlyRight safety`
   (`...LocalDiamondSpike.idr:8943-8951`); and
5. the suffix-free full-certificate fixture supplies `replayAligned source`
   (`research-tests/DGamma/R19SuffixFreeFullAdjacentCertificatePositive.idr:307-324`).

The helper itself reconstructs both steps under the outer dictionaries from the
checked producer path (`...LocalDiamondSpike.idr:571-594`). My independent
old-boundary “sixth producer” deliberately supplied every former field but no
moved alignment; Idris rejected it exactly by trying to unify
`movedRightAction` with the new `AlignedTransitions` field. Thus the new field is
not cosmetic, and an old-style producer cannot silently bypass it.

### 3. [pass] B's suffix spine is sealed and is not Option D in disguise

The type is exported but its constructors are not. An external attempt to build
even `SealedSuffixReplayEnd` failed with “SealedSuffixReplayEnd is private”
(`/tmp/thm73-r19-probes/log-R19OwnSpineForgeNegative.txt`). The recursive node
owns exact source/replayed heads and tails, action/tag equality, singleton RAR,
head-map equality, endpoint, occurrence correspondence, relative ordinal, and
then a spine indexed by **those exact** `sourceTail`/`replayedTail`
(`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:843-882`). The recursive
argument is not a function or fresh arbitrary-tail quantification
(`...LocalDiamondSpike.idr:878-882`).

A structural extraction of exactly that data declaration reported
`spine_has_bundle=False` and `spine_exact_recursive_tail=True`; there is no
`ReplayInvariantBundle` in the spine. External output-shaped injection also
fails at the outer seal: `MkAdjacentSwapResult` is private
(`/tmp/thm73-r19-probes/log-R19OwnAdjacentConstructorForgeNegative.txt`).

### 4. [pass] C's opaque facade faithfully preserves all nine former APIs

At `17fc7df`, the nine public record fields were `replayedFinal`,
`replayedSuffix`, `swappedTrace`, the two decompositions, external order, RAR,
endpoint, and target bundle
(`17fc7df:research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:855-870`). The live
opaque record stores corresponding private `adjacent*` fields and the two erased
seals (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:888-925`). Each former
name is a direct alias to its corresponding internal field:

- `replayedFinal` at `:929-942`;
- `replayedSuffix` at `:944-958`;
- `swappedTrace` at `:960-974`;
- `originalDecomposition` at `:976-991`;
- `swappedDecomposition` at `:993-1009`;
- `swappedSameExternalInputs` at `:1011-1025`;
- `swappedReplayCorrespondence` at `:1027-1042`;
- `swappedEndpoint` at `:1044-1059`; and
- `swappedPremises` at `:1061-1076`.

My independent positive probe reconstructed a record with the exact prior nine
field types exclusively through that public facade and elaborated. An attempt
to name the internal `adjacentReplayedFinal` failed because the projection is
private, and an external `MkAdjacentSwapResult` construction failed because the
constructor is private. A non-erased attempt to return `sealedSuffixReplay`
failed with a quantity/accessibility error, while both seals are usable in an
erased consumer (`...LocalDiamondSpike.idr:1078-1111` and the positive facade
probe). This attests opacity, facade fidelity, and erasure.

### 5. [pass] D retires the false theorem honestly and preserves the historical evidence

The unrestricted live declaration is absent. `swappedOccurrenceFold` is now
exactly `sealedOccurrenceFold result`
(`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:1113-1122`). The manifest
removed only `adjacentSwapOperationalOccurrenceFoldSpike`, and the actual named
hole total fell from 21 to 20.

The impossibility proof remains self-contained: it defines the retired
unrestricted record locally (`research-tests/DGamma/R18OccurrenceFoldArbitrarySuffixImpossibilityPositive.idr:43-76`),
quantifies the retired producer contract rather than the live hole (`:78-106`),
and derives `Void` by forcing a target ordinal-two suffix occurrence into a
two-node source (`:107-138`). The old open adjacent-envelope claim is likewise
preserved as a local `RetiredOpenAdjacentSwapResult` (`research-tests/DGamma/R11GenericRawPlanRepackagerPositive.idr:12-49`)
with an explicitly caller-fed historical materializer (`:51-89`), not silently
recast as authority to construct the live opaque type. Both modules were in the
fresh passing suite (`research-tests/run-r11-suite.sh:31-32,55`).

### 6. [pass] E cannot be detached from the producer path

`headMapPreserved` is adjacent to `headRAR` and indexed by the exact constructor
heads (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:853-868`). My
independent attack accepted a detached theorem of precisely that type and tried
to pass it to `SealedSuffixReplayStep`; Idris rejected the attempt because the
constructor is private
(`/tmp/thm73-r19-probes/log-R19OwnDetachedHeadMapNegative.txt`). There is no live
constructor use outside the declaration, and `adjacentSwapSuffixSpike` accepts
no map premise (`...LocalDiamondSpike.idr:9034-9055`).

The concrete provenance prototype retains both exact source/target head-map
equality and target identity inside its producer-owned envelope
(`research-tests/DGamma/R23CorrectedInternalFixturePositive.idr:1420-1436`), and
constructs them before projection (`:1546-1592`). This is the required placement,
not post-hoc caller capital.

### 7. [pass] `adjacentSwapSuffixSpike` is byte-identical and has no new premise

I extracted bytes from the first byte of
`0 adjacentSwapSuffixSpike :` through the final byte of its named-hole RHS, both
from `17fc7df` and HEAD. Both blobs are 1183 bytes, compare equal, and hash to:

```text
e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41
```

The current declaration is at
`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:9034-9055`; the manifest's
pinned text is at `research-tests/cp5-hole-interface-baseline.json:148-152`.
Consequently A/B/C/D/E added no caller premise to the suffix theorem.

### 8. [pass] `r29TargetBundle` is closed and accepts no output-shaped premise

`r29TargetBundle` is a zero-argument constant, not a function accepting target
capital (`research-tests/DGamma/R29RetainedFinishTargetBundlePositive.idr:70-77`).
My independent module imported it and consumed the complete
`ReplayInvariantBundle` with no arguments.

Its dependency chain is constructive and ordered:

- reached-from-empty comes from the exact target trace, retained alignment, and
  source initial facts (`...R29RetainedFinishTargetBundlePositive.idr:21-25`);
- provenance, protocol/parent ranks, precedence, and support well-foundedness are
  derived at `:27-58`;
- support/active matching consumes the checked target trace and already-derived
  target invariants at `:60-68`; and
- all fields assemble at `:70-77`.

The critical target heads are generated by `r27ProduceMapRetainedFinish` from a
checked source head, source well-formedness/lookup, and the current relational
endpoint (`research-tests/DGamma/R23CorrectedInternalFixturePositive.idr:1438-1450`),
with target checked execution and next endpoint derived internally (`:1450-1592`).
The pair endpoint is constructed from the genuine local diamond
(`:1614-1617`), and whole alignment consumes the new moved-pair field
(`:1787-1790`). No target bundle, target independence, target map, or target
endpoint is an input to `r29TargetBundle`.

### 9. [pass, subject to Finding 1] The manifest delta matches the pre-declared A/B/C/D/E package

The independent JSON comparison found:

- hole interfaces `27 -> 26`, removing only
  `adjacentSwapOperationalOccurrenceFoldSpike`;
- approved record fields `2 -> 5` (A plus the two C seals);
- approved type additions `0 -> 1` (B);
- approved constructor revisions `0 -> 2` (B/E spine constructors and opaque C
  adjacent constructor); and
- approved projection revisions `0 -> 1` (D).

The landed manifest records these at
`research-tests/cp5-hole-interface-baseline.json:170-255`, and the hardened audit
checks their counts, signatures, audit coordinate, constructor visibility claim,
and retired declaration absence at
`research-tests/audit-r11-claims.sh:164-221`. This matches the revision-29
pre-declaration (`research-tests/O6-R29-FINISH-MAP-END-TO-END-AUDIT.md:117-187`).
The only reconciliation defect is the stale current plan text in Finding 1.

### 10. [pass] Immutable production, build, suite, and escape-hatch boundaries hold

Independent checks established:

- `src/` and `dgamma.ipkg` have an empty diff from `34b21c9`;
- `src/DGamma/CP3.idr` has Git blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`;
- the package lists 207 unique modules;
- an exact external archive, seeded from the byte-identical production cache and
  with the terminal interface removed, rebuilt
  `207/207: Building DGamma.CP4ProgressProof` with no `Error:` diagnostic;
- the forced-fresh serial suite passed all five spikes, 45 positives, and 41
  intended negatives, reporting 50 successful fresh build markers;
- there are no `believe_me`, `assert_total`, `unsafePerformIO`, declaration-form
  `postulate`, or `%default partial` hits in tracked Idris code; and
- actual research holes are exactly `6/4/8/1/1 = 20`, with no test holes.

All compilation occurred in `/tmp/thm73-r19-probes`; the repository's build tree
was not used as a write target.

### 11. [pass with residual proof risk] The boundary is forward-viable for the O6 body

The intended producer can now proceed without a caller-supplied output:

1. split the source bundle's checked alignment and other trace invariants
   (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:438-462`);
2. seed replay after the pair from `swappedEffects`,
   `swappedControlEquivalent`, and `swappedWellFormed`, while taking the moved
   checked pair from `movedPairAligned` (`:545-569`);
3. recurse over the exact source suffix. At each source head, reconstruct the
   same checked action/tag at the related control state, retain exact map
   equality before projecting the target transition, construct singleton RAR,
   endpoint, occurrences, and relative ordinal, then seal the exact recursive
   tail in `SealedSuffixReplayStep` (`:853-882`);
4. compose prefix identity, the already-authorized pair external-order proof,
   and suffix replay (`:8964-9029`);
5. construct the global occurrence fold from the exact pair plus sealed suffix,
   not from an arbitrary replayed suffix; and
6. build the whole target bundle in the order demonstrated end-to-end by R29,
   then call the private `MkAdjacentSwapResult` with all nine outputs and two
   erased seals (`:888-925`).

This closes the historical chain at the correct ownership points: controls are
in the diamond; pair external order is the one pre-existing explicit premise;
occurrence authenticity is producer-sealed; moved alignment is in the diamond;
and map retention is per checked replay head. No new output-shaped premise
appears in the public theorem type.

The residual risk is proof effort, not an exposed unsound boundary: the general
head replay/map-retention lemma and the global ordinal fold are not yet
implemented, and there is intentionally no live `MkAdjacentSwapResult` use while
`adjacentSwapSuffixSpike` remains the sole local-diamond hole at
`...LocalDiamondSpike.idr:9055`. R29 proves a nonempty two-finish target-bundle
case, not the generic recursion. The first general body must therefore remain a
mandatory review gate.

## Probe inventory

All files below are review-owned and untracked under `/tmp/thm73-r19-probes/`.

| Probe | What it proves |
|---|---|
| `external/DGamma/R19OwnMovedAlignmentConsumerPositive.idr` + `log-R19OwnMovedAlignmentConsumerPositive.txt` | Exact `movedPairAligned` feeds arbitrary replay-tail whole alignment. |
| `external/DGamma/R19OwnOldSixthProducerNegative.idr` + matching log | Every former diamond field is insufficient; the missing new alignment is the rejection boundary. |
| `external/DGamma/R19OwnSpineForgeNegative.idr` + matching log | Even the empty sealed spine cannot be forged externally. |
| `external/DGamma/R19OwnDetachedHeadMapNegative.idr` + matching log | A detached exact head-map theorem cannot enter the private step constructor. |
| `external/DGamma/R19OwnAdjacentConstructorForgeNegative.idr` + matching log | `MkAdjacentSwapResult` is inaccessible externally. |
| `external/DGamma/R19OwnInternalFieldNegative.idr` + matching log | The renamed internal adjacent projections are private. |
| `external/DGamma/R19OwnRuntimeSealLeakNegative.idr` + matching log | The erased public suffix seal cannot be returned at runtime. |
| `external/DGamma/R19OwnFacadePositive.idr` + matching log | All nine prior public types reconstruct one prior-shaped view; both seals work at quantity 0. |
| `external/DGamma/R19OwnTargetBundleNoPremisePositive.idr` + matching log | `r29TargetBundle` is consumable with no output-shaped argument. |
| `structural-audit.txt` | Frozen hash, no spine bundle, exact recursive tail, five producer sites, manifest delta, 20-hole split. |
| `adjacentSwapSuffixSpike.no-trailing-newline.blob` | Exact 1183-byte frozen function blob. |
| `hygiene-and-plan-audit.txt` | Baseline/CP3/package/escape checks and the stale-plan contradiction. |
| `log-seeded-package-207.txt` | Exact seeded terminal rebuild reaches 207/207 with no `Error:`. |
| `log-full-suite-fresh.txt` | Forced-fresh serial suite passes with 50 positive build markers and all 41 intended rejections. |

## Residual risks

1. The plan inconsistency in Finding 1 must be corrected before calling the
   landing fully reconciled.
2. `adjacentSwapSuffixSpike` is intentionally still a hole; the generic replay
   proof may expose additional lemma work even though the public boundary no
   longer asks for output-shaped capital.
3. The concrete R29 fixture covers two replayed empty-program L-Finish heads;
   it is strong end-to-end evidence but not a substitute for the general
   action/tag recursion.

## Repository hygiene

Before adding this report, `git status --short` contained only the pre-existing
untracked `paper/` directory. This report is the sole added/staged/committed
path. No source, research declaration, manifest, test, package, or plan file was
modified by the reviewer.
