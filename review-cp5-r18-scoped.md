# CP5 revision-18 scoped adversarial review

Reviewed coordinate: branch `cp5-thm73-scoping`, requested HEAD
`c9c18d862d7137e4c196c1aafcbf3c78f64b6e65`, diff base `fb753b0`.
The accepted revision-13/revision-14 material, revision-15 premises, local O5
body, revision-17 `ControlEquivalent` repair, and round-11/12 scoping were not
re-litigated.

## Verdict

**ACCEPT-WITH-CHANGES**

Revision 18 repairs the revision-17 blocker without introducing caller-supplied
whole-trace authority. The new premise is erased and indexed by the exact source
pair and the exact moved pair of the supplied `LocalRelationalDiamond`.
Independent probes construct it for genuine block-internal crossings and stable
internal/root sorting crossings, including state-sensitive moved root retire and
remove classification reconstructed from checked foreign transitions. Distinct
root/root transpositions are excluded at the new consumer boundary, while the
tracked current-interface full-result impossibility proof remains total.

One minor bookkeeping defect remains: the plan's old runner inventory paragraph
still reports 29 positives, 28 negatives, and 57 tracked tests although the
current authoritative inventory is 34 positives, 30 negatives, and 64 tracked
test modules. This is not an over-broad proof or producer claim and does not
undermine the repair, but it should be corrected.

## Findings

### M1 — minor — stale suite counts in the plan

`THM73-PLAN.md:416-422` says the runner contains five spikes, 29 positives, 28
expected failures, and 57 tracked Idris test modules. The checked runner and
auditor contain five spikes, 34 positives, 30 expected failures, and 64 tracked
test modules. `THM73-PLAN.md:591-593` already uses the correct 64-module test
inventory, so the document is internally inconsistent.

Required change: update the older paragraph to 34 positives, 30 negatives, and
64 tracked test modules. The stale figures are under-counts, not a repeated
claim that the O6 proof or full pipeline is complete.

### N1 — note — the pair-local narrowing is exact and non-circular

The only frozen hole declaration changed from `fb753b0` is
`adjacentSwapSuffixSpike`. Its delta is exactly one four-line erased premise at
`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:8794-8797`:

- source: exactly `left`, then `right`, then `NoTransitions`;
- target: exactly `movedRight diamond`, then `movedLeft diamond`, then
  `NoTransitions`; and
- no quantified or caller-selected original/swapped endpoint trace.

All other 26 frozen hole declarations are byte-identical to `fb753b0`.
`adjacentSwapOperationalOccurrenceFoldSpike` and `adjacentSwapSuffixSpike` still
have exactly their named hole bodies. The local-spike file delta is additive-only
(71 additions, zero removals), comprising the premise and the two framing
lemmas. `LocalRelationalDiamond`, `AdjacentSwapResult`, the occurrence fold, O5,
and the finite/nonempty finite derivations are unchanged.

`sameExternalAppendSpike` structurally recurses over the first relation at
`:8713-8744`. `framePairExternalOrderSpike` at `:8749-8774` accepts only separate
prefix identity, exact pair, and suffix relations and composes them. It does not
accept the desired whole-trace result as an input. The independent positive
`reviewWholeTraceFraming` in
`/tmp/thm73-r18-probes/DGamma/R18IndependentReview.idr` typechecks this exact
composition. The independent negative
`/tmp/thm73-r18-probes/DGamma/R18UnrelatedPairNegative.idr` attempts to supply a
relation for different moved transition terms and is rejected at
`unrelatedPair` with `Mismatch between: unrelatedLeft and movedLeft`.

The actual O6 body remains a named hole, as required by the scope. Thus this
review attests the non-circular interface and its checked framing consumer, not a
claim that the future O6 body already uses it.

### N2 — note — genuine O19 and stable O17 producer capital is inhabited

The independent total module
`/tmp/thm73-r18-probes/DGamma/R18IndependentReview.idr` does not import the
tracked R18 probe. It fresh-typechecks and independently proves:

- `reviewBeginNode` from an exact checked `BeginStep`;
- `reviewBodyHeadNode` by eliminating both constructors of
  `ActorLifecycleOnly`, covering ordinary lifecycle and yielded-child insertion;
- `reviewO19BeginBegin`, `reviewO19BeginBody`, `reviewO19BodyBegin`, and
  `reviewO19BodyBody`, covering all opening/body Cartesian forms on both sides;
- moved-side internal classification only through
  `movedRightAction`/`movedLeftAction`; and
- `reviewO17InternalRootFromBundle`, whose alignment is projected from the exact
  two-step `ReplayInvariantBundle` accepted at the sorter boundary.

For the stable mixed case, `reviewCheckedForeignLookup` derives foreign lookup
framing from `checkedActionProjects`, `applyActionLocalUpdate`, and
`systemLocalUpdateForeign`. `reviewMovedRootAfterCheckedForeign` eliminates all
three `RootOrchestrationStep` constructors. Its `RootRetireStep` and
`RootRemoveStep` branches transport the actual source fiber lookup through that
checked transition and retain the source fiber's actual `Root` parent; neither
branch accepts a moved root classification or registry equality as a premise.

The tracked implementation has the same genuine boundary:

- exact block forms and mixed Cartesian producers at
  `research-tests/DGamma/R18ExternalOrderProducerPositive.idr:16-173`;
- checked foreign lookup derivation at `:178-198`;
- internal/root moved retire/remove reconstruction at `:204-260`;
- root/internal moved retire/remove reconstruction at `:286-356`; and
- final stable pair relations at `:360-442`.

The fresh suite typechecks the tracked R18 module. The source confirms that the
moved ORetire/ORemove classification is derived, rather than assumed.

### N3 — note — narrowing excludes root/root without making genuine sorting vacuous

The tracked `R17FullResultImpossibility` still targets the current unchanged
`AdjacentSwapResult` and succeeds in the fresh suite. Its ordinal proof forces an
empty replayed suffix for the exact two-node case (`research-tests/DGamma/
R17FullResultImpossibility.idr:15-105`), and its external-relation inversion and
root-insert specialization remain at `:107-200`.

The independent `reviewRootRootPairPremiseImpossible` additionally inverts the
new exact pair-local premise itself. It proves that a source/moved first-node
root/root pair with distinct actions makes that premise `Void`. Root/root is
therefore excluded before `adjacentSwapSuffixSpike` can be called, rather than
hidden behind its result hole.

This does not remove a pair required by the accepted canonical strategy:

- O17's output stores a finite derivation and `sortedSameInputs` at
  `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:119-123`, while canonical
  placement only requires root inputs before lifecycle work at `:145-148`.
  Stable hoisting retains the root subsequence and uses internal/root or
  root/internal crossings; it has no target obligation to reorder roots.
- O19's accepted source is an exact `ActorBlockDecomposition` of
  `LocatedOpenEpisodeBlock`s at
  `research/DGamma/CP5ConfluenceCrossTraceSpike.idr:43-73,839-853`. A block is
  its L-Begin opening plus an `ActorLifecycleOnly` body, so every Cartesian node
  has one of the independently checked internal forms. The operational block
  producer must store a nonempty finite derivation and whole external relation at
  `:638-712`; O20 consumes only the sealed operational package at `:1003-1115`.

O17 and O19 remain proof holes, so there is no completed literal call chain to
inspect. The checked evidence establishes premise availability for the stable
O17 strategy and every O19 block-node form represented by the accepted
interfaces; construction of those full derivations remains the declared future
obligation.

## Immutability and manifest audit

Passed:

- `git diff 34b21c9..c9c18d8 -- src dgamma.ipkg` is empty.
- `HEAD:src/DGamma/CP3.idr` and the worktree blob are exactly
  `2c697e532e83989de8591fa6a4378747c6a501c0`.
- Across commits `22ccdfe`, `b24de6f`, `ae97e2b`, `1a7c0fa`, and `c9c18d8`, the
  only research spike changes are 71 additive lines: the one authorized
  signature premise plus framing lemmas.
- The frozen-signature comparison against `fb753b0` reports exactly
  `['adjacentSwapSuffixSpike']`; its signature adds four lines and deletes none.
- The manifest records exactly the revision-18 authorization and retains the two
  accepted revision-17 record fields.
- There are 21 holes with split `6/4/8/2/1`; no hole was added, moved, or renamed.
- No escape hatch occurs in `research/` or `research-tests/`.

## Full theorem assembly

`research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr:72-86` still
declares exactly:

```idris
0 r16ConfluenceTheoremAssembly :
  confluenceTheorem name key value world error
```

The module is total, hole/escape-free, constructs both theorem-input bundles,
and calls `fullPipelineFromBundles`. It fresh-builds against the current 21-hole
pipeline. As documented, this is exact assembly through research holes, not a
proof that those holes are filled.

## Harness results

All Idris invocations were serial. There was no SIGKILL, retry, or seeded
fallback.

`research-tests/run-r11-suite.sh --fresh` passed with:

```text
SPIKES=5
POSITIVES=34
NEGATIVES=30
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=39
R11_REPRODUCIBLE_SUITE=passed
```

The captured successful output contains zero `Error:` diagnostics. Every one of
the 30 negatives failed and satisfied its module-specific diagnostic and source
symbol check.

`research-tests/audit-r11-claims.sh` passed with:

```text
R12_RUNNER_INVENTORY=passed
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=39
R11_REPRODUCIBLE_SUITE=passed
R12_CLAIMS_AUDIT=passed
```

The audit correctly validates the current inventory, production isolation,
authorized signature/field manifest, hole split, phase arithmetic, escape scans,
and runner harness. It does not detect the stale prose counts in finding M1.

## Residual risks

- Theorem 73 remains unproved with 21 named research holes.
- `adjacentSwapOperationalOccurrenceFoldSpike` and `adjacentSwapSuffixSpike`
  remain holes. The new framing lemmas establish the exact intended external
  composition, but the eventual O6 implementation still must use them correctly.
- O17's stable sorter and O19's complete Cartesian block replay remain holes.
  The probes establish local capital availability, not those recursive
  algorithms or their termination.
- The independent probes are intentionally under `/tmp/thm73-r18-probes/` and
  are not tracked.
- Idris emits existing implicit-shadowing warnings in the research pipeline;
  there were no errors.
- The worktree had a pre-existing untracked `paper/` directory throughout the
  review. It was not modified or staged.

## Commands and evidence summary

- production diff, CP3 blob, 27-signature comparison, additive spike diff, named
  hole bodies, hole split, escape scan, and exact R16 declaration — passed;
- independent O19 opening/body/yielded-child and stable internal/root positive
  module — passed;
- independent unrelated-pair index negative — rejected at the intended exact
  moved-transition mismatch;
- independent root/root pair-premise `Void` proof — passed;
- tracked R17 current-result impossibility, tracked R18 producer, and exact R16
  assembly — fresh-built in the suite;
- `research-tests/run-r11-suite.sh --fresh` — passed 39/30/zero Error;
- `research-tests/audit-r11-claims.sh` — passed.
