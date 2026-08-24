# CP5 revision-15/revision-16 scoped adversarial review

Reviewed coordinate: branch `cp5-thm73-scoping`, requested HEAD
`5f9d45cecccbfce049f7d313d52f27569dde1999`.

Scope was limited to revision 15's O/O dictionary-alignment premises, revision
16's `LocalRelationalDiamond.swappedControls` retirement, constructive O5
closure, the R16 theorem-assembly probe, and the release harness. Accepted
revision-13/O3, revision-14/O4, and round-11/12 scoping were not re-litigated.

## Verdict

**REJECT**

Revision 15 and the local O5 body pass their scoped checks. Revision 16 does not
remove the structural ordered-control obstruction from the adjacent-swap
pipeline: it removes the field from `LocalRelationalDiamond`, but the unchanged
`AdjacentSwapResult.swappedEndpoint` still contains
`RelationalReplayEndpoint.replayedControls`, which demands the same impossible
`OrderedRegistryControlsRelated` relation for a suffix-free distinct
O-Insert/O-Insert transposition. The R16 theorem-assembly test elaborates only
because both O6 producers remain holes.

## Findings

### B1 — blocker — ordered-control impossibility is transferred to O6, not retired

The local field is gone at
`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:550-576`, but the suffix
replay endpoint still requires:

- `RelationalReplayEndpoint.replayedControls` at `:479-490`; and
- `AdjacentSwapResult.swappedEndpoint` at `:850-879`.

The structural facts independently re-derived from production definitions are:

1. `insertBinding` prepends (`src/DGamma/Coeffects.idr:86-91`).
2. Therefore checked left-then-right insertion has endpoint heads
   `right :: left :: source`, while checked right-then-left has
   `left :: right :: source`. `checkedApplyAction` cannot alter this raw endpoint
   (`src/DGamma/Calculus.idr:1414-1426,5829-5847`).
3. `OrderedRegistryControlsRelated` requires the same actor at both heads in its
   only cons constructor (`src/DGamma/CP4DeletionRelationalBoundary.idr:20-32`).
   Distinct actors make the relation uninhabitable.
4. O6's occurrence contract prevents hiding extra transitions after a swapped
   pair when the source suffix is empty: any third target node is in the
   `AdjacentSuffixOrdinal` region and must originate at source ordinal 2, but a
   two-node source has no such occurrence
   (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:790-817`).

A fresh total Idris probe at
`/tmp/thm73-r16-probes/DGamma/R15R16IndependentReview.idr` typechecks all four
steps constructively:

- `checkedInsertSwapEndpointControlsImpossible` derives the opposing endpoint
  heads from four actual checked evaluator equations and rejects the ordered
  relation;
- `emptySuffixReplayEndpointImpossible` rejects the unchanged
  `RelationalReplayEndpoint` at those exact endpoints;
- `pairFoldForcesEmptyReplayedSuffix` proves the operational occurrence fold
  forces an empty replayed suffix for a two-node source with empty suffix; and
- `suffixFreeInsertSwapResultImpossible` combines the current
  `AdjacentSwapResult`, `swappedOccurrenceFold`, and endpoint requirements into
  `Void` for a genuine distinct O-Insert/O-Insert diamond.

Consequently the two O6 holes at `:824-843` and `:8426-8446` cannot both be
filled for the O5 case that revision 16 was intended to unblock. The
`r16ConfluenceTheoremAssembly` success does not refute this: its call through
`R8FullPipeline` reaches the current 21-hole pipeline, so the O6 holes supply the
impossible values as unresolved metavariables. This violates the substantive
full-coverage/retirement claim even though the assembly file itself is
hole-free.

Required repair: retire or replace the ordered relation in
`RelationalReplayEndpoint` and every authenticated downstream consumer, or
provide a different producer-authenticated permutation/name-indexed endpoint
relation. Excluding O-Insert/O-Insert would instead abandon the stated O5 case.
Either repair is a new scoped interface revision.

### N1 — note — tracked R15 positive does not itself index the singleton by a safety value

`research-tests/DGamma/R15O5AlignedProducerPositive.idr:31-68` builds a singleton
for a freshly checked transition but does not construct
`OrchestrationSwapSafety` and return alignment indexed by the exact
`earlyRight safety`. This is not a premise-suppliability failure: the independent
probe's `outerProducerCallsO5` constructs the old safety record around the same
outer-dictionary `Fired` transition, constructs
`AlignedTransitions ... (MoreTransitions (earlyRight safety) NoTransitions)`
definitionally, and invokes `orchestrationOrchestrationDiamondSpike`. The tracked
probe is simply weaker than its “exactly the two erased inputs” comment suggests.

## 1. Frozen production boundary

Passed exactly:

- `git diff 34b21c9..5f9d45c -- src dgamma.ipkg` is empty.
- `HEAD:src/DGamma/CP3.idr` and the worktree file are blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.
- Production does not import research CP5 modules.
- The pre-existing untracked `paper/` directory was preserved.

## 2. Revision-15 declaration delta and producer capital

An independent comparison of the 28 frozen declarations at accepted revision-14
coordinate `117f179` and revision-15 bookkeeping coordinate `b5f2a20` found one
changed declaration only: `orchestrationOrchestrationDiamondSpike`. Its delta is
exactly:

- erased source-pair `AlignedTransitions`;
- naming the pre-existing anonymous `OrchestrationSwapSafety` argument `safety`;
  and
- erased singleton `AlignedTransitions` indexed by the exact
  `earlyRight safety`.

There are no added/removed manifest entries and no other common signature
changes. `OrchestrationSwapSafety` is byte-identical from `117f179` through HEAD.
The reviewed O3/O4 bodies were byte-identical through the pre-retirement
coordinate `a926996`.

The independent producer probe constructs, rather than assumes:

- arbitrary exact prefix/pair/suffix extraction from `replayAligned` via two
  `alignedAppendSplit` applications;
- O/O-oriented source capital at O6;
- O17 recursive capital from `swappedPremises`;
- O19 current capital from `sourcePremises`, recursive capital from
  `blockSwapPremises`, initial sealed capital from `canonicalReplayPremises`, and
  target sealed capital from `operationalTargetPremises`; and
- a complete statement-dictionary O5 application with the exact dependent
  singleton built simultaneously with `OrchestrationSwapSafety`.

The probe passed under Idris 2 0.8.0. The tracked independent-dictionary negative
failed at the intended declaration with status 1 and:

```text
Mismatch between: alternateKeyEq and keyEq.
```

Thus revision 15 is producer-suppliable and does not weaken statement-input
aligned capital.

## 3. Revision-16 mechanical retirement checks

The mandatory literal checks pass:

- `git grep swappedControls -- '*.idr'` returns zero matches.
- `git diff a926996..821c143` changes one file by 3 insertions/5 deletions:
  exactly the record field's two lines and one positional constructor argument at
  each of the three closed O3/O4 sites. Their proof-producing local bindings and
  bodies are otherwise unchanged.
- There are no hidden projections, declarations, or literal consumers at this
  coordinate.
- The original structural impossibility claim is correct, as independently
  proved in B1.

The mechanical removal therefore matches its commit claim. The failure is that
an equivalent ordered endpoint obligation survives under a different field name.

## 4. R16 theorem assembly

`research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr` passes the
specified syntactic checks:

- `%default total`;
- public erased declaration exactly
  `r16ConfluenceTheoremAssembly : confluenceTheorem name key value world error`;
- no holes or escape hatches;
- `canonicalPremisesFromTheoremInputs` derives provenance, final well-formedness,
  protocol ranks, parent ranks, precedence acyclicity, support well-foundedness,
  and active-support matching from immutable theorem inputs;
- two separate `MkReplayInvariantBundle` values are reconstructed for the left
  and right traces; and
- the complete call to `fullPipelineFromBundles` typechecks.

The runner correctly places this test immediately after `R8FullPipeline`.
However, this is interface assembly against holes, not a constructive proof that
retirement removed all downstream demand for the field. B1 shows the specific
O6 obligation concealed by those holes.

## 5. O5 closure genuineness

The local O5 theorem body itself is constructive and correctly scoped:

- recursive scans of `research/` and `research-tests/` Idris files find no
  `believe_me`, `assert_total`, `postulate`, `%default partial`, or
  `unsafePerformIO`;
- the body contains no hole, surviving-hole name, or self-call;
- conservative same-module call-graph reachability visits 57 local declarations
  and reaches no surviving hole;
- source alignment is deconstructed for both source transitions and the
  dependent singleton alignment is independently deconstructed
  (`CP5ConfluenceLocalDiamondSpike.idr:8317-8325`);
- the extracted outer checked equations drive raw replay, effect commutation,
  endpoint checking, and moved transitions.

All nine rule pairs are covered:

- early/right ORetire uses the actual checked retirement as a static replacement;
  `orchestrationRawAfterForeignReplacement` reconstructs left OInsert, ORetire,
  and ORemove (`:2272-2412`);
- early/right ORemove uses actual checked deletion;
  `orchestrationRawAfterDelete` reconstructs all three left rules, while
  `insertionParentOutsideFromLaterRemove` derives the child-parent exclusion from
  the actual later successful ORemove (`:2510-2561,2789-2990`); and
- early/right OInsert reconstructs all three left rules directly. In the
  insert/insert branch, provision compatibility is obtained from the actual
  later checked right insertion and symmetry, not assumed; in the remove/insert
  branch, parent exclusion is obtained from the actual later insertion after
  deletion (`:3023-3380`).

The direct O/O effect proof matches production `partialEffectMapFor` semantics:
OInsert/ORemove set the acting table empty, ORetire is identity, distinct table
updates commute, and the endpoint relation is oriented from `originalFinal` to
the checked swapped endpoint (`:5070-5405`; production semantics at
`src/DGamma/Metatheory.idr:1191-1210`). The final constructor uses the exact
`earlyRight safety`, checked moved-left transition, commuted effects, and target
well-formedness (`:8391-8424`).

O5 is therefore a genuine **local** diamond. B1 concerns its mandatory downstream
splicing interface, not these nine checked reconstructions.

## 6. Harness and bookkeeping

Both required commands ran serially from a tracked/index-clean state. No Idris
process was concurrent, killed, retried, or seeded.

`research-tests/run-r11-suite.sh --fresh` passed with:

```text
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=36
R11_REPRODUCIBLE_SUITE=passed
```

Independent counts found 36 successful build markers, 29 intended-negative
headers, and zero `Error:` diagnostics in successful output.

`research-tests/audit-r11-claims.sh` passed with:

```text
R12_RUNNER_INVENTORY=passed
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=36
R11_REPRODUCIBLE_SUITE=passed
R12_CLAIMS_AUDIT=passed
```

Independent inventory confirms:

- spikes / positives / negatives: 5 / 31 / 29;
- 60 tracked test modules, each registered exactly once;
- frozen manifest: 27 unique entries;
- surviving holes: 21 with split 6/4/8/2/1; and
- phase arithmetic: 148–249 total, 139–240 implementation-remaining.

Those constants are mechanically correct. The status claims at
`THM73-PLAN.md:73-91,393-404,486,522-524` are not semantically consistent with
B1: O5 cannot be called closed in the whole pipeline while the accepted O6
endpoint contract remains uninhabitable for its suffix-free insert/insert case.

## Residual risks

- Twenty-one research holes remain and Theorem 73 is not proved.
- The independent blocker probe is intentionally under
  `/tmp/thm73-r16-probes/`, not tracked in the repository.
- Repairing B1 requires a new endpoint-relation design and a scoped re-review;
  mechanically removing only `RelationalReplayEndpoint.replayedControls` may
  affect endpoint composition and downstream canonical convergence.
- The R15 tracked positive should eventually be strengthened to construct the
  exact safety-indexed singleton, although independent review established the
  premise is genuinely suppliable.

## Commands and evidence summary

- frozen production diff/blob checks — passed;
- independent frozen-signature comparison — only the authorized O/O revision-15
  delta;
- `git diff a926996..821c143` and zero `swappedControls` grep — passed;
- independent producer plus structural/O6 impossibility Idris probe — passed;
- direct R15 intended-negative check — rejected at the expected dictionary
  index;
- research escape/hole/call-graph scans — passed;
- `research-tests/run-r11-suite.sh --fresh` — passed 36/29/zero Error;
- `research-tests/audit-r11-claims.sh` — passed 36/29/zero Error.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Blocker B1 cites the surviving endpoint-control requirements and immutable ordered/prepending definitions; N1, validation evidence, and residual risks cite concrete paths and declarations."
    }
  ],
  "changedFiles": [
    "review-cp5-r15-r16-scoped.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git diff 34b21c9..5f9d45c -- src dgamma.ipkg && git rev-parse HEAD:src/DGamma/CP3.idr",
      "result": "passed",
      "summary": "Frozen production diff empty; CP3 blob exactly 2c697e532e83989de8591fa6a4378747c6a501c0."
    },
    {
      "command": "test -z \"$(git grep swappedControls -- '*.idr' || true)\" && git diff a926996..821c143 -- research/DGamma/CP5ConfluenceLocalDiamondSpike.idr",
      "result": "passed",
      "summary": "Zero surviving identifiers; retirement diff is only the field and three positional constructor arguments."
    },
    {
      "command": "idris2 --source-dir /tmp/thm73-r16-probes --check /tmp/thm73-r16-probes/DGamma/R15R16IndependentReview.idr",
      "result": "passed",
      "summary": "O6/O17/O19 producer capital, exact safety-indexed singleton, evaluator-derived head transposition, retained endpoint impossibility, empty-suffix occurrence theorem, and simultaneous O6-result contradiction all elaborate."
    },
    {
      "command": "idris2 --source-dir research-tests --check research-tests/DGamma/R15O5IndependentDictionaryNegative.idr (wrapped to require status 1 and intended diagnostic)",
      "result": "passed",
      "summary": "Expected rejection at independentEarlyOrchestrationCannotAlign: alternateKeyEq versus keyEq."
    },
    {
      "command": "research-tests/run-r11-suite.sh --fresh",
      "result": "passed",
      "summary": "36 successful markers, 29 intended negatives, zero Error: diagnostics."
    },
    {
      "command": "research-tests/audit-r11-claims.sh",
      "result": "passed",
      "summary": "Inventory, immutability, signatures, escapes, 27-entry manifest, 21-hole split, arithmetic, and fresh suite passed."
    }
  ],
  "validationOutput": [
    "R11_FRESH_SUCCESSFUL_BUILD_MARKERS=36",
    "R11_REPRODUCIBLE_SUITE=passed",
    "R12_RUNNER_INVENTORY=passed",
    "R12_CLAIMS_AUDIT=passed",
    "manifest=27; surviving holes=21; split=6/4/8/2/1",
    "R15 negative: Mismatch between alternateKeyEq and keyEq",
    "Independent Idris theorem suffixFreeInsertSwapResultImpossible : current suffix-free insert/insert AdjacentSwapResult -> Void"
  ],
  "residualRisks": [
    "Theorem 73 remains unproved with 21 research holes.",
    "RelationalReplayEndpoint.replayedControls preserves the same structural OInsert/OInsert obstruction that revision 16 removed only locally.",
    "The R16 theorem assembly cannot detect the obstruction because the two O6 producers are holes.",
    "A replacement permutation/name-indexed endpoint relation requires a new scoped design and downstream review."
  ],
  "noStagedFiles": true,
  "diffSummary": "Adds only this scoped adversarial review report; all code and tracked tests remain untouched by the reviewer.",
  "reviewFindings": [
    "blocker: research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:479-490,824-879,8426-8446 - revision 16 transfers the impossible ordered-control relation to RelationalReplayEndpoint/AdjacentSwapResult; simultaneous O6 closure is constructively contradictory for suffix-free distinct OInsert/OInsert.",
    "note: research-tests/DGamma/R15O5AlignedProducerPositive.idr:31-68 - tracked positive does not itself construct the exact safety-indexed singleton, although the independent review probe proves it producer-suppliable.",
    "no separate O5 proof blocker: all nine checked rule pairs, both alignments, effects, and endpoint orientation are constructive."
  ],
  "manualNotes": "Verdict REJECT. Pre-existing untracked paper/ was preserved. All reviewer probes and outputs are under /tmp/thm73-r16-probes/. Validation was strictly serial; no SIGKILL, retry, or seeded fallback occurred."
}
```
