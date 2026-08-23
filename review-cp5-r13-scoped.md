# CP5 revision-13 scoped adversarial review

Reviewed coordinate: branch `cp5-thm73-scoping`, requested HEAD
`111e3cd8157d16b51d195e0a9adb3f6a6f687384`.

Review scope was limited to the revision-13 O3 interface repair, constructive O3
closure, producer-suppliability, release harness, and frozen production boundary.
The accepted round-11/12 scoping was not re-opened.

## Verdict

**ACCEPT-WITH-CHANGES**

No rejection condition was found: both erased alignment premises are constructible
at every planned genuine producer boundary, the repaired diamond remains usable
from the immutable theorem's statement-input capital, and the closed proof has no
escape hatch or dependency on a surviving research hole. Two documentation/harness
issues should be repaired before calling revision-13 bookkeeping fully reconciled.

## Findings

### F1 — minor — `THM73-PLAN.md` contains stale inventory and release text

The executable/audited inventory is correct, but the plan is internally
inconsistent with it:

- `THM73-PLAN.md:282-287` says 27 positives, 26 negatives, and 53 tracked test
  modules. The runner and auditor contain 28 positives, 27 negatives, and 55
  tracked test modules; the fresh suite confirms those values.
- `THM73-PLAN.md:366-372` claims 24 holes while listing local diamonds as 6.
  The actual split is **6/4/8/5/1 = 24**, so local diamonds must be 5.
- `THM73-PLAN.md:431-436` still calls the release gate an external round-12
  review and again requests exact 53-module coverage, although this HEAD is the
  revision-13/O3 closure gate.

The O3 status row at `THM73-PLAN.md:341` is substantively correct, as are the
148–249 and 139–240 phase sums. This is bookkeeping, not a proof/interface flaw.

### F2 — minor — automated escape guard omits `unsafePerformIO`

`research-tests/audit-r11-claims.sh:166-174` rejects `believe_me`,
`assert_total`, `postulate`, and `%default partial`, but does not include
`unsafePerformIO`. A manual recursive scan of `research/` found none at this
HEAD, so O3 closure is clean. Adding `unsafePerformIO` to the auditor would make
future automated claims match the escape-hatch set required by this review.

## 1. Frozen production boundary

Passed exactly:

- `git diff --exit-code 34b21c9..111e3cd -- src dgamma.ipkg` produced an empty
  diff (0 bytes).
- `111e3cd:src/DGamma/CP3.idr` is blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.
- The package/source graph therefore did not absorb any research O3 artifact.

## 2. Revision-13 interface delta

At the accepted pre-repair frozen-hole manifest coordinate (`1432fb2`, parent of
`6280396`), `activationActivationDiamondSpike` had no `AlignedTransitions`
premises. Its current declaration differs by exactly these four lines:

```idris
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (0 earlyRightAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions earlyRight NoTransitions)) ->
```

Both binders are explicitly quantity 0. A manifest/signature comparison found:

- old entries: 31; current frozen surviving entries: 30;
- 30 common declarations changed: none;
- the sole removed entry is the now-filled
  `activationActivationDiamondSpike`;
- its old/current signature diff contains only the two premises above.

Thus this is the only mutation of a previously frozen hole declaration. The O3
closure necessarily added private helper declarations and filled a body; those
are implementation additions, not additional changes to accepted hole
interfaces.

Commit-level inspection also matched the claimed revision-13 split:

- `6280396`: four declaration lines only;
- `39253c1`: positive/negative probes plus runner registration;
- `270f5d1`: manifest/auditor/runner/plan bookkeeping only.

## 3. Producer-suppliability and non-weakening

I wrote an independent probe module at
`/tmp/thm73-r13-probes/DGamma/R13GenuineProducerSites.idr` and checked it with
Idris 2 0.8.0. It constructs, rather than assumes in prose, the following:

1. `pairAlignedFromExactReplayBundle`: splits `replayAligned` at an arbitrary
   exact prefix/pair/suffix decomposition using immutable `alignedAppendSplit`,
   then splits the two-node pair from the suffix.
2. O17 current and recursive sites: the current pair comes from its exact bundle;
   the recursive source is `replayAligned (swappedPremises result)`.
3. O6 whole-block site: any concrete adjacent crossing selected under its
   `sourcePremises` gets the same exact pair alignment.
4. O19 boundaries: `OperationalAdjacentBlockSwap` exposes `sourcePremises`;
   recursion exposes `blockSwapPremises`; the initial sealed realization exposes
   `canonicalReplayPremises leftCapital`; the sealed target exposes
   `operationalTargetPremises`.
5. Singleton reconstruction: a checked transition built as
   `Fired nameEq keyEq ...` immediately yields
   `AlignedStep ... NoTransitions AlignedEnd`.
6. Full consumer application: `statementAlignedConsumerCallsO3` pattern matches
   a replay bundle's aligned two-node statement-input trace, reconstructs the
   singleton `earlyRight`, and typechecks a direct call to
   `activationActivationDiamondSpike` with all of the pre-repair semantic
   premises unchanged.

The probe passed. This confirms the capital is available not only at a head-pair
fixture but under the arbitrary exact decompositions used by adjacent sorting
and block producers.

The immutable `confluenceTheorem` already requires
`AlignedTransitions ... nameEq keyEq` on both statement-input traces
(`src/DGamma/CP3.idr:3785-3810`). `ReplayInvariantBundle.replayAligned` retains
that exact indexed evidence. Identity deletion does not weaken it; replayed
swaps return a new aligned bundle. Therefore statement-input transitions are
not made unusable by the repair.

The tracked R13 negative was also checked directly. It failed with status 1 at
`independentDictionariesCannotAlign`, specifically:

```text
Mismatch between: alternateKeyEq and keyEq.
```

That is the intended boundary: arbitrary independent executable dictionaries do
not elaborate as alignment evidence.

## 4. O3 closure genuineness

### Escape and hole audit

A recursive `research/` scan found zero occurrences of:

- `believe_me`;
- `assert_total`;
- `postulate`;
- `%default partial`; or
- `unsafePerformIO`.

All five research modules use `%default total`. The closed
`activationActivationDiamondSpike` body contains no hole token, mentions no
surviving hole function, and does not recursively call itself. Its immediate
helpers have constructive definitions. The only 24 remaining hole tokens are
in the declared 6/4/8/5/1 surviving split.

### Evidence consumption

The body pattern matches `sourceAligned` into the exact two outer-dictionary
`Fired` constructors and independently pattern matches `earlyRightAligned` into
an exact singleton outer-dictionary constructor. Those matches expose the
checked equations used by the remainder of the proof. The premises are not
ignored, converted from unrelated dictionaries, or discharged by an impossible
case.

The proof then genuinely consumes:

- the checked source and reconstructed early-right executions;
- both `PaperActivationStep` witnesses and distinct actors;
- source well-formedness via preservation;
- `TraceIndependent` for framed foreign effects and iterator outcome agreement;
- checked reconstruction of the crossed left transition;
- exact replacement-binding equations; and
- constructive ordered-control replacement/commutation.

### Crossed-occurrence authentication (`1cf9d51`)

The two replacement comparisons authenticate the relevant iterator stage from
an actual occurrence in the concrete pair trace:

- left comparison uses `Left leftOccurs` for the original left node;
- right comparison uses `Right rightOccurs` for the original right node because
  the reconstructed early-right node is not an occurrence of that pair trace.

In the `Right` branch, `StageFromAdvance` uses the moved checked equation and
`movedFound`; `movedFound` is obtained from the exact foreign-lookup equality,
not fabricated. `iteratorStageOutcome` then reduces to the same component/view/
step continuation data in either occurrence branch, justifying the explicit
transport to `iteratorStageOutcomeComponentData`. This is the needed
cross-occurrence authentication and is not circular.

### Ordered controls (`db2621f`, helper introduced by `10d3160`)

Let `S` be the source binding list. The proof establishes exactly:

- original = replace right `RO` (replace left `LO` S);
- swapped = replace left `LM` (replace right `RE` S);
- `LO` is control-related to `LM` from the left replacement comparison; and
- `RO` is control-related to `RE` by symmetry of the right comparison's
  `RE`-to-`RO` relation.

`orderedControlsAfterDistinctReplacements` first relates the left replacements,
then the right replacements, producing
`replace right RO (replace left LO S)` related to
`replace right RE (replace left LM S)`. The constructive distinct-key commute
lemma rewrites the latter to the swapped order. The argument order in the final
O3 assembly matches these roles exactly. The resulting `swappedControls` claim
has the correct orientation and endpoints.

## 5. Harness and reconciliation

### Fresh suite

`research-tests/run-r11-suite.sh --fresh` passed serially:

- 5 research spikes;
- 28 positive tests;
- 27 expected-failure tests;
- exactly 33 successful fresh build markers (5 + 28);
- zero `Error:` diagnostics in the successful-suite output;
- `R11_REPRODUCIBLE_SUITE=passed`.

The R13 positive marker was present. The independently rerun R13 negative failed
at the intended dictionary index mismatch described above.

### Broad auditor

`research-tests/audit-r11-claims.sh` passed from a tracked-clean/index-clean
state and ended with:

```text
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=33
R11_REPRODUCIBLE_SUITE=passed
R12_CLAIMS_AUDIT=passed
```

Its output contained zero `Error:` diagnostics. The working tree had a
pre-existing untracked `paper/` directory, which was not touched and did not
participate in the checks.

### Manifest and holes

Independent enumeration confirmed:

- frozen manifest: 30 unique entries;
- surviving holes: 24;
- split: canonical sort 6, cross-trace 4, deletion chain 8, local diamonds 5,
  renaming 1;
- auditor constants: `(5, 28, 27)` suite categories, 55 tracked test modules,
  30 manifest entries, 24 holes, and split 6/4/8/5/1.

These executable constants match reality. The stale prose identified in F1 is
not checked by the auditor.

## Residual risks

- O6, O17, and O19 remain deliberate holes. The independent probes prove that
  their indexed inputs/recursive bundles can supply both O3 alignment premises;
  they do not claim those future producers are already implemented correctly.
- The O3 proof is checked in the research graph, not the production package, by
  design. Theorem 73 remains unproved while the other 24 holes remain.
- Current implicit-binding shadow warnings are noisy but are warnings only; both
  hardened runs had zero successful-unit `Error:` diagnostics.
- Until F2 is fixed, future `unsafePerformIO` regressions require a manual scan.

## Commands and evidence summary

- `git diff --exit-code 34b21c9..111e3cd -- src dgamma.ipkg` — passed, empty.
- `git rev-parse 111e3cd:src/DGamma/CP3.idr` — exact required blob.
- independent frozen-manifest/current-signature comparison — exactly two added
  erased alignment premises; no other common declaration changed.
- recursive escape/hole scans — passed.
- independent genuine producer/non-weakening Idris probe — passed.
- direct R13 negative Idris check — expected failure at dictionary mismatch.
- `research-tests/run-r11-suite.sh --fresh` — passed, 33 markers, zero `Error:`.
- `research-tests/audit-r11-claims.sh` — passed, zero `Error:`.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete findings F1/F2 cite THM73-PLAN.md and research-tests/audit-r11-claims.sh; proof, producer probes, harness outputs, and residual risks are documented above."
    }
  ],
  "changedFiles": [
    "review-cp5-r13-scoped.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git diff --exit-code 34b21c9..111e3cd -- src dgamma.ipkg && git rev-parse 111e3cd:src/DGamma/CP3.idr",
      "result": "passed",
      "summary": "Empty frozen production diff; exact required CP3 blob."
    },
    {
      "command": "idris2 --source-dir /tmp/thm73-r13-probes --check /tmp/thm73-r13-probes/DGamma/R13GenuineProducerSites.idr",
      "result": "passed",
      "summary": "Arbitrary decomposition, O6/O17/O19 capital, singleton reconstruction, and full O3 consumer application elaborated."
    },
    {
      "command": "idris2 --source-dir research-tests --check research-tests/DGamma/R13O3IndependentDictionaryNegative.idr",
      "result": "passed",
      "summary": "Expected rejection observed with status 1 at alternateKeyEq versus keyEq."
    },
    {
      "command": "research-tests/run-r11-suite.sh --fresh",
      "result": "passed",
      "summary": "33 fresh successful markers, 27 intended negatives, zero Error: in successful output."
    },
    {
      "command": "research-tests/audit-r11-claims.sh",
      "result": "passed",
      "summary": "Inventory, immutability, interface, hole split, arithmetic, and fresh serial suite passed."
    }
  ],
  "validationOutput": [
    "R11_FRESH_SUCCESSFUL_BUILD_MARKERS=33",
    "R11_REPRODUCIBLE_SUITE=passed",
    "R12_CLAIMS_AUDIT=passed",
    "manifest entries=30; surviving hole split=6/4/8/5/1; total=24",
    "R13 negative: Mismatch between alternateKeyEq and keyEq"
  ],
  "residualRisks": [
    "O6/O17/O19 are still holes; probes attest premise supply at their exact indexed boundaries, not completed implementations.",
    "The automated escape scan does not yet include unsafePerformIO; current research tree was manually verified clean.",
    "THM73-PLAN.md has stale 27/26/53 and local-diamonds=6 bookkeeping despite correct executable constants."
  ],
  "noStagedFiles": true,
  "diffSummary": "Adds only this scoped adversarial review report; production and research proof files remain untouched by the reviewer.",
  "reviewFindings": [
    "minor: THM73-PLAN.md:282-287,366-372,431-436 - stale runner counts, wrong local-hole subtotal, and stale round-12 release wording.",
    "minor: research-tests/audit-r11-claims.sh:166-174 - escape guard omits unsafePerformIO; manual HEAD scan is clean.",
    "no blockers or majors: producer-suppliability, non-vacuity, proof genuineness, and immutable boundaries passed."
  ],
  "manualNotes": "Verdict ACCEPT-WITH-CHANGES. Pre-existing untracked paper/ was preserved; all review probes and captured outputs are under /tmp/thm73-r13-probes/."
}
```
