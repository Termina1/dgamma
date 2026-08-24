# CP5 revision-14 scoped adversarial review

Reviewed coordinate: branch `cp5-thm73-scoping`, requested HEAD
`6d7aa98d7f4435dd5c1b23f3b7cbb069d75ec25c`.

Scope was limited to the revision-14 interface delta, the two O4 mixed-diamond
closures, retained O4 side premises, the release harness, and the frozen
production boundary. Revision-13/O3 and the accepted round-11/12 scoping were
not re-litigated.

## Verdict

**ACCEPT**

No blocker, major, or minor finding was found. In particular, all three new
erased alignment-premise occurrences are constructible at the genuine typed
O6/O17/O19 boundaries, statement-input alignment is not weakened, neither
closure uses circular or hole evidence, and both mixed diamonds reconstruct
checked transitions rather than obtaining their result vacuously.

## Findings

### N1 — note — retained parent/child exclusions are proof-unused but consumer-significant

The bodies do not inspect:

- A/O `parentSafe` at
  `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:6471-6475`; or
- O/A `childSafe` and `parentSafe` at
  `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:6702-6712`.

This is not evidence of a vacuous diamond. The raw checked reconstructions prove
a stronger property of this concrete LTS: activation replaces one existing
binding while preserving its static component and exact parent, so foreign
O-Insert/O-Retire/O-Remove guards can be reconstructed without those exclusions.
All operational premises, alignment, checked equations, well-formedness,
independence, effect commutation, and control comparisons are genuinely used.

The exclusions should nevertheless be retained. They are consumer-level causal
and licensing guards, not merely local evaluator-applicability facts. Paper
Lemma 71(2), `paper/cordis-paper.txt:2235-2261`, requires that the activation not
register the orchestration actor; the A/O parent exclusion is the host encoding
of that restriction for yielded child insertion. The reverse O/A case is an
extra sorting case and its exclusions prevent moving an activation across its
own birth/licensing insertion. The future whole-block boundary explicitly owns
generated-child safety in `AdjacentActorSwapSafety`
(`research/DGamma/CP5ConfluenceCrossTraceSpike.idr:114-140`). Removing the
premises would make the standalone raw LTS theorem stronger, but would erase an
important provenance gate from the interface consumed by sorting. They are
therefore **proof-unused, paper/provenance-significant, and harmlessly retained**,
not vestigial declarations requiring removal.

### N2 — note — repaired closed interfaces are attested at this coordinate, not kept in the current hole manifest

The current manifest deliberately has 28 entries while 22 holes survive. The
six non-hole entries are older unchanged O1/O2 declarations; the revised O3/O4
interfaces are removed when their holes close. Thus the current auditor does not
provide future drift detection for the two closed O4 signatures. This review's
coordinate-specific signature comparison supplies the requested attestation.
This matches the requested 28-entry bookkeeping and is not a revision-14
failure, but future changes to the closed O4 interfaces would require another
coordinate comparison or a separate repaired-interface manifest.

## 1. Frozen production boundary

Passed exactly:

- `git diff --exit-code 34b21c9..6d7aa98 -- src dgamma.ipkg` returned 0 with an
  empty diff.
- `6d7aa98:src/DGamma/CP3.idr` is blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.
- Worktree and index had no tracked changes before either harness run.
- The pre-existing untracked `paper/` directory was preserved and did not enter
  any build or diff.

## 2. Revision-14 interface delta

Commit `1734fdd0861017d91fc9ffe912fb563177dbd9b1` has exactly this numstat:

```text
6  0  research/DGamma/CP5ConfluenceLocalDiamondSpike.idr
```

It changes no other file. The six inserted lines are exactly three explicitly
quantity-0 `AlignedTransitions` premise occurrences:

1. A/O `activationOrchestrationDiamondSpike`: source pair only (two lines);
2. O/A `orchestrationActivationDiamondSpike`: source pair and singleton
   `earlyRight` (four lines).

There are no deletions or other edits in that commit. A direct declaration diff
from the revision-13 reviewed coordinate `111e3cd` to HEAD found exactly those
two and four added lines respectively.

An independent manifest/declaration comparison found:

- revision-13 manifest entries: 30;
- current manifest entries: 28;
- removed entries: exactly the now-filled A/O and O/A declarations;
- added entries: none;
- 28 common manifest entries changed: none;
- 28 common current declarations differing from their manifest signatures:
  none; and
- `orchestrationOrchestrationDiamondSpike` directly unchanged from `111e3cd` to
  HEAD.

Thus O/O is untouched and no other frozen declaration changed.

## 3. Producer-suppliability and non-weakening

I wrote and checked an independent 320-line probe at
`/tmp/thm73-r14-probes/DGamma/R14GenuineProducerSites.idr` with Idris 2 0.8.0.
It constructs the evidence rather than accepting an equality between executable
dictionaries.

### Exact adjacent-pair capital

`pairAlignedFromExactReplayBundle` starts with an arbitrary exact decomposition

```text
prefix ++ left :: right :: suffix = original
```

and `ReplayInvariantBundle ... nameEq keyEq original`. It splits
`replayAligned` first at the prefix and then after the two-node pair using the
immutable `alignedAppendSplit`, yielding exactly:

```text
AlignedTransitions ... nameEq keyEq
  (MoreTransitions left (MoreTransitions right NoTransitions))
```

Separate A/O and O/A wrappers require the corresponding
`PaperActivationStep`/`PaperOrchestrationStep` orientations and elaborate with
the same construction. Alignment is orientation-independent, but these wrappers
confirm that both intended call shapes retain it.

### Genuine boundaries

The probe rechecked all requested boundaries:

- O6 arbitrary whole-block crossing: exact source bundle plus exact pair
  decomposition;
- O17 current pair: the same decomposition construction;
- O17 recursion: `replayAligned (swappedPremises result)`;
- O19 current `OperationalAdjacentBlockSwap`: its indexed `sourcePremises`;
- O19 recursive source: `blockSwapPremises step`;
- O19 initial sealed realization: `canonicalReplayPremises leftCapital`;
- O19 sealed target: `operationalTargetPremises selected`; and
- for each O19 bundle above, a second exact decomposition extracts the concrete
  adjacent pair rather than stopping at whole-trace alignment.

A genuine O/A producer evaluates the early activation with the outer
`nameEq`/`keyEq`, constructs
`Fired nameEq keyEq ... earlyChecked`, and constructs its singleton alignment
definitionally with `AlignedStep ... AlignedEnd`.

### Statement-input consumers

Two full consumer probes accept only statement-dictionary
`AlignedTransitions` for the source pair plus the pre-repair semantic premises:

- A/O calls `activationOrchestrationDiamondSpike` directly;
- O/A constructs the checked early transition and singleton alignment and then
  calls `orchestrationActivationDiamondSpike` directly.

Both return the immutable `LocalRelationalDiamond` type. No `DecEq` equality,
caller-selected effect map, arbitrary evaluator output, or independently stored
transition proof was added. This establishes non-weakening for consumers holding
only the theorem's aligned statement-input capital.

The tracked R14 negative was also checked directly and failed with status 1 at
`independentMixedPairCannotAlign`, specifically:

```text
Mismatch between: alternateKeyEq and keyEq.
```

That is the intended rejection boundary. The tracked positive and the broader
independent probe both succeed.

## 4. Closure genuineness

### Escape, holes, and recursion

A recursive scan of every Idris file under `research/` found zero occurrences of:

- `believe_me`;
- `assert_total`;
- `postulate`;
- `%default partial`; or
- `unsafePerformIO`.

All five research modules use `%default total`. Exactly 22 hole tokens remain,
with split 6/4/8/3/1.

A conservative local identifier-reachability scan from each body traversed 91
local declarations for A/O and 79 for O/A. Neither closure reached any of the
three surviving hole functions in the local-diamond module. Neither exact body
contains a hole token or surviving-hole name, and each closure name occurs in
its body region only on the defining left-hand side: there is no self-recursion.

### Alignment and premise use

A/O pattern matches `sourceAligned` into the exact two outer-dictionary
`AlignedStep` constructors. O/A does the same and independently pattern matches
`earlyRightAligned` into the exact singleton constructor. These are ordinary
constructor matches, not impossible/vacuous eliminations. The extracted
`leftChecked`, `rightChecked`, and `earlyChecked` equations drive checked action
projection, preservation, reconstruction, effect framing, occurrence
witnessing, and endpoint assembly.

Apart from the retained exclusions assessed in N1, the semantic premises are
used repeatedly: action/tag transport, paper rule witnesses, actor distinction,
source well-formedness, and `TraceIndependent` all enter constructive helpers or
the final branches.

### Rule-by-rule orchestration reconstruction

For A/O, `orchestrationRawBeforeCheckedActivation`
(`CP5ConfluenceLocalDiamondSpike.idr:5477-5669`) reconstructs the later
orchestration at `first` by all three paper constructors:

- **OInsert:** extracts the successful insertion plan at `middle`, transports
  absence across the distinct activation replacement, transports parent
  presence across replacement, transports provision disjointness using exact
  static-component preservation, and constructs the fresh checked insertion;
- **ORetire:** extracts the successful lookup and transports it back across the
  distinct replacement before constructing the checked retirement; and
- **ORemove:** transports lookup, normalizes the source removable guard, and
  transports exact `hasChild` through static-parent preservation before
  constructing the checked deletion.

For O/A, `orchestrationRawAfterCheckedActivation`
(`CP5ConfluenceLocalDiamondSpike.idr:5403-5470`) reduces the early activation to
an exact static replacement and calls the rule-by-rule
`orchestrationRawAfterForeignReplacement` (`:2223-2361`). Its OInsert, ORetire,
and ORemove branches reconstruct the same guards after that replacement. No
case is defaulted or excluded by contradiction.

### Exact child relation

`hasChildInStaticReplacement` and `hasChildStaticReplacement`
(`CP5ConfluenceLocalDiamondSpike.idr:2163-2203`) prove Boolean equality of the
whole child fold, not merely preservation of `False`. At the replaced entry they
use the successful lookup to identify the old fiber exactly and static-parent
equality to preserve `isChildOf`; all other entries recurse unchanged. The A/O
ORemove reconstruction uses this exact equality in the required reverse
direction. The O/A reconstruction uses the established production
`hasChildReplaceFalse` with the same exact static-parent premise. This validates
the `fd17200` claim.

### Comparisons, effects, and controls

Both closures authenticate activation replacement comparisons against concrete
occurrences in the exact two-node trace:

- A/O left activation: source `first -> middle`, `Left leftOccurs`;
- O/A right activation: source `middle -> originalFinal`, moved
  `first -> earlyRightFinal`, `Left rightOccurs`.

Iterator outcome agreement is transported with `TraceIndependent`; O/A reverses
that agreement constructively with
`localIteratorOutcomeAgreementSymmetric`. Effect outputs are obtained by the
mixed pair effect-output helpers, and checked endpoint construction relates the
actual original endpoint to the swapped endpoint.

The symmetry helpers introduced by `1a6e777` are structurally correct:
`activationReplacementComparisonSymmetric` swaps both before/after pairs, old
and replacement fibers, lookup/static facts, registry/binding shapes, and
symmetrizes the fiber-control relation;
`orderedControlsSymmetric` recursively symmetrizes every binding relation.

#### `swappedControls` endpoint orientation

O/A uses the ordered-control assembler directly:

```text
orchestration: first -> middle
activation:    middle -> originalFinal
early act.:    first -> earlyRightFinal
moved orch.:   earlyRightFinal -> swappedFinal
```

Its comparison is source `middle -> originalFinal`, moved
`first -> earlyRightFinal`, so the assembler returns exactly
`controls(originalFinal, swappedFinal)`.

A/O reuses the same assembler with authenticated roles exchanged:

```text
orchestration: first -> earlyRightFinal
activation:    earlyRightFinal -> swappedFinal
early act.:    first -> middle
moved orch.:   middle -> originalFinal
```

`activationReplacementComparisonSymmetric leftComparison` has exactly the
required source `earlyRightFinal -> swappedFinal`, moved `first -> middle`
orientation. Consequently the assembler first returns
`controls(swappedFinal, originalFinal)` as `reverseControls`, and the explicit
`orderedControlsSymmetric` produces the required
`controls(originalFinal, swappedFinal)`. This matches the final
`LocalRelationalDiamond.swappedControls` endpoints in both bodies.

## 5. Harness and bookkeeping

Both required commands ran serially from a tracked-clean and index-clean state.
No Idris process was concurrent, no process was killed, and no retry/seeded
fallback was needed.

### Fresh suite

`research-tests/run-r11-suite.sh --fresh` passed with:

```text
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=34
R11_REPRODUCIBLE_SUITE=passed
```

Independent output counts found exactly 34 `Building DGamma...` markers, 28
negative headers, and zero `Error:` diagnostics in successful output.

### Broad auditor

`research-tests/audit-r11-claims.sh` passed and ended with:

```text
R12_RUNNER_INVENTORY=passed
R11_FRESH_SUCCESSFUL_BUILD_MARKERS=34
R11_REPRODUCIBLE_SUITE=passed
R12_CLAIMS_AUDIT=passed
```

It likewise had 28 negative headers and zero successful-output `Error:`
diagnostics.

Independent inventory enumeration confirms:

- spikes / positives / negatives: 5 / 29 / 28;
- tracked Idris test modules: 57, each occurring exactly once in the runner;
- frozen manifest entries: 28;
- surviving holes: 22, split 6/4/8/3/1;
- phase rows: 9–9, 32–55, 15–26, 14–27, 7–13, 27–47, 39–64,
  and 5–8;
- total: 148–249; B–H remaining: 139–240; and
- `THM73-PLAN.md` contains the revision-14-only interface authorization, O4
  complete row, shifts 18–20, exact current split, and scoped review gate.

## Residual risks

- O6, O17, and O19 remain deliberate holes. The independent probes establish
  exact premise supply at their indexed current, recursive, initial, and sealed
  boundaries; they do not prove the future implementations of those holes.
- Theorem 73 remains unproved while the other 22 research obligations survive.
- The two repaired O4 signatures are no longer in the current hole-interface
  manifest after closure; this report attests them at the reviewed coordinate,
  as described in N2.
- The worktree had the pre-existing untracked `paper/` directory throughout;
  tracked files and the index were clean before validation.

## Commands and evidence summary

- `git diff --exit-code 34b21c9..6d7aa98 -- src dgamma.ipkg` — passed, empty.
- `git rev-parse 6d7aa98:src/DGamma/CP3.idr` — exact required blob.
- independent revision-13/current manifest and declaration comparison — exact
  +2/+4 O4 delta; no common frozen change; O/O unchanged.
- independent recursive escape/hole/call-graph scans — passed.
- `idris2 --source-dir /tmp/thm73-r14-probes --check /tmp/thm73-r14-probes/DGamma/R14GenuineProducerSites.idr`
  — passed.
- direct R14 negative check — intended `alternateKeyEq`/`keyEq` rejection.
- `research-tests/run-r11-suite.sh --fresh` — passed, 34/28/zero Error.
- `research-tests/audit-r11-claims.sh` — passed, 34/28/zero Error.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "N1/N2 and the closure sections cite concrete file paths and lines; producer probes, interface diffs, proof-genuineness checks, harness output, and residual risks are recorded."
    }
  ],
  "changedFiles": [
    "review-cp5-r14-scoped.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git diff --exit-code 34b21c9..6d7aa98 -- src dgamma.ipkg && git rev-parse 6d7aa98:src/DGamma/CP3.idr",
      "result": "passed",
      "summary": "Empty frozen production diff and exact required CP3 blob."
    },
    {
      "command": "independent manifest/declaration comparison from 111e3cd to 6d7aa98",
      "result": "passed",
      "summary": "Exactly +2 A/O and +4 O/A alignment lines; 28 common entries unchanged; O/O unchanged."
    },
    {
      "command": "idris2 --source-dir /tmp/thm73-r14-probes --check /tmp/thm73-r14-probes/DGamma/R14GenuineProducerSites.idr",
      "result": "passed",
      "summary": "O4 orientations, arbitrary pair decomposition, O6/O17/O19 current/recursive/sealed boundaries, singleton construction, and both full statement-input consumers elaborated."
    },
    {
      "command": "idris2 --source-dir research-tests --check research-tests/DGamma/R14O4IndependentDictionaryNegative.idr",
      "result": "passed",
      "summary": "Expected status-1 rejection at alternateKeyEq versus keyEq was observed."
    },
    {
      "command": "research-tests/run-r11-suite.sh --fresh",
      "result": "passed",
      "summary": "34 fresh successful markers, 28 intended negatives, and zero Error: diagnostics in successful output."
    },
    {
      "command": "research-tests/audit-r11-claims.sh",
      "result": "passed",
      "summary": "Inventory, immutability, interfaces, escapes, hole split, plan arithmetic, and serial fresh suite passed."
    }
  ],
  "validationOutput": [
    "R11_FRESH_SUCCESSFUL_BUILD_MARKERS=34",
    "R11_REPRODUCIBLE_SUITE=passed",
    "R12_CLAIMS_AUDIT=passed",
    "manifest entries=28; surviving holes=22; split=6/4/8/3/1",
    "R14 negative: Mismatch between alternateKeyEq and keyEq"
  ],
  "residualRisks": [
    "O6/O17/O19 remain holes; probes attest exact capital at their typed boundaries, not completed implementations.",
    "Theorem 73 remains unproved with 22 research holes.",
    "Closed repaired O4 signatures are coordinate-attested here but are not retained by the current hole manifest."
  ],
  "noStagedFiles": true,
  "diffSummary": "Adds only this scoped adversarial review report; reviewer probes and outputs remain under /tmp/thm73-r14-probes/.",
  "reviewFindings": [
    "note: research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:6471-6475,6702-6712 - retained exclusions are unused by the stronger raw LTS reconstruction but remain consumer-significant provenance/paper guards.",
    "note: research-tests/cp5-hole-interface-baseline.json - the requested 28-entry manifest excludes the two repaired closed O4 declarations, so future drift is not automatically guarded.",
    "no blockers, majors, or minors"
  ],
  "manualNotes": "Verdict ACCEPT. Pre-existing untracked paper/ was preserved. Validation was strictly serial with at most one Idris process; no SIGKILL, retry, or seeded fallback occurred."
}
```
