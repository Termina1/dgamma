# R192 owner decision memo: A8 / A10 / candidate A11

Research-only; no surface change authorized or implemented. Production `src/`
and `dgamma.ipkg` remain frozen against `34b21c9`, including CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0`. A8/O17 remains paused. O19 and
`adjacentSwapSuffixSpike` remain frozen. No O21 withdrawal proof is consumed.

## Candidate A11: removed historical names (bounded side-analysis D1)

Supervisor ruling following `440bfdb3`: **candidate A11**, countershape-first,
in the same premise/conclusion-mismatch family as A9. Do not interpret the
fixture as a counterexample to the full protected O20 theorem.

### Exact offending research clause

`CP5ConfluenceCrossTraceSpike.idr:537-562` concludes
`CanonicalConvergenceResult ... operational`; its `convergenceBridge` field is
`ReplayedCanonicalEndpointBridge`. In
`CP5ConfluenceRenamingCompositionSpike.idr:1794-1816` the fourth field is:

```idris
0 replayedGeneratedBirthMatched :
  {child, parent : name} ->
  {component : Component key value world error} ->
  (replayedOccurrence : LocatedGeneratedRegistration child parent component
    replayedLeftTrace) ->
  (sourceOccurrence : LocatedGeneratedRegistration child parent component
    (canonicalTrace (canonicalSchedule leftCapital)) **
    (sourceOccurrence = replayGeneratedRegistrationOrigin replayedOccurrences
      replayedOccurrence,
     (rightOccurrence : LocatedGeneratedRegistration
       (renameForward (expectedBridgeBijection sameInputs) child)
       (renameForward (expectedBridgeBijection sameInputs) parent) component
       (canonicalTrace (canonicalSchedule rightCapital)) **
       generationForward (generatedGenerationBijection sameInputs)
         (registrationGeneration
           (replayGeneratedRegistrationOrigin
             (canonicalOccurrenceCorrespondence leftCapital)
             sourceOccurrence)) =
       registrationGeneration
         (replayGeneratedRegistrationOrigin
           (canonicalOccurrenceCorrespondence rightCapital)
           rightOccurrence))))
```

There is **no current-generation, endpoint-presence, support, or retention
premise** on `replayedOccurrence`. `LocatedGeneratedRegistration` (CP3:2124)
locates an historical insertion by its exact before/after subtraces; a later
Remove does not invalidate that occurrence. `expectedBridgeBijection`
(:1743-1752) is precisely `currentNameBijection (endpointRenaming sameInputs)`,
not the historical `RegistrationGenerationBijection`.

The first three bridge clauses concern final ambient, table lookups and
`MaybeFiberRelatedBy` at final registries. They do not independently quantify
over removed historical births. Clause 3's exact all-name relation can be a
separate vestigial-domain risk; A11 does not silently bless or change it.

### What frozen production actually asks for

CP3 `confluenceTheorem` (:3785-3810) concludes `ConfluenceResult` at the accepted
generation bijection and accepted current-name bijection. `ConfluenceResult`
(:3756-3777) contains:

- both `CanonicalSchedule` values;
- `finalRegistrationCorrespondence : RegistrationCorrespondenceByGeneration`;
- `finalEndpointRenaming : CurrentEndpointRenaming`;
- `finalEndpointsEquivalent : SystemEquivalentByRenamingModuloVestigial`.

Historical tree matching is still required, but **by generation**, independently
of current raw names. `SystemEquivalentByRenamingModuloVestigial` (:3080-3104)
asks for exact final ambient, final table lookups under the current bijection,
and `EndpointFiberRelatedModuloVestigial` at each final registry lookup.
The latter (:3033-3071) distinguishes exact Maybe-fiber correspondence,
one-sided present/absent vestigial cases and bilateral unrelated vestigial
cases. A vestigial package (CP3:2850ff) retains the exact current/discarded birth
stamp, fiber presence, retired+clean inactive state, empty owned table, no
children and unsupportedness. **Absent/absent names need no vestigial fiber or
historical current-name equation.**

Thus the frozen production conclusion does not require the research fourth
clause for removed historical raw names. This is a research-surface
strengthening, not a demonstrated need to strengthen frozen CP3 premises.
Source audit found no implemented consumer of `replayedGeneratedBirthMatched`:
its bridge is passed to the still-open `replayedCanonicalToOriginalEndpointSpike`
(:2701-2735). This is not proof that every future endpoint argument is complete;
it is evidence that no current checked consumer forces the stronger clause.

### Compiled countershape and its exact limits

`R192RemovedBirthCurrentNameProbe` (A18-A28) owns six actual native edges:
Insert root0, Begin0, Insert child1, Finish0, Retire1, Remove1. It inhabits full
`SameOrchestrationModuloGenerated` (all E8 fields), all four
`CurrentEndpointRenaming` fields, and nonvacuous E9 Retire/Remove matching.
Generation(1,2) maps to itself. The accepted CURRENT bijection swaps absent1/2,
fixing live root0. Exact original child1 birth exists, child1 is proved
unsupported, and no insertion at mapped name2 exists anywhere in the trace.

It refutes deriving the historical raw-name bridge from E8+Current(+E9) alone.
Full `UniqueRawNameInsertions`, independent canonical capital, and the sealed
operational replay triangle are not packaged, so it does NOT refute
`canonicalSchedulesConvergeSpike` or production confluence.

### Minimal proposed research weakening — OWNER GATE, NOT AN EDIT

| Existing clause | Proposed disposition | Producer/obligation |
| --- | --- | --- |
| 1 ambient equality | unchanged | paired actual effect induction |
| 2 all-name table lookup equality | unchanged | paired ordered-table projection plus inert/absent empty tables |
| 3 exact all-name Maybe-fiber relation | initially unchanged; separately audit vestigial-domain compatibility before any alteration | native controls + explicit original endpoint vestigial transport |
| 4 arbitrary historical replayed birth under current raw map | restrict fixed-current-name matching to **original supported/current non-vestigial generations**; preserve exact source-origin and historical-generation equations there | existing `supportedReplayedBirthBridge` owns the supported branch |
| Remaining unsupported histories | keep generation-only matched-or-authentically-closing classification, **not** a fabricated current raw-name birth | `o20CanonicalOriginMatchOrClosing`; no O21 withdrawal consumption |
| Present unmatched endpoint remainder | require the FULL accepted-scanner `VestigialEndpointGeneration` package on the present side(s) | separate checked endpoint disposition, never merely `isSupported=False` |
| Removed/absent endpoint remainder | exact absent lookup(s); no vestigial package can be invented for a nonexistent fiber | actual Remove frame / finite registry proof |

A naive `current` guard on child alone is not enough: parent may be vestigial;
using the existing original-**supported** child condition is the smallest
already-owned fourth-clause restriction and also owns supported ancestors.
Any broader current/non-vestigial version needs explicit parent mapping proof.
Do not replace the fourth field by a generic assumed endpoint conclusion.

Fixture plan before any migration: (1) finish uniqueness and full canonical
capital for the removed-child trace with the accepted construction pattern;
(2) show production final equivalence accepts the absent-name swap; (3) positive
supported-child fixed-name bridge; (4) present vestigial on one/both sides with
all inertness/scanner fields; (5) reject a present active or non-discarded
"vestigial" fake; (6) preserve exact generation/origin stamps under independent
parent schedules and reject an alternate coherent occurrence map. Then update
only the reviewed research bridge/call sites under a separately adapted guard.
Production statement strengthening is NOT recommended from A11 evidence.

## A8 / A10: production unfreeze versus research fork

A8 is an O17-only **initial-placement construction dependency**, not an absent
O20 hypothesis: accepted O20 capital already owns initial all-root placement.
Do not reopen O17 as a side effect of this memo.

A10 is the generated-child Retire/Remove placement problem. R191 has eleven
actual edges, full replay premises and all three frozen block values; child3
retirement lies in the physical gap between actor1 and actor2. It does not have
full canonical decomposition/capital and therefore is not yet a protected
selector counterexample. The frozen actor-only grammar permits child Insert,
not Retire/Remove. List adjacency and root-first placement do not prove the
actual `betweenBlocks` trace empty.

| Option | Benefit | Owner cost / risk | Recommendation |
| --- | --- | --- | --- |
| Production unfreeze | unify eventual grammar/runtime semantics | touches frozen CP3/API and proofs; A8/O17 and A10 decisions still pending; raw historical bridge would still be over-strong | do not do in R192 |
| Research-only extended block grammar | test actual generated-child Retire/Remove at physical cuts without changing production | needs provenance, liveness, installed-state and physical zero-gap evidence; no coercion to old grammar | bounded Unit C probe, then owner review |
| Silently coerce zero gap / add hidden applicability oracle | no legitimate benefit | would assume the selector's missing safety conclusion | prohibited |

Unit B keeps a single explicitly named `ZeroGapPending` boundary; actual
right-first Begin/selection wiring is still being investigated. Unit C probe
results will be appended before final freeze. No selector body this shift.

## Status

A11 exact clause/downstream audit complete as one bounded analysis side-unit;
no surface edits and no extra compiler invocation. Unit B/C results pending.
