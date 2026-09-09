# R204 → R205 handoff (no R205 work authorized here)

R204 baseline9b532666; retained source freeze3e6d8ff0.29 total erased support
declarations, B14/A16 caps reached; A15 STOP3/3 fully reverted. Both mandatory
R203 P1/P2 repairs landed before B1 (af2df90b/c254d5a1). C INELIGIBLE;
full O20/Thm73 closure and census4=1/2/0/0/1 unchanged.

## FIRST: R205 production unfreeze and required rebuild

The final owner ruling designates R205 the **PRODUCTION-UNFREEZE shift, not a
proof shift**. Use the owner-signed patch at
`origin/cp5-thm73-lane-a8a10:research-tests/O6-L2R15-CP3-TIER1-SIGNED-DIFF.patch`:
7 hunks, `src/DGamma/CP3.idr` only,31,798 bytes, SHA256
`42d957748fcc67ff534c33a6c369eded4bad65e0f37e5c72e4539b737a68fb8a`.
Pinned ref snapshot6f85af32e54d5c2709c6b76d2cdda833ea362ec1. The owner reports
apply-check PASS on56d1269b; R204 performed read-only git-object inspection,
not apply/rebuild and not lane2 worktree access. Authority:
O6-R204-R205-PRODUCTION-UNFREEZE.json and O6-R204-OWNER-FINAL-GATE.md.

Follow the signed patch scope, finish the owner-required rebuild and establish
the new production/source baseline BEFORE proof work. Do not run unchanged
R204 freeze guards after unfreezing CP3. The following visibility candidate
is the **first PROOF micro-unit AFTER the rebuild**, under its separate prior
gate. Earlier “FIRST micro-unit” wording below is historical parent steering,
not permission to bypass production unfreeze/rebuild or R205 scope/budget.

## Candidate FIRST PROOF micro-unit AFTER rebuild: visibility companion, PRIOR GATE REQUIRED

Parent steering: **visibility-only companion (export → public export, no
type/body change) on those two projections is a candidate FIRST micro-unit
for R205 under gate (recorded V on the module + import-closed re-validation
of its dependents), after which the two-path append equality may be
re-stated ONCE as a NEW micro-unit (different premises: reducible
projections), not as a retry of the exhausted statement.**

The two whole-path projections are o20OccurrenceHistoryLeftPath and
 o20OccurrenceHistoryRightPath in CP5O20OccurrenceStampedHistorySpike.
Their export-only opacity, unlike public-export stamped-edge projections,
is a source-level probable cause of A15's conversion failure, NOT a tested
new theorem or permission to edit during R204. Reducibility changes the
elaboration context, not the paper/runtime hypotheses. The two-path and
narrowed left-only R204 statements remain exhausted. Do not start the new
proof until the visibility companion is gated, separately recorded/checked,
and its affected import closure is re-validated. Keep that future equality in
the original ChronologicalOccurrenceHistorySpike context, which defines
o20OccurrenceHistoryAppend; moving it elsewhere introduces a further export
boundary not covered by this two-prefix candidate. No visibility change has
been written to an Idris file during R204.

Exact hypothetical delta:14 bytes total, two unique export-prefix replacements;
no type/body/runtime data or frozen fields changed. Candidate manifest:
O6-R204-R205-VISIBILITY-CANDIDATE.json. Recompute source hashes and closure at
R205 start; the below list is a snapshot, not a license to reuse stale tests.

| Proposed topological validation target | R204 current source SHA256 |
|---|---|
| `research/DGamma/CP5O20OccurrenceStampedHistorySpike.idr` | `ec06bdfd0d8f20ffe04a2b8d8d42cedce67b98f8fe2e957441d348ba98c15195` |
| `research/DGamma/CP5O20CanonicalSynchronizationModuloSpike.idr` | `ebddcdfaca9a421500bd8de9c4efdb7302ae6f4c6f9815ce333c26bfbcdd1990` |
| `research/DGamma/CP5O20InsertOccurrenceHistorySpike.idr` | `3c928e581c65dabf7a15b49e0dc2ba9b6004a46d69efd4c4f9f579c13e482677` |
| `research-tests/DGamma/R198OccurrenceStampedHistoryPositive.idr` | `376b419f9bad0a3a19df04e24831411ebe01d83baf6993279ff01c59f9066c40` |
| `research/DGamma/CP5O20ChronologicalOccurrenceHistorySpike.idr` | `5967fa8438bee25461153e53b1379d1e6e7dc01995ebfddbaaa232d3a0acb183` |
| `research-tests/DGamma/R204InsertOccurrenceHistoryPositive.idr` | `54b1196cabf00d8a7540419aae993f8560c2d35149f2ed976ccf3689ffa0d842` |
| `research-tests/DGamma/R204NativeChronologicalBirthPositive.idr` | `8fda11ccd281eed876d83849734d79059c63e54dde9946182866699dacb71b87` |

## Actual B frontier

Proved: present-vestigial selected-list adapter; real-chain current absence
including non-head selections and both canonical endpoints; any-present
original controls/current-name agreement and exact replay count/stamp
transport. B14 supplies original/canonical current stamps and the replay
map equality, NOT O20AllNameCut.

Missing: transport all parent/provider control names and absent-domain
lookups under the conjugated history/current map into full allNameEffects
and allNameControls. Then the bridge must use the ACTUAL chain result;
do not retry the exhausted R197 generic if-projection consumer, call
frozen deletionTheoremProof, or cast scoped control relations to raw ones.
No stronger macro premise or stored field is authorized by this handoff.

## Actual A frontier

A6 produces one-edge histories for actual supplied words; A7 includes native
prefix scans; A8 supplies actual canonical/permuted physical histories plus
both original insertion attachments for supported births. A10/A11 locate
every retained birth/open suffix in both ORIGINAL chronologies. A12/A13
pair chosen matching original events conditionally: event match + local
child/parent name equations are explicit. A14 only composes exact matching
intermediate cuts. Three real nonempty fixtures are retained.

Missing: global matching/zip order/coverage, canonical-prefix activation
position transport, unconditional predecessor ALL-name cut, real unsupported
and closing skips with disappearance evidence, whole R198 history folds,
and conditional then discharged o20SynchronizeCanonicalHistoriesModulo.
The actual existing goal declaration is o20CanonicalSynchronizationGoalModulo;
the desired synchronization producer is absent. Original position metadata,
role-word equality and one-edge runtime histories do not fill these gaps.

## Final gate constraints to preserve

No new proof/cap extension occurred after A16. Production src/+dgamma.ipkg
remain byte-identical to34b21c9; whole frozen modules, O19 body, adjacent body,
bridge manifest and four hole statements/bodies unchanged. No lane2
worktree action, no cross-lane locks/windows, one main compiler at a time;
future recorded validations use the then-authorized own RSS guards.

RSS means maximum sampled RSS over command-matching idris2 processes
(single-process compiler; not an aggregate process-tree total; not OS
high-water). Reuse of unchanged seeds is not cold certification or a fresh
PASS for an unvalidated source. Machine verification is not human review.
R204 final evidence and owner/reviewer disposition must be read before R205.
