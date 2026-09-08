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

## R192 binding owner decision — verbatim (2026-09-08)

> OWNER DECISION (2026-09-08, binding, record verbatim in your A8/A10 memo, audit, THM73-PLAN and NOTES): A8 and A10 are resolved by OPTION A — a DEFERRED PRODUCTION UNFREEZE of src/DGamma/CP3.idr limited to the canonical-form definitions: CanonicalInputPlacement (A8: root-first MODULO PROVISION AVAILABILITY, the R178 replacement placement record) and ActorLifecycleOnly (A10: the actor's own generated-child ORetire/ORemove belong to the parent's block). Sequence: (1) research-copies FIRST — prove both cures on research variants (ActorLifecycleOnlyExtended; the R178 placement record), including the zero-gap completeness for the selector and the O17 root phase on those variants, with fixtures (R191 F1–F6 child-retire candidate must fall INSIDE the parent block under the variant; the R174 provision-collision candidate must be admissible under the revised placement); (2) then a single production-unfreeze shift prepares the EXACT CP3 diff (definitions + in-file dependents), the clause map, and a memory-safe seeded rebuild plan (the CP3 change invalidates most downstream TTCs; plan a serialized module-by-module build via the /tmp/dgamma-build-loop.sh pattern under the 48 GiB monitor — the from-scratch Chez peak was ~138 GiB; never run the whole package build in one unmonitored process); (3) the owner signs the production diff before it is committed. Until (3): production stays byte-identical to 34b21c9; the frozen-surface rules are unchanged. Your Unit C memo becomes the plan for (1)–(2): make it precise (names, line numbers, dependents, fixture list, rebuild plan). No production edit this shift.

This ruling supersedes earlier pending/option-comparison language, but does NOT
unfreeze production in R192. Current-shift O17 prohibition remains; variant
root-phase work is planned for the explicitly authorized research sequence.

## Precise deferred production-unfreeze sequence (owner Option A)

### (1) Research proofs FIRST — not complete in R192

- **A10 definitions:** `research/DGamma/CP5ActorLifecycleOnlyExtended.idr:17`
  `ActorLifecycleOnlyExtended` adds `ExtendedChildRetireStep` and
  `ExtendedChildRemoveStep`, each with the actual source lookup, exact
  `ChildOf selected` parent, and exact native action. Its nameEq index must
  be threaded into the eventual production grammar. `actorLifecycleOnlyIntoExtended`
  is ONLY old→extended. `LocatedOpenEpisodeBlockExtended` retains exact physical
  cuts, opening, body, installedness, no other lifecycle, final Active, and
  full trace factorization; none of those is replaced by an order list.
- **A10 compiled probes:** `r192ExistingParentBodyRetireExtended` and
  `r192ExistingParentBodyRemoveExtended` in `R192RemovedBirthCurrentNameProbe`
  classify genuine existing R178/R192 bodies. `r192RetirementHasNoLegacyOrZeroGapCoercion`
  rejects old-grammar and empty-gap coercions. These are not a universal cure.
- **R191 required fixture:** states/trace/block source at
  `R191CanonicalChildRetirementGap.idr:32,80,108,125,152,185ff` retain actual
  F1–F6 capital. Its retirement at8 cannot belong to contiguous parent[3,6)
  merely by extending syntax: actor1's lifecycle at6/7 intervenes. FIRST derive
  an actual relocation across those two foreign edges (same action word except
  that permutation, same endpoint), THEN build the extended parent block and
  adjacent block/gap certificates. R192 C4 exhausted3/3 native guard
  normalization attempts and was reverted; `R192ExtendedChildBlockProbe`
  contains only named candidate states, NOT its eleven-edge trace.
- **A8 research definitions:** `CP5AvailabilityAwarePlacement.idr:17`
  `rootDeclaredProvisionsFree`, :27 `rootInputAtSource`, :50 `AvailabilityTrace`,
  :68 `rootCutCompatible`, :86 `EarliestAvailableRootBirth`, :104
  `AvailabilityAwareCanonicalInputPlacement`. The original trace is an extra
  explicit record index; `placementExternalInputsSame` preserves root-input
  order. Availability holds at EVERY crossed state, including the final cut,
  and no root input is crossed. Retirement/inactivity does NOT release keys.
- **R174 required fixture:** `R174O17ProvisionCollisionCandidate.idr:91,103,111,129`
  owns observed actions, annotation, actual prefix/suffix and scalar compatible
  interval shape `[False,False,False,False,False,True]`. Root2 at5 is permitted
  only after Remove1 at4, not at an earlier pointwise-free snapshot. Complete
  the still-uninhabited `EarliestAvailableRootBirth`, all located-root cases and
  full `AvailabilityAwareCanonicalInputPlacement`, including own-lifecycle
  order. R178 C9's parked2/3 cost history is NOT erased or retried in R192.
- **Required future proof gates:** research-copy canonical schedule/order and
  block decomposition; exact relocation provenance; preservation of revised
  placement under actual O19 steps; right dependency-domain transport; real
  candidate/enumeration orientation completeness; **selector zero-gap
  completeness**, and **O17 root phase on the availability-aware variant**.
  No O17 work was performed in R192. Its old frozen body is not a target for
  an implicit compatibility coercion.

### (2) Prepare one exact CP3 patch and dependent/rebuild plan — later shift

Frozen locations (before any owner-signed patch):

| CP3 location | Planned canonical-definition change | Immediate in-file dependents |
| --- | --- | --- |
| :1786–1804 `ActorLifecycleOnly` | research-validated own-child Retire/Remove constructors and source-parent/nameEq indexing | :1824–1846 `LocatedOpenEpisodeBlock.blockActorOnly`; :1873 `BlockBefore` through the block type; :3241 `CanonicalSchedule.canonicalBlock` |
| :3156–3198 `CanonicalInputPlacement` | replace strict `allRootInputsFirst` and all-lifecycle root order by the R178 availability interval/earliest/own-lifecycle clauses; retain actual freshness and child-generation-before-own-lifecycle | :3265 `CanonicalSchedule.inputPlacement`, threaded original trace required by replacement record |
| :3756 `ConfluenceResult`, :3785 `confluenceTheorem` | dependent references must still typecheck; NO strengthening of final-state equivalence or historical/current-name identification | their canonical schedule fields only; preserve production theorem conclusion fidelity |

No edit to evaluator `applyAction`, O-Insert provision guard, generation-scanner
semantics, vestigial package or effect/control equivalence is included in this
owner decision. A11 is separate and research-only.

**Out-of-file direct consumers:** `src/DGamma/CP3StatementChecks.idr:3398–3445`
(full canonical constructor), :3548–3549 (actor-body constructor), :3586
(placement projection), plus the remaining schedule statement checks to:3738.
Direct research grammar/placement matches are in `CP5ConfluenceCanonicalSortSpike`
(:109/:111, :159, :1294, :2027/:2046, :4185/:4222/:4257–4265),
`CP5O19OriginalBlockClassSpike`, `CP5O19ReachedBlocksSpike`,
`CP5O20InversionChildSafetySpike`, and R192 `CP5O20RightOpeningTransportSpike`.
The last two structural inductions currently cover ONLY the old two
constructors; new child Retire/Remove cases require actual ownership frames,
not an omitted coverage case. All transitive callers must then be rechecked.

`O6-R192-CP3-REBUILD-INVENTORY.json` is the read-only, hashed source/import
inventory and topological affected-module list for the current tree. It is a
PLAN, not compiler evidence and not a promise every legacy negative compiles.
Regenerate/freeze it against the exact owner-approved diff before execution.

**Memory-safe seeded rebuild protocol:**
1. Owner signs the exact CP3 + in-file-dependent diff before any production
   commit. Preserve all existing TTC/build files and record compiler version,
   package/source hashes, cache inventory and no-orphan check.
2. Adapt the progress/resume idea of `/tmp/dgamma-build-loop.sh`, NOT its old
   unmonitored whole-package command. The existing helper is READ ONLY in R192.
   Generate one topologically ordered explicit source-check invocation per
   affected production module; each detached process gets a process-group
   monitor, sampled RSS, **48 GiB hard stop**, timestamp, exit/log/source SHA
   and own Building-line evidence. Serialize; never overlap Idris processes.
3. Compile CP3 first with unchanged prerequisites seeded. Then compile each
   affected production module once in dependency order, reusing newly written
   TTCs. A stopped/failed process is not a PASS; audit native source/TTC status
   and gate before retry. No blanket TTC deletion, no fallback unsafe axioms,
   no restart count treated as proof. If no progress or a single module still
   approaches48 GiB, stop the series and redesign the memory plan.
4. Only after all affected production module checks PASS, run a MONITORED
   seeded package validation under the same guard; NEVER one from-scratch
   unmonitored package process (historical Chez peak ~138 GiB). Then check
   direct research consumers in dependency order and their transitive closure.
   Negative fixtures need frozen symbol+diagnostic contracts, not exit-only
   acceptance. Do not run broad legacy R11.
5. Owner/reviewer inspect exact source diff, clause map, fixture matrix,
   immutable logs, RSS peaks, cache census and receipts before the single
   production-unfreeze commit. Until that signature, CP3 bytes stay frozen.

## A11 exact gate and coverage split (approved after Unit B stop)

Supervisor approved ONLY the existing fourth field gaining:

```idris
(isSupported {name = name} {key = key} {value = value} {world = world}
  {error = error} @{nameEq} @{keyEq} child leftFinal = True) ->
```

`leftFinal` is already bound in the record header. No binder added, first
three fields/constructor unchanged. Supported children: exact current raw-name
match with original generation/origin triangle. Unsupported historical:
generation-only E8 / `o20CanonicalOriginMatchOrClosing`. PRESENT unmatched
original remainder: full CP3 vestigial package in the unchanged O21 statement.
Removed names: actual absence. This revision does not prove the O21 hole.

The exact manifest records field **1154→1297 bytes**, SHA
`574fcb56e55e2bc3f54d36711b23ef6ac767f9c97952c596ce5c72dd6e7123d1` →
`037737c2cd0d9c29ae7d1637a7eaf19f9ea75bbc07a1546f8870b312b3af2894`;
record **3100→3243 bytes**, SHA
`b65cc059e8dea35ce9e7fdd1b580b1d2b5e0e3e03b4ed6aaddf07c6f101cf6d1` →
`ac5304c1a6a6e0cea988eac4b0dcdb5756fcf1b67ede7d0db6a4d723c73b695d`.
O21 declaration SHA remains
`377b08ff82e1e4212738bb00a45a088b1f0d8fd8bc8b54bf061c96f2f4891681`.
Two constructor fixtures (not endpoint theorem consumers) need only the same
supported binder plumbing: R8 authenticated-direction positive and R8
wrong-birth negative. Baseline old wrong-birth rejection is fresh/diagnostic-
authenticated. New matrix/recheck results will be recorded before final freeze.

### A11 realized boundary (D cap6; no further proof units this shift)

The exact two-line field change is committed `ebaa750e`. Constructor consumers
are revised `6526bc5d`/`4e3273dd`, both exact manifest checks pass including the
old wrong-generation negative's authenticated rejection. New helper
`CP5O20SupportedBridgeAssemblySpike.o20SupportedBridgeFromOwnedCut` assembles the
EXACT revised record from an owned all-name cut and the already accepted
supported-birth capital. Therefore the revised **fourth** clause now has a
native producer; actual arbitrary canonical execution→cut extraction remains
open. O21 statement/body stays byte-identical and its hole stays a hole.

R192 removed historical countershape: old clause logically refuted; new scoped
instance passes vacuously for the unsupported child. R178 real Active child:
`r192SupportedBirthScopePositive` proves support and a real birth/generation
triangle, no caller support premise. `r192UnsupportedIsNotVestigialWithoutDiscard`
rejects the missing-discarded-generation shortcut for a PRESENT remainder.
Full independent canonical/replay countershape capital, full one-/two-sided
present CP3 vestigial instances and a concrete active-fake negative remain OPEN
fixtures. This is not hidden behind the E8/Current/E9 success or R4's conditional
assembly test. See the audit's six-row exact fixture matrix and final ledger.
