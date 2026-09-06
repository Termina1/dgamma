# O6 R172 — reconnaissance and O14 probe-first grind audit

## Coordinate, authorization and immutable boundary

Required start `0e58c54`, branch `cp5-thm73-scoping`, verified **2026-09-06
11:49:38 UTC**; only allowed untracked `paper/` and byte-frozen adversarial
review. Idris 0.8.0; `%default total`; one compiler at a time, process inspection
before checks. No build tree/TTC seed deletion, production edit, from-scratch
build, subagent, forbidden body or new `with`. No-new-attempt time **15:09:38**,
safe-gate deadline **15:34:38**, timeout **15:49:38 UTC**.

Unit A is committed at **b5d6904**, with all seven full hole statements, exact
last-stop quotes, capital-to-premise routes, ranking and the current debt
register in `O6-R172-NEXT-PHASE-RECON.md` and `THM73-PLAN.md`. Its eight
sequential invocations freshly elaborate each spike once (three other calls
were explicitly cached); all pass, seeded package retains 207/207 modules.
Details and complete frozen SHA values are in that memo.

The supervisor **ACCEPTED b5d6904** and approved O14 probe-first exactly:

> one disposable fully explicit top-level lookupFiber-found ->
> supportedActiveAt = isActive (fiberLifecycle fiber) equation bridge via public
> activePredicateAtFoundQ, ≤3 checks, probe removed (source + TTC/TTM) and
> transcript committed to the R172 audit BEFORE any retained O14 helper.

On PASS, the ruling pre-authorizes an erased producer-owned lookup/rank view
and a simultaneously constructed stable-rank-sort invariant, one declaration
per invocation and immediate checked commit; O14 body only after its invariant
capital is committed. O17 probe-first is only after O14 closes/stops. No surface
revision, O19 body, O21 withdrawal or debt-register implementation this shift.
**No gate-timeout exception was used**: the reply arrived normally.

## P1 — disposable active lookup equation: PASS 2/3

The first probe was genuinely compiled before a retained helper. Command:

```sh
idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R172SupportedActiveLookupEquationProbe.idr
```

Exactly one new declaration. Full final disposable source (not retained as an
Idris module):

```idris
module DGamma.R172SupportedActiveLookupEquationProbe

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import Decidable.Equality

%default total

0 r172SupportedActiveLookupEquationProbe :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} selected (registry state) = Just fiber) ->
  (supportedActiveAt {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} selected state =
    isActive (fiberLifecycle fiber))
r172SupportedActiveLookupEquationProbe name key world error value nameEq state selected fiber found =
  activePredicateAtFoundQ {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq state selected fiber found
```

### P1-1 — charged infrastructure failure

**12:07:42–12:07:47 UTC**. The first source omitted only the direct
`DGamma.Coeffects` import. Full diagnostics:

```text
1/1: Building DGamma.R172SupportedActiveLookupEquationProbe (research-tests/DGamma/R172SupportedActiveLookupEquationProbe.idr)
Error: While processing type of r172SupportedActiveLookupEquationProbe. Undefined name DGamma.Coeffects.CoeffectSpec.dependencies.

Error: While processing right hand side of r172SupportedActiveLookupEquationProbe. DGamma.CP4SupportQuiescence.activePredicateAtFoundQ is not accessible in this context.

DGamma.R172SupportedActiveLookupEquationProbe:21:3--21:26
 17 |   (supportedActiveAt {name = name} {key = key} {value = value}
 18 |     {world = world} {error = error} @{nameEq} selected state =
 19 |     isActive (fiberLifecycle fiber))
 20 | r172SupportedActiveLookupEquationProbe name key world error value nameEq state selected fiber found =
 21 |   activePredicateAtFoundQ {name = name} {key = key} {value = value}
        ^^^^^^^^^^^^^^^^^^^^^^^

```

The compiler process returned **0 despite the Error diagnostics**. This is
counted as failure **1/3**, not a successful check. The check wrapper is now
explicitly diagnostic-aware in addition to testing exit status. The
`activePredicateAtFoundQ` accessibility diagnostic was secondary to the missing
dependent definition; no visibility edit or production change was made.

### P1-2 — pass

**12:08:14–12:08:19 UTC**, exit 0, no Error diagnostic:

```text
1/1: Building DGamma.R172SupportedActiveLookupEquationProbe (research-tests/DGamma/R172SupportedActiveLookupEquationProbe.idr)
```

Adding the direct Coeffects import makes the **same** fully explicit equation
check through the public theorem. It tests the actual `supportedActiveAt`, not
a manually mirrored case expression or an assumed equality. This discharges
the designated R135 observation spelling probe, not the rank-sort invariant or
O14 body.

The disposable `.idr` and its exact `.ttc/.ttm` outputs were removed; no seed or
other artifact was deleted. Source and logs are reproduced above; `/tmp` copies
are optional telemetry only. No retained research helper has been added yet.
O14 body remains **0/3**, original seven-hole census unchanged. This audit
commit precedes any retained helper, as ruled.

## Unit B — approved O14 target CLOSED

**Body commit `c99145c`, first body attempt 1/3.** No statement weakening,
new premise, name movement, surface revision, visibility change or other
research-module content change. The exact body uses only the existing bundle's
`replayProtocolRanked` and `replayParentRanksIncrease` fields. It does not use a
raw-name exclusion or the frozen deletion theorem.

### Construction and quantities

1. **M1–M6:** the passed actual active-lookup equation is retained, alongside
   `CanonicalActiveRank` and a quantity-0 producer that selects the actual lookup
   and extracts its authentic protocol rank. The absent branch is refuted using
   the actual predicate equation and `SupportMatchesActive`, not an uncorrelated
   Bool case tree. This completes the approved R135 observation/rank probe route.
2. **M7–M9:** `canonicalProtocolRank` is executable and total, defaulting to zero
   only for absent/unranked observations. `canonicalProtocolRankExact` equates it
   to an authentic `NameProtocolRank`; `canonicalRankedSupportPathStrict` uses the
   two exact path witnesses. Thus defaults cannot forge a strict support-path
   inequality. The final O14 assembly uses this smaller direct path-rank route;
   **M1–M6's active-rank view is retained capital, not falsely claimed as a
   dependency of the final body**. No active/installed view is reconstructed
   inside the sort.
3. **M10–M29:** `CanonicalRanksOrdered` and `CanonicalRankSortResult` carry every
   head's rank bound over its suffix, uniqueness, and both membership directions
   for the exact runtime output. Fresh insertion, duplicate removal and outer
   sorting each construct list plus invariant together in structural recursion.
   There is **no independent `sort` followed by a theorem about its output**.
   The output lists/rank function/comparisons are executable; proof fields and
   insertion invariant arguments have quantity **0**. No `with`, inferred local
   dependent record, local `let`, as-pattern or unsafe termination claim.
4. **M30–M33:** strict ranks imply actual `BeforeIn` by induction on the output
   list. A wrongly placed upper head contradicts its suffix bound; identical
   endpoints contradict strict rank. This is not merely set membership.
5. **M34–M41:** explicit `decEq` observations reflect the actual `listMember`
   predicate in both directions. `canonicalSupportOrderingFromSort` constructs
   all four `LinearizesSupport` fields: unique, sound, complete, paths ordered.
   It needs only global protocol/parent ranks and the actual sorted support set.
6. The unchanged O14 signature is filled only after the entire invariant and
   assembler are committed (`a87f109` and `8f5b5c2`). O14 **does not** prove the
   shared original/reduced order or any operational sorting/origin accounting.
   The R143 correction and all non-hole debts remain in force.

The list algorithm inserts an earlier input before equal-ranked distinct suffix
names. M42 checks that behavior on a concrete tie example, plus nonmonotone
ranks and duplicate elimination; no separate universally quantified tie-stability
theorem is claimed, nor is one required by `LinearizesSupport`.

### Per-micro-unit fresh checks and immediate commits

Every row adds exactly **one** declaration except the marked O14 existing-body
fill (zero new declarations). All target checks freshly report
`3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike`; each successful row is
committed before the next source change. Exactly 42 new declarations and 43
source commits. M1–M41 each **1/3**; O14 body **1/3**; M42 **2/3**.

| Micro-unit | Retained declaration / body | Successful fresh check UTC window | Commit |
|---|---|---|---|
| M1 | `canonicalSupportedActiveAtFound` | 12:11:41–12:11:46 | `c787fb8` |
| M2 | `CanonicalActiveRank` | 12:12:29–12:12:34 | `1125df2` |
| M3 | `canonicalSupportedActiveAtMissing` | 12:12:51–12:12:56 | `b6e42bd` |
| M4 | `canonicalActiveRankAtFound` | 12:13:17–12:13:22 | `9620ddd` |
| M5 | `canonicalSupportedRankObserved` | 12:13:49–12:13:54 | `9c27b25` |
| M6 | `canonicalSupportedRank` | 12:14:45–12:14:55 | `a0ffdf9` |
| M7 | `canonicalProtocolRank` | 12:14:56–12:15:06 | `6d2ad1c` |
| M8 | `canonicalProtocolRankExact` | 12:15:06–12:15:11 | `9cd2a78` |
| M9 | `canonicalRankedSupportPathStrict` | 12:20:13–12:20:18 | `22004fc` |
| M10 | `CanonicalRanksOrdered` | 12:20:18–12:20:28 | `73940ee` |
| M11 | `CanonicalRankSortResult` | 12:20:28–12:20:38 | `45c8c36` |
| M12 | `canonicalRanksTail` | 12:22:43–12:22:53 | `3238307` |
| M13 | `canonicalRanksHeadBelow` | 12:22:53–12:22:59 | `545ba54` |
| M14 | `canonicalUniqueTail` | 12:22:59–12:23:04 | `f7fef05` |
| M15 | `canonicalUniqueHeadAbsent` | 12:23:04–12:23:14 | `637b921` |
| M16 | `canonicalRanksLowerThroughHead` | 12:23:14–12:23:24 | `de7d8d7` |
| M17 | `canonicalRankExistingForward` | 12:23:24–12:23:34 | `476fce8` |
| M18 | `canonicalRankPushOldTail` | 12:23:35–12:23:45 | `0c6fb4e` |
| M19 | `canonicalRankSwapFront` | 12:23:45–12:23:55 | `1a812c7` |
| M20 | `canonicalRankConsMembership` | 12:24:45–12:24:55 | `427ffb6` |
| M21 | `canonicalRankInsertedHeadAbsent` | 12:24:55–12:25:05 | `399988a` |
| M22 | `canonicalRankHeadBelowInserted` | 12:25:05–12:25:15 | `5f73212` |
| M23 | `canonicalFreshRankInsertAt` | 12:25:15–12:25:26 | `2caca0f` |
| M24 | `canonicalFreshRankInsert` | 12:26:11–12:26:21 | `6640c7c` |
| M25 | `canonicalRankInsertSeen` | 12:26:21–12:26:31 | `e8da7e5` |
| M26 | `canonicalRankInsert` | 12:26:32–12:26:42 | `e2168ed` |
| M27 | `canonicalRankSortCompose` | 12:26:42–12:26:52 | `0fb71da` |
| M28 | `canonicalRankSortStep` | 12:26:52–12:27:02 | `cf9d795` |
| M29 | `canonicalStableRankSort` | 12:27:02–12:27:12 | `a87f109` |
| M30 | `canonicalRankBeforeFromHead` | 12:27:48–12:27:58 | `9a95817` |
| M31 | `canonicalRankBeforeUpperSplit` | 12:27:58–12:28:08 | `6723791` |
| M32 | `canonicalRankBeforeLowerSplit` | 12:28:08–12:28:18 | `bb6ff0c` |
| M33 | `canonicalRankOrderBefore` | 12:28:19–12:28:29 | `20debca` |
| M34 | `canonicalListMemberKnownYes` | 12:30:10–12:30:21 | `c5e3bf0` |
| M35 | `canonicalListMemberKnownNo` | 12:30:21–12:30:31 | `d96318d` |
| M36 | `canonicalListMemberCompleteStep` | 12:30:31–12:30:41 | `d1e9bb3` |
| M37 | `canonicalListMemberComplete` | 12:30:41–12:30:51 | `984bf68` |
| M38 | `canonicalListMemberSoundNo` | 12:30:51–12:31:01 | `e99442a` |
| M39 | `canonicalListMemberSoundStep` | 12:31:02–12:31:12 | `29f4556` |
| M40 | `canonicalListMemberSound` | 12:31:12–12:31:22 | `cdfe03c` |
| M41 | `canonicalSupportOrderingFromSort` | 12:31:59–12:32:09 | `8f5b5c2` |
| O14-body | `supportOrderingSpike — existing body` | 12:32:38–12:32:48 | `c99145c` |
| M42 | `canonicalRankSortConcreteChecks` | 12:35:17–12:35:27 | `9a70ffd` |

M6–M8's shell commit-subject formatter emitted a shell syntax diagnostic after
each successful check and produced ugly subjects. Their compiler logs are clean,
each source increment was committed immediately and contains one declaration.
No history rewrite was performed. The table gives their intended identities;
this is administrative, not an unreported Idris attempt or source failure.

### M42 concrete fixture — one corrected spelling failure

M42-1 (**12:34:44–12:34:49 UTC**, exit 1) was charged **1/3**. Unqualified `id`
in a type was implicitly bound as a fresh arbitrary rank function; the compiler
correctly would not reduce an arbitrary rank-sort to the numeric order. Exact
diagnostic transcript (trailing whitespace normalized):

```text
3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Warning: We are about to implicitly bind the following lowercase names.
You may be unintentionally shadowing the associated global definitions:
  id is shadowing Prelude.Basics.id

DGamma.CP5ConfluenceCanonicalSortSpike:1209:3--1211:97
 1209 | 0 canonicalRankSortConcreteChecks :
 1210 |   (rankSortedItems (canonicalStableRankSort Nat %search id [3, 1, 2, 1, 0]) = [0, 1, 2, 3],
 1211 |    rankSortedItems (canonicalStableRankSort Nat %search (\selected => 0) [3, 1, 2]) = [3, 1, 2])

Error: While processing right hand side of canonicalRankSortConcreteChecks. Can't solve constraint between: [0, 1, 2, 3] and (canonicalRankInsert Nat DecEq implementation at Decidable.Equality:40:1--45:32 id 3 (rankSortedItems (canonicalStableRankSort Nat DecEq implementation at Decidable.Equality:40:1--45:32 id [1, 2, 1, 0])) (rankSortedOrdered (canonicalStableRankSort Nat DecEq implementation at Decidable.Equality:40:1--45:32 id [1, 2, 1, 0])) (rankSortedUnique (canonicalStableRankSort Nat DecEq implementation at Decidable.Equality:40:1--45:32 id [1, 2, 1, 0]))) .rankSortedItems.

DGamma.CP5ConfluenceCanonicalSortSpike:1212:36--1212:40
 1208 | ||| Concrete reduction checks: nonmonotone ranks with a duplicate, and stable equal-rank names.
 1209 | 0 canonicalRankSortConcreteChecks :
 1210 |   (rankSortedItems (canonicalStableRankSort Nat %search id [3, 1, 2, 1, 0]) = [0, 1, 2, 3],
 1211 |    rankSortedItems (canonicalStableRankSort Nat %search (\selected => 0) [3, 1, 2]) = [3, 1, 2])
 1212 | canonicalRankSortConcreteChecks = (Refl, Refl)
                                           ^^^^

```

M42-2 (**12:35:17–12:35:27**, exit 0, no diagnostic) replaced only that `id` by
an explicit identity lambda. The committed declaration at `9a70ffd` is:

```idris
0 canonicalRankSortConcreteChecks :
  (rankSortedItems (canonicalStableRankSort Nat %search (\selected => selected) [3, 1, 2, 1, 0]) = [0, 1, 2, 3],
   rankSortedItems (canonicalStableRankSort Nat %search (\selected => 0) [3, 1, 2]) = [3, 1, 2])
canonicalRankSortConcreteChecks = (Refl, Refl)
```

These are actual reductions of the implemented algorithm, not supplied-capital
proof repackagers. They do not substitute for the parked concrete end-to-end
R129/O16/repeated-Iter fixtures.

## Final validation and census

Proof coordinate **`9a70ffd`**. Source checks use the same verified direct seeded
CLI recorded in Unit A. The final serial boundary checks are:

| Check | Outcome | UTC window / evidence |
|---|---|---|
| CanonicalSort | PASS, fresh M42-2 | 12:35:17–12:35:27, `3/3: Building` |
| RenamingComposition + CrossTrace | PASS, fresh dependent rebuild | 12:36:42–12:36:58, `4/5: Building` then `5/5: Building` |
| RenamingComposition direct | PASS, cached | 12:36:58–12:37:03; fresh evidence is the prior dependent rebuild |
| DeletionChain direct | PASS, cached | 12:37:03–12:37:08; Unit A's fresh 85.6-second check remains valid, source unchanged |
| LocalDiamond direct | PASS, cached | 12:37:08–12:37:13; Unit A's fresh 503.9-second check remains valid, source unchanged |
| `idris2 --build dgamma.ipkg` | PASS, seeded **207/207** | 12:37:13–12:37:33; not a from-scratch or research-suite build |

**59 sequential compiler invocations:** 8 Unit A/baseline + 2 disposable P1 +
44 retained-source attempts + 5 final boundary checks. **57 diagnostic-clean
passes, 2 charged corrected failures** (P1-1 missing Coeffects import, M42-1
accidental `id` implicit). P1-1 misleadingly returned process code zero and is
still counted as failure. No timeout, overlap, orphan, OOM, seed deletion or
third/fourth attempt. Peak sampled memory across the session was Unit A's fresh
LocalDiamond at **50365840 KiB (~48.0 GiB)**, not a measured OS exact peak.
No new proof attempt began after **12:35:17 UTC**, well before 15:09:38.

Six exact remaining holes (**1/4/0/0/1**, delta **-1**):

| File part | Hole | Final line |
|---|---|---:|
| CanonicalSort | `sortClosingFreeTraceSpike_rhs` | 1319 |
| CrossTrace | `operationalAdjacentBlockSwapSpike_rhs` | 714 |
| CrossTrace | `canonicalSupportOrdersMatchSpike_rhs` | 986 |
| CrossTrace | `selectOperationalCanonicalPermutationSpike_rhs` | 1067 |
| CrossTrace | `canonicalSchedulesConvergeSpike_rhs` | 1325 |
| RenamingComposition | `replayedCanonicalToOriginalEndpointSpike_rhs` | 2723 |

The Unit A memo's seven-hole types/coordinates are deliberately retained as its
ratified **start-coordinate** snapshot, not silently rewritten. The live plan
and README/NOTES status now report O14 closed and six holes. No non-hole debt was
implemented or discharged: exact canonical accounting, shared original/reduced
order, R16 drift, frozen CP3 raw-premise defect, R129 integration, copied `with`
cleanup and concrete authentic integrations remain recorded.

### Asserting frozen/self-validation

`python3 -I /tmp/dgamma-r172-validate.py` succeeds and checks:

- full adjacent definition **1470 bytes**, SHA-256
  `2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf`;
- signature prefix **1154 bytes**, SHA-256
  `3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf`;
- CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0`;
- production `src/` and package diff versus `34b21c9`: **EMPTY**;
- **LocalDiamond, DeletionChain, CrossTrace and RenamingComposition entire source
  bytes** versus `0e58c54`: unchanged; no exports or consumers to list;
- removing exactly the new private O14 capital block and restoring only the
  O14 RHS reproduces the original CanonicalSort file byte-for-byte. Its original
  O14 statement, all other statements/bodies and all original visibility remain
  unchanged. No new public/private visibility revision is concealed in helpers;
- DeletionChain `with` count **9 → 9**, zero `with`/`let`/hole/frozen-call or
  unsafe additions anywhere in the source diff, `%default total` retained;
- each of 43 source commits adds at most one declaration (42 total), with its
  own successful fresh Building marker, recorded in the table; all 59 compiler
  time windows are pairwise sequential;
- exact six-hole names/coordinates, 207/207 seed artifacts, whitespace-clean
  shift diff, clean staging and only the two permitted untracked paths;
- review still untracked, never staged/modified/deleted, SHA-256
  `61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8`.

No wider R11 runner, R16 aggregate assembly, runtime suite or clean rebuild was
run or claimed. These are reproducible **self-checks**, not independent review.

## Status

**Fully proved this shift:** approved O14 finite support-ordering producer,
unchanged `supportOrderingSpike` at `c99145c`; exact observation/rank capital,
total simultaneous rank sorting/deduplication with all required invariants,
strict-rank occurrence ordering, and concrete reduction regressions.

**Partial overall:** Theorem-73 campaign. The already closed DeletionChain and
newly closed O14 do not provide O17, CrossTrace coherence or final vestigial
composition.

**Merely stated:** six remaining holes, delta **-1**, with no new hole or escape
hatch. Non-hole debts remain explicit. Theorem 73 is **not claimed proved**.

**Next:** final supervisor/reviewer acceptance gate for this completed approved
first target. O17 is next **probe-first** in the ratified ranking; it was not
started in Unit B. O19 body remains banned, O21 withdrawal branches parked, no
surface revision. The shift stops after its approved first target rather than
silently expanding into a new operational proof campaign.
