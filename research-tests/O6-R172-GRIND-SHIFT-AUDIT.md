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

## Continuation ruling after the ratified O14 milestone

The supervisor independently verified and **RATIFIED O14 closure at `b590789`**
(clean tree, production diff empty, independent six-hole census, removed probe;
comment-only `with` text was not mistaken for new syntax), and pushed that HEAD.
The initial final-gate request above is therefore a **ratified O14 milestone**,
not the end of the shift. The ruling redirects R172 to **O17 PROBE-FIRST now**,
with ≤3 checks per micro-unit, no retained capital before a committed disposable
probe transcript, no O17 body before committed invariant, no surface/O19/O21
work, and a new gate on O17 closure/stop. If ≥90 minutes remain then, target #3
requires another authorization; it must not be self-started. The time guard is
unchanged. The entire ratified O14 audit above is preserved verbatim.

The exact R144 `O6-R144-O17-SORT-BASE-BUDGET-STOP-AUDIT.md` was reread. Its wall
is the missing operational hoist and simultaneous current trace/bundle,
nonzero derivation, external relation, ranges and occurrence provenance—not a
failed proof that an already supplied contiguous block is contiguous. The
identity-as-complete-sort route stays closed.

## P2 — actual one-splice recursive-state probe: PASS 1/3

This deliberately isolates the **operational package boundary** before an O17
recursion: execute the frozen `adjacentSwapSuffixSpike` at the actual source
bundle and local pair, then construct a **nonempty** one-node derivation, exact
returned TARGET bundle, external relation, operational occurrence map, endpoint
relation, and a freshly produced O14 support order at **that same returned
endpoint**. No caller supplies a moved trace, independent order, contiguous
block or equality between independently computed endpoints. The only lambda is
fully typed by its exact `AdjacentSwapResult` telescope, not an inferred local
dependent view; no `let`/`with`, new helper or export.

The probe still takes the local diamond/orientation/pair-external witness as
input. **It does not prove crossing selection or early applicability**, fixed
original-order transport, moved block ranges, closing-freedom transport or an
O17 body. Those must be produced in the retained phase; this is not an honest
basis for claiming that a generic O19 crossing is available. The upstream
DeletionChain result feeds its `reducedPremises` into precisely this source
bundle type; the new O14 body now supplies the reached-state order rather than
assuming a second sorting result.

Exactly one disposable declaration:

```idris
module DGamma.R172O17SingleSwapStateProbe

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| A real one-node operational splice, never identity-as-a-complete-block.
||| Local crossing applicability remains explicit input to this narrowly scoped probe.
0 r172O17SingleSwapStateProbe :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  (initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error) ->
  (original : Transitions initial originalFinal) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) -> (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  (appendTransitions prefixTrace (MoreTransitions left (MoreTransitions right suffix)) = original) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  AdjacentSwapOrientationEvidence left right ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond) (MoreTransitions (movedLeft diamond) NoTransitions)) ->
  (targetFinal : SystemState name key value world error **
    target : Transitions initial targetFinal **
    (NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original target,
     ReplayInvariantBundle name key world error value protocol nameEq keyEq target,
     SameExternalOrchestration nameEq original target,
     ActionRegistrationReplayCorrespondence name key world error value original target,
     RelationalReplayEndpoint name key world error value nameEq keyEq originalFinal targetFinal,
     SupportOrderingCapital name key world error value nameEq keyEq targetFinal))
r172O17SingleSwapStateProbe name key world error value nameEq keyEq protocol
  initial pairFirst pairMiddle pairFinal originalFinal original prefixTrace left right suffix
  decomposition premises orientation diamond pairExternal =
    (the ((result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original prefixTrace left right suffix diamond) ->
      (targetFinal : SystemState name key value world error **
    target : Transitions initial targetFinal **
    (NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original target,
     ReplayInvariantBundle name key world error value protocol nameEq keyEq target,
     SameExternalOrchestration nameEq original target,
     ActionRegistrationReplayCorrespondence name key world error value original target,
     RelationalReplayEndpoint name key world error value nameEq keyEq originalFinal targetFinal,
     SupportOrderingCapital name key world error value nameEq keyEq targetFinal)))
      (\result => (replayedFinal result ** swappedTrace result **
        (NonEmptyAdjacentSwap original prefixTrace left right suffix orientation diamond result
          (swappedTrace result) FiniteAdjacentSwapDone,
         swappedPremises result,
         swappedSameExternalInputs result,
         swappedOccurrenceCorrespondence result,
         swappedEndpoint result,
         supportOrderingSpike nameEq keyEq protocol (swappedTrace result) (swappedPremises result)))))
      (adjacentSwapSuffixSpike nameEq keyEq protocol original prefixTrace left right suffix
        decomposition premises diamond pairExternal)
```

Command and complete result:

```sh
idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R172O17SingleSwapStateProbe.idr
```

**12:47:45–12:47:50 UTC**, exit 0, no Error diagnostic:

```text
1/1: Building DGamma.R172O17SingleSwapStateProbe (research-tests/DGamma/R172O17SingleSwapStateProbe.idr)
```

The exact `.idr/.ttc/.ttm` files were removed, without deleting any seeded
artifact. This transcript is committed **before any retained O17 declaration**.
O17 body budget in this continuation is still **0/3**; the six-hole census and
all frozen bytes remain unchanged. This successful state-index probe permits
only the scoped producer-owned capital campaign; it is not a block-hoist proof.


## O17 continuation — retained capital and full-input local obstruction

This section **supersedes the O14-only stopping/next-target status above**;
the entire O14 audit ratified at `b590789` is preserved byte-for-byte. The
supervisor ratified and pushed that milestone, explicitly ruled “DO NOT STAND
DOWN”, and authorized O17 probe-first in the same shift. P2 and its removed
source/TTC/TTM transcript were committed at `259eb71` before N1.

At proof checkpoint **a069cbc** (whitespace-only validation correction
**775bd22**), O17 is **OPEN / paused for a semantic-frontier gate**, body
**0/3**. No micro-unit exhausted its three-attempt budget; this is not a claimed
compiler-budget exhaustion. O14 remains closed; six named holes remain,
**1/4/0/0/1**, net shift delta **-1**. No other original research declaration,
production source or package surface was changed.

### N1–N42: actual reached-state capital, not an assumed sorted output

* N1–N8 simultaneously carry the exact current trace/final, finite operational
  derivation, complete current bundle, external correspondence and endpoint;
  the source-to-current operational occurrence/replay folds come from that
  same derivation. A genuinely applied `adjacentSwapSuffixSpike` extends it.
* N9–N20 derive the distinct-root insertion crossing from the actual source
  bundle, decomposition, paper activation branch and actor/root inequality.
  Alignment, source well-formedness, pair independence, early applicability,
  child-parent exclusion, local diamond and pair-external relation are produced,
  not new premises supplied to O17. The owner-produced hoist contains the exact
  returned `AdjacentSwapResult` and moved root action.
* N21–N28 locate exact original/moved root occurrences, prove the moved ordinal
  decreases by one, build a nonempty derivation, and extend the reached state.
* N29–N42 preserve active/component/parent observations, support truth and every
  parent/precedence path under **full no-withdrawal ControlEquivalent**. O14's
  authentic active/rank witness feeds this argument. N42 preserves the **same
  fixed desired list**, using the two endpoints' authenticated rank/support
  facts; it does not recompute an unrelated order. This is **not** the R143-
  refuted arbitrary original/reduced deletion-order transfer.

N42 is committed at `1e8105e`. Remaining operational work is real: a decreasing
full worklist/selector, all root orchestration and activation cases, stable
child-yield placement, contiguous block ranges/order/disjointness, coverage,
closing-freedom transport and exact registration accounting. A one-position
root-insert decrease is not a termination theorem for this full selector.

#### Retained N micro-unit ledger

Each row is one new top-level declaration, followed immediately by its clean
fresh compiler check and commit. No new export/visibility declaration was added
to the research module. Direct imports added there are `DGamma.CP3Support`,
`DGamma.CP4TerminalRecovery`, and `DGamma.CP4RecoveryModelTrace`.

| Unit | Declaration | Check | Commit |
|---|---|---|---|
| N1 | `CanonicalSortingReplayState` | PASS 1/3 | `05be2ba` |
| N2 | `canonicalSortingCurrentOrdering` | PASS 1/3 | `2db89f0` |
| N3 | `canonicalSortingReplayCorrespondence` | PASS 1/3 | `f7c6177` |
| N4 | `canonicalSortingOccurrenceCorrespondence` | PASS 1/3 | `f421607` |
| N5 | `canonicalSortingReplayStart` | PASS 1/3 | `ebbacbc` |
| N6 | `canonicalSortingDerivationAppend` | PASS 1/3 | `db96bad` |
| N7 | `canonicalSortingReplayExtend` | PASS 1/3 | `7138bf7` |
| N8 | `canonicalSortingReplaySwap` | PASS 1/3 | `0e19aa6` |
| N9 | `canonicalPaperActivationLifecycle` | PASS 1/3 | `1bae176` |
| N10 | `canonicalRootChildInsertImpossible` | PASS 2/3 | `578fbb6` |
| N11 | `canonicalLifecycleInternal` | PASS 1/3 | `02efd60` |
| N12 | `canonicalRootInsertPairExternal` | PASS 1/3 | `74d8a7d` |
| N13 | `canonicalSortingPairAligned` | PASS 1/3 | `af1ff7a` |
| N14 | `canonicalSortingPairSourceWellFormed` | PASS 1/3 | `2984c65` |
| N15 | `canonicalSortingAppendRightOccurrence` | PASS 1/3 | `40dcf95` |
| N16 | `canonicalSortingPairIndependent` | PASS 2/3 | `694d660` |
| N17 | `canonicalRootInsertHoistDiamond` | PASS 1/3 | `b3ac87d` |
| N18 | `CanonicalRootInsertionHoist` | PASS 1/3 | `64948d6` |
| N19 | `canonicalRootInsertionHoistFromDiamond` | PASS 1/3 | `dbeec85` |
| N20 | `canonicalRootInsertionHoist` | PASS 1/3 | `0ea1a11` |
| N21 | `canonicalHoistedRootOccurrence` | PASS 1/3 | `88bc6d2` |
| N22 | `canonicalHoistedRootOrdinal` | PASS 1/3 | `1fa867b` |
| N23 | `canonicalOriginalHoistedRootOccurrence` | PASS 1/3 | `1624837` |
| N24 | `canonicalSortingPrefixSnocCount` | PASS 1/3 | `427d8eb` |
| N25 | `canonicalRootHoistMovesOneOrdinal` | PASS 1/3 | `c48d682` |
| N26 | `canonicalRootHoistNonempty` | PASS 1/3 | `0738d2c` |
| N27 | `canonicalSortingAcceptRootHoist` | PASS 1/3 | `c93dfac` |
| N28 | `canonicalSortingHoistRoot` | PASS 1/3 | `f6677ee` |
| N29 | `canonicalSortingLifecycleActiveSame` | PASS 1/3 | `26772fa` |
| N30 | `canonicalSortingFiberActiveSame` | PASS 1/3 | `2f7b3de` |
| N31 | `canonicalSortingFiberComponentSame` | PASS 1/3 | `c7eed3b` |
| N32 | `canonicalSortingFiberParentSame` | PASS 1/3 | `69cc47d` |
| N33 | `canonicalSortingSupportFromRelatedActive` | PASS 1/3 | `17dec8c` |
| N34 | `canonicalSortingSupportFromActiveRank` | PASS 1/3 | `8c80210` |
| N35 | `canonicalSortingSupportTrueForward` | PASS 1/3 | `71f62f6` |
| N36 | `canonicalSortingPrecedenceFromFibers` | PASS 1/3 | `d484ef4` |
| N37 | `canonicalSortingPrecedenceForward` | PASS 1/3 | `72f7c1c` |
| N38 | `canonicalSortingParentFromFiber` | PASS 1/3 | `21863c4` |
| N39 | `canonicalSortingParentForward` | PASS 1/3 | `80e6d56` |
| N40 | `canonicalSortingSupportEdgeForward` | PASS 1/3 | `a7241d2` |
| N41 | `canonicalSortingSupportPathForward` | PASS 1/3 | `918ba6c` |
| N42 | `canonicalSortingFixedLinearization` | PASS 2/3 | `1e8105e` |

### C1–C49: a full O17 input, with an exact local obstruction

File: `research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr`.
This is a **retained checked candidate**, not one of the two disposable probes.
It imports the public R45 empty-key, Unit-world, tagged/ranked registration
fixture. Its exact checked trace is:

| Ordinal | Checked action | Role |
|---|---|---|
| 0 | `OInsert 0 Root r45Parent` | external root birth |
| 1 | `LBegin 0` | the parent's sole open activation starts |
| 2 | `OInsert 1 (ChildOf 0) r45Child` | actual next tagged iterator step licenses this child |
| 3 | `ORetire 1` | internal retirement of that generated child |
| 4 | `ORemove 1` | internal removal; name 1 becomes fresh |
| 5 | `OInsert 1 Root r45Child` | a later external root reissues raw name 1 |
| 6 | `ORetire 1` | external retirement of the later root |
| 7 | `LAdvance 0`, `LFinishTag` | parent finishes; no closing episode occurs |

The root reissue is during the **still-open** parent's activation. The actual
`RegistrationDiscipline` licenses it: the generated child's immediate retirement
provides `ChildRetiredBeforeParent`; it does not forbid its removal/root reissue.
The endpoint is well-formed, quiet and failure-free, with support set **[0]**.
The checked finish equation excludes the executable final-state helper's default
branch; no assumed evaluator success is used.

**Every unchanged O17 input is constructed**, without calling its hole:
`r172ReuseTrace`, `r172ReuseBundle`, `r172ReuseShape`, `r172ReuseOrdering`.
The bundle includes full trace independence, totality, rank/parent-rank/path
capital and `SupportMatchesActive`; `r172ReuseNoClosing` derives the shape by
the existing proved O13 producer. `r172ReuseOrderingIsParentOnly` authenticates
O14's exact output **[0]** from membership/uniqueness laws, not an opaque `Refl`.
Trace independence is not assumed: all empty-key/Unit effect states have equal
runtime observations, generated transformations respect those observations,
partial domains are reflected, generated maps commute, and iterator outcomes
are stable by the public runtime-respect theorem.

Additional **proved** facts:

* `r172ReuseSourceNotRootFirst` rules out using the original trace as an already
  canonical identity terminal.
* `r172ReuseRootBeforeRemoveRejected` computes the later root insertion before
  the child removal to `Nothing` (the raw name is still occupied).
* `r172ReuseRemoveRootDiamondImpossible` rejects **every LocalRelationalDiamond
  for this exact immediate removal/root-insertion pair**, through its aligned
  moved-right equation. No pre-supplied target or diamond is hidden here.

**Not proved:** `SortedClosingFreeTrace ... r172ReuseTrace r172ReuseOrdering ->
Void`, or impossibility of every finite alternative sorting derivation. A local
failed crossing and a noncanonical input alone do not imply that negation.
The plausible global obstruction is a cycle: full discipline places the child
birth after parent begin; same-name insertion generations cannot reverse their
relative birth order via valid adjacent swaps; canonical all-root-first would
place the later root birth before that begin. Formalizing that invariant and
its occurrence/ordinal transports is still necessary. This is not a claimed
paper counterexample, nor permission to revise the frozen canonical-placement
surface. No false O17 body was manufactured to conceal this frontier.

#### Retained C micro-unit ledger

Each C row is one new top-level declaration in the total, unbound-implicits-off
candidate fixture. Local `where` proofs are explicit; no new `let`/`with`.

| Unit | Declaration | Check | Commit |
|---|---|---|---|
| C1 | `r172ReuseRootFresh` | PASS 1/3 | `be67d97` |
| C2 | `r172ReuseAfterRoot` | PASS 1/3 | `c2888d8` |
| C3 | `r172ReuseRootRetired` | PASS 1/3 | `9d5ba78` |
| C4 | `r172ReuseAfterRetire` | PASS 1/3 | `1e0e123` |
| C5 | `r172ReuseFinal` | PASS 1/3 | `b0fb77b` |
| C6 | `r172ReuseRemoveChecked` | PASS 1/3 | `c648250` |
| C7 | `r172ReuseRootChecked` | PASS 1/3 | `900c6a0` |
| C8 | `r172ReuseRetireChecked` | PASS 1/3 | `1cd47df` |
| C9 | `r172ReuseFinishChecked` | PASS 1/3 | `755254b` |
| C10 | `r172ReuseRemove` | PASS 1/3 | `7a90861` |
| C11 | `r172ReuseRoot` | PASS 1/3 | `404b5bb` |
| C12 | `r172ReuseRetire` | PASS 1/3 | `4ce45ab` |
| C13 | `r172ReuseFinish` | PASS 1/3 | `a7286f2` |
| C14 | `r172ReuseTail` | PASS 1/3 | `7645629` |
| C15 | `r172ReuseTrace` | PASS 1/3 | `8566dcb` |
| C16 | `r172ReuseAligned` | PASS 1/3 | `6a31871` |
| C17 | `r172ReuseDiscipline` | PASS 1/3 | `def5e50` |
| C18 | `r172ReuseInitialWellFormed` | PASS 1/3 | `72fd98a` |
| C19 | `r172ReuseInitialEmpty` | PASS 1/3 | `59fced7` |
| C20 | `r172ReuseFinalWellFormed` | PASS 1/3 | `085370d` |
| C21 | `r172ReuseQuiet` | PASS 1/3 | `8b307be` |
| C22 | `r172ReuseNoFailure` | PASS 1/3 | `84a6f64` |
| C23 | `r172ReuseSupportSet` | PASS 1/3 | `3b0a8df` |
| C24 | `r172ReuseAnyTransitionTotal` | PASS 1/3 | `6f0af99` |
| C25 | `r172ReuseTotal` | PASS 1/3 | `757235a` |
| C26 | `r172ReuseEmptyKeyBindings` | PASS 1/3 | `0a37fde` |
| C27 | `r172ReuseAllEffectStatesRelated` | PASS 1/3 | `efcb8c6` |
| C28 | `r172ReuseRelatedBind` | PASS 1/3 | `36f57d4` |
| C29 | `r172ReuseTransformationRespects` | PASS 2/3 | `d80e9f6` |
| C30 | `r172ReuseUndefinedRight` | PASS 1/3 | `76a4072` |
| C31 | `r172ReuseBothDefinedRelated` | PASS 1/3 | `f1b24e4` |
| C32 | `r172ReuseCommuteAt` | PASS 1/3 | `274ded9` |
| C33 | `r172ReuseMapsCommute` | PASS 1/3 | `f429fa1` |
| C34 | `r172ReuseIteratorStableAt` | PASS 1/3 | `41ea1a5` |
| C35 | `r172ReuseIndependent` | PASS 1/3 | `ce8001e` |
| C36 | `r172ReuseReached` | PASS 1/3 | `9d30a7c` |
| C37 | `r172ReuseProvenance` | PASS 1/3 | `474f273` |
| C38 | `r172ReuseBundle` | PASS 1/3 | `24efce9` |
| C39 | `r172ReuseNoUnload` | PASS 1/3 | `c435481` |
| C40 | `r172ReuseAppendRightOccurrence` | PASS 1/3 | `035d428` |
| C41 | `r172ReuseClosingOccurs` | PASS 2/3 | `27c0d29` |
| C42 | `r172ReuseNoClosing` | PASS 1/3 | `0ca2a41` |
| C43 | `r172ReuseShape` | PASS 1/3 | `f0147a5` |
| C44 | `r172ReuseOrdering` | PASS 1/3 | `e5ee1b5` |
| C45 | `r172ReuseSourceNotRootFirst` | PASS 2/3 | `21bf0d3` |
| C46 | `r172ReuseRootBeforeRemoveRejected` | PASS 1/3 | `db8b9c0` |
| C47 | `r172ReuseMovedRootImpossible` | PASS 1/3 | `e7ee8c5` |
| C48 | `r172ReuseRemoveRootDiamondImpossible` | PASS 1/3 | `ccd0e2e` |
| C49 | `r172ReuseOrderingIsParentOnly` | PASS 2/3 | `a069cbc` |

### Continuation failures and corrections (all charged)

All N/C units not listed here passed 1/3. O17's body was never attempted.

* **N10-1 → N10-2:** dependent impossible root/child equality had residual named
  component indices; replacing those impossible-clause arguments with `_`
  removed the binding wall without changing the statement.
* **N16-1 → N16-2:** the exact occurrence-embedding type required the direct
  `DGamma.CP4RecoveryModelTrace` import, not a visibility edit.
* **N42-1 → N42-2:** `controlEquivalentSymmetric` required direct
  `DGamma.CP3Support` import, not a new assumption.
* **C29-1 → C29-2:** independently generated anonymous case trees did not
  definitionally identify with executable `partialCompose`; the corrected
  proof carries actual evaluation equations through a local composition fold.
  C28's weaker case-tree lemma remains honest but is not used by that fold.
* **C41-1 → C41-2:** `prefix` was a reserved token, not a term variable; renamed
  to `earlier`. No statement change.
* **C45-1 → C45-2:** the concrete nested indexed pattern exceeded the external
  **120-second** tool window. The wrapper and compiler were gone by the
  **13:55:06 UTC** inspection; the buffered log was empty. This is charged as
  exit 124 in the ledger, **not** a compiler Error diagnostic or pass. The RSS
  sample was lost with the wrapper (the ledger's 0 means unavailable). A generic
  occurrence eliminator replaced the deeply nested concrete NoRoot match; the
  same theorem then passed in 15.1 seconds. No concurrent compiler was started.
* **C49-1 → C49-2:** O14's returned order was opaque to direct `Refl`; the
  corrected proof uses its actual four-field linearization certificate and a
  singleton unique-enumeration argument. No metadata/visibility widening.

Complete diagnostic-bearing failed outputs follow (trailing spaces normalized
for the baseline whitespace gate). The already ratified P1-1
(exit 0 with Error diagnostics) and M42-1 failures remain recorded above and are
included in the cumulative failure count.

#### N10-1

```text
3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Error: Impossible pattern gives an error:
When unifying:
    OInsert ?child (ChildOf ?parent) ?childComponent = OInsert ?child (ChildOf ?parent) ?childComponent
and:
    OInsert ?root Root ?rootComponent = OInsert ?child (ChildOf ?parent) ?childComponent
Pattern variable rootComponent unifies with: ?childComponent [no locals in scope].

DGamma.CP5ConfluenceCanonicalSortSpike:1448:81--1448:109
      |
 1448 | canonicalRootChildInsertImpossible name key world error value root child parent rootComponent childComponent Refl impossible
      |                                                                                 ^^^^^^^^^^^^^ ^^^^^^^^^^^^^^

Suggestion: Use the same name for both pattern variables, since they unify.
```

#### N16-1

```text
3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Error: While processing right hand side of canonicalSortingPairIndependent. When unifying:
    OccurrenceEmbedding name key world error value pairFirst pairFinal pairFirst originalFinal (MoreTransitions left (MoreTransitions right NoTransitions)) (appendTransitions (MoreTransitions left (MoreTransitions right NoTransitions)) suffix)
and:
    Transition stepBefore stepAfter -> OccursIn transition (MoreTransitions left (MoreTransitions right NoTransitions)) -> OccursIn transition (MoreTransitions left (MoreTransitions right suffix))
Undefined name DGamma.CP4RecoveryModelTrace.OccurrenceEmbedding.

DGamma.CP5ConfluenceCanonicalSortSpike:1543:10--1543:125
 1539 |   traceIndependentUnderEmbedding
 1540 |     (\transition, occurs => replace {p = OccursIn transition} decomposition
 1541 |       (canonicalSortingAppendRightOccurrence name key world error value prefixTrace
 1542 |         (MoreTransitions left (MoreTransitions right suffix)) transition
 1543 |         (appendLeftOccurrenceEmbedding (MoreTransitions left (MoreTransitions right NoTransitions)) suffix transition occurs)))
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

#### N42-1

```text
3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Error: While processing right hand side of canonicalSortingFixedLinearization. Undefined name controlEquivalentSymmetric.

DGamma.CP5ConfluenceCanonicalSortSpike:1917:12--1917:38
 1913 |         (canonicalSortingSupportTrueForward name key world error value protocol nameEq keyEq target source
 1914 |           targetRanked targetMatches sourceMatches (controlEquivalentSymmetric controls) selected supported))
 1915 |       (\lower, upper, path, lowerIn, upperIn => supportPathsOrdered linearization lower upper
 1916 |         (canonicalSortingSupportPathForward name key world error value nameEq target source
 1917 |           (controlEquivalentSymmetric controls) lower upper path) lowerIn upperIn)
                   ^^^^^^^^^^^^^^^^^^^^^^^^^^
```

#### C29-1

```text
2/2: Building DGamma.R172O17OpenParentRootReuseCandidate (research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr)
Error: While processing right hand side of r172ReuseTransformationRespects. Can't solve constraint between: case runTraceEffectTransformation before x of
  { Nothing => Nothing
  ; Just middle => runTraceEffectTransformation after middle
  } and case runTraceEffectTransformation before x of
  { Nothing => Nothing
  ; Just middle => runTraceEffectTransformation after middle
  }.

DGamma.R172O17OpenParentRootReuseCandidate:185:3--187:59
 185 |   r172ReuseRelatedBind (runTraceEffectTransformation before x) (runTraceEffectTransformation before y)
 186 |     (runTraceEffectTransformation after) (r172ReuseTransformationRespects actor after)
 187 |     (r172ReuseTransformationRespects actor before related)
```

#### C41-1

```text
2/2: Building DGamma.R172O17OpenParentRootReuseCandidate (research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr)
Error: Couldn't parse declaration.

DGamma.R172O17OpenParentRootReuseCandidate:334:1--334:23
 330 |   {selected : Nat} -> {initial, finalState : SystemState Nat R45Key R45Value Unit String} ->
 331 |   {trace : Transitions initial finalState} ->
 332 |   (located : LocatedClosedEpisode Nat R45Key Unit String R45Value r45NameEq r45KeyEq selected trace) ->
 333 |   OccursIn (unloadTransition (closing (locatedEpisode located))) trace
 334 | r172ReuseClosingOccurs (MkLocatedClosedEpisode pre after prefix episode suffix decomposition) =
       ^^^^^^^^^^^^^^^^^^^^^^
```

#### C49-1

```text
2/2: Building DGamma.R172O17OpenParentRootReuseCandidate (research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr)
Error: While processing right hand side of r172ReuseOrderingIsParentOnly. Can't solve constraint between: [0] and r172ReuseOrdering .orderedSupportNames.

DGamma.R172O17OpenParentRootReuseCandidate:399:33--399:37
 395 |   (movedPairAligned diamond) (movedRightAction diamond)
 396 |
 397 | public export
 398 | 0 r172ReuseOrderingIsParentOnly : orderedSupportNames r172ReuseOrdering = [0]
 399 | r172ReuseOrderingIsParentOnly = Refl
                                       ^^^^
```

The baseline whitespace validator, not the compiler, found one final blank
line in the newly added candidate file. `775bd22` removes exactly that line;
its fresh check passed. This zero-declaration correction is separate from the
49 C declarations, not a hidden extra C49 body attempt. No compiler failure is
charged for a documentation/whitespace validation assertion.

### Refreshed continuation validation and frozen boundaries

Eight serial continuation gate invocations passed, including the final
whitespace-only source check. CanonicalSort and the candidate were source-mtime
refreshed only to force fresh elaboration; no TTC or source bytes were deleted.
RenamingComposition and CrossTrace also freshly elaborated as dependents.
DeletionChain and LocalDiamond are explicitly **cached boundary checks** here;
their unchanged bytes still have the genuine Unit A fresh-check evidence
(85.6 seconds / 4,339,104 KiB and 503.9 seconds / 50,365,840 KiB respectively).
Inherited CrossTrace shadowing warnings are not new diagnostics.

| Check | UTC start–end | Outcome | Sample peak KiB |
|---|---|---|---|
| `gate-o17-CanonicalSort` | 14:01:48–14:01:58 | PASS; fresh | 748,768 |
| `gate-o17-RenamingComposition` | 14:01:58–14:02:09 | PASS; fresh | 815,360 |
| `gate-o17-CrossTrace` | 14:02:09–14:02:14 | PASS; fresh | 0 |
| `gate-o17-DeletionChain` | 14:02:14–14:02:19 | PASS; seeded/cached | 0 |
| `gate-o17-LocalDiamond` | 14:02:19–14:02:24 | PASS; seeded/cached | 0 |
| `gate-o17-candidate` | 14:02:24–14:02:39 | PASS; fresh | 1,734,464 |
| `gate-o17-package` | 14:02:39–14:02:59 | PASS; seeded/cached | 219,920 |
| `gate-o17-candidate-whitespace` | 14:05:05–14:05:20 | PASS; fresh | 1,727,776 |

Cumulative compiler ledger: **166 invocations = 157 diagnostic-clean passes +
9 charged corrected failures**, including the external C45 timeout. The original
P1 diagnostic is recomputed from its full log because its early wrapper had no
`diagnosticErrors` field. Every successful micro-unit has a fresh `Building`
marker and an immediately following source commit: **133 new top-level
declarations**, **135 source commits** (85 CanonicalSort, including O14's body;
50 candidate, including the zero-declaration whitespace correction). All budgets
are ≤2/3 in the continuation. No clean-rebuild or R11/R16/full-runtime-suite pass
is claimed; all 207/207 production module seeds remain.

The refreshed validator checks stripping **only** the two exact private capital
blocks, O14's new body and the three imports restores CanonicalSort at `0e58c54`;
both original O14/O17 signatures are exact. The other four research sources are
byte-identical to start. It also checks the ratified O14 audit is an exact prefix,
both disposable probes have no source/TTC/TTM, each source commit adds ≤1
new top-level declaration, all clean commit checks are unique and fresh, and
no compiler is left running.

* `src/` and `dgamma.ipkg`: empty diff against **34b21c9**.
* LocalDiamond: empty diff against **0e58c54**; full frozen suffix producer is
  **1470 bytes**, SHA-256
  `2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf`.
* Frozen statement prefix: **1154 bytes**, SHA-256
  `3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf`.
* CP3 blob: `2c697e532e83989de8591fa6a4378747c6a501c0`.
* Untracked adversarial review SHA-256 remains
  `61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8`;
  it was never staged, modified or removed. Only it and `paper/` are untracked.
* DeletionChain legacy `with (` count: **9 → 9**; no exception renewed.
* No new hole, unsafe totality escape, postulate, residual as-pattern, `let`,
  `with`, frozen deletion-theorem call or generation-scoped-to-raw cast.

Live six-hole coordinates: CanonicalSort `sortClosingFreeTraceSpike_rhs:1935`;
CrossTrace `operationalAdjacentBlockSwapSpike_rhs:714`,
`canonicalSupportOrdersMatchSpike_rhs:986`,
`selectOperationalCanonicalPermutationSpike_rhs:1067`,
`canonicalSchedulesConvergeSpike_rhs:1325`; RenamingComposition
`replayedCanonicalToOriginalEndpointSpike_rhs:2723`. DeletionChain/LocalDiamond
remain hole-free. The reconnaissance memo deliberately remains the ratified
**seven-hole start-coordinate snapshot**, not silently rewritten.

### Gate request / next, not authorization

O17 should stay open pending either a proved global generation-order obstruction
or a real alternative operational selector; current capital proves neither full
sorting nor its negation. Retain the full-input candidate and exact local wall
for review. O14's fixed-order transport through no-withdrawal equivalence is useful
capital, not a cure for deletion-order matching or registration accounting.

At this checkpoint more than 90 minutes remain until the absolute shift deadline;
request the supervisor's O17 stop/frontier ruling and **separate authorization
for ranked target #3, canonical support matching, probe-first**, rather than
self-starting it. O19's body, O21 withdrawals, production/surface revision and
debt-register implementation remain forbidden. The accounting/original-order,
R16/R129, concrete two-birth/one-withdrawal and repeated-Iter, copied-with and
paper/guarded-scope debts remain OPEN/parked exactly as catalogued in the plan.
