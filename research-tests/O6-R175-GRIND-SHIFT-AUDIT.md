# R175 grind-shift audit

Start **2026-09-06 23:50:09 UTC**, branch `cp5-thm73-scoping`, required HEAD
`c4e78e0a16806cf57095d2bb68afa3da9dfadb2c`; only allowed untracked `paper/`
and frozen `review-o6-body-adversarial.md`. Idris **0.8.0**; `--source-dir`
and `--check` verified with `idris2 --help`; no compiler orphan at start.
Required R174 audit/recon, R173 audit, THM73-PLAN and R146 strategy read first;
the complete 3883-line paper was read. No new attempt after **03:10:09 UTC**;
safe final gate by **03:35:09 UTC**, timeout **03:50:09 UTC** on September 7.

## Boundaries and protocol

Research only, one top-level declaration per fresh source invocation, at most
three attempts per micro-unit; commit immediately on success. Seeded checks
only, serialized detached wrapper with RSS sampling. No build deletion.
Production/package frozen against `34b21c9`; CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0`. Root placement/hoisting is
OWNER-PAUSED; no O17 body, O19 body, O21 withdrawal work, G31, Q9 or archived
C58 restatement; no new `with`, local let aliases, partiality or proof escapes.
Unit B gets at most 15 micro-units. Unit C is analysis only, at most 40 minutes.

## Unit A — surface-independent producers

The A/O grouping branch is a generated insertion of the selected parent, NOT
root placement. Its early applicability is already derived inside the existing
A/O diamond. First integrate that actual branch using the selected pair's owned
registration and derived foreign-parent/scalar distinctness, then address the
selected Iter/Finish branches. Classification alone is not an applicable swap.

| Unit | Declaration | Commit | Fresh check / attempts |
|---|---|---|---|
| A1 | `canonicalWorkOwnedOrchestrationInsertion` | `bd6d056` | PASS 1/3, 2026-09-06T23:54:54.103633+00:00–2026-09-06T23:55:49.063669+00:00, 19280480 KiB sampled |
| A2 | `canonicalWorkGroupingActivationOrchestrationDiamond` | `27c8fbe` | PASS 1/3, 2026-09-06T23:56:20.781032+00:00–2026-09-06T23:57:15.742100+00:00, 18941600 KiB sampled |
| A3 | `canonicalWorkRegistrationInternal` | `9ed32d8` | PASS 1/3, 2026-09-06T23:57:40.752026+00:00–2026-09-06T23:58:35.720778+00:00, 18199200 KiB sampled |
| A4 | `canonicalWorkGroupingActivationOrchestrationExternal` | `c42e402` | PASS 1/3, 2026-09-06T23:59:09.994842+00:00–2026-09-07T00:00:04.945283+00:00, 18144016 KiB sampled |
| A5 | `canonicalWorkGroupingActivationOrchestrationResult` | `fffbc2b` | PASS 1/3, 2026-09-07T00:00:33.362619+00:00–2026-09-07T00:01:28.313827+00:00, 18191888 KiB sampled |
| A6 | `canonicalWorkAdvanceActivationOrchestration` | `1f1c9c8` | PASS 1/3, 2026-09-07T00:01:56.021981+00:00–2026-09-07T00:02:50.934951+00:00, 18153584 KiB sampled |

## Unit B — raw-closing maximum under uniqueness

Not started. The target is the existential `rawClosingMaximumUnderUniqueInsertions`
from R174 reconnaissance, via immutable cross-time rank coherence. It does not
cast an arbitrary scoped maximum to raw maximality or call the frozen deletion
proof. No satisfiability discharge is claimed before its actual source checks.

## Unit C — O21 uniqueness-threading plan

Not started; no signature edits authorized.

## Status

Start census **6 = 1/4/0/0/1** (CanonicalSort / CrossTrace / DeletionChain /
LocalDiamond / RenamingComposition), unchanged. O17 remains open; root clause
owner-paused. Validation and full ledger to be appended at the committed gate.

## Unit A milestone and policy-cycle design gate

A1–A6 are complete and independently fresh-checked at each immediate commit.
They produce the ACTUAL A/O grouping diamond and sealed result from the same
pair, deriving child/actor and licensing-parent inequalities, both internal
external-order directions, and the existing full reached reinspection. No
root-phase helper was modified or invoked by this chain. Other orientations,
early Iter/Finish applicability, structural BlockBefore, global measure and
exact accounting remain OPEN. All six holes remain unchanged.

Before further proof work, source inspection found an abstract cycle in the
OLD grouping-before-ordering policy. With pending order [0,1], the ownership
word of Begin1;Begin0;Finish0;Finish1 is [1,0,0,1]. Actor0 is a ready contiguous
block; actor1 NeedsGrouping despite opening before it. Grouping swaps the final
two nodes to [1,0,1,0]. Reinspection now groups actor0 by the inverse final swap.
Thus unconditional S17 reinspection plus every old selected grouping swap is
not a strictly decreasing global algorithm. This is a structural policy analysis,
NOT a full checked O17-input execution countermodel. The supervisor ratified
A1–A6, accepted the old global-measure route as dead, and authorized an INTERNAL
selector/progress redesign with a HARD CAP of 12 micro-units including first
a cheap abstract-cycle regression. No theorem surface change was authorized.
The proposed design (not implemented) is whole-state inversion count relative
to fixed order, plus grouping debt, selecting ordering before grouping where
an opening precedes a completed block; selection and decrease must be built
simultaneously, never selected and justified afterwards.

### D1 mandatory stop — 3/3 compiler rejections, fully removed

The FIRST prerequisite regression declaration exhausted its budget. No redesign
source or measure was attempted (D2–D12 unspent). D1 was a lightweight abstract
ownership-word policy calculation, explicitly NOT a full operational trace or
bundle. Attempts 1/2 were rejected by ambiguity depth at nested pair/equality
and List operations. Attempt 3 fully instantiated Equal's two argument types
and passed that spelling boundary, but used `Data.List.reverse`; Idris reports
the actual function is `Prelude.Types.List.reverse`. That obvious correction
was NOT tried: no fourth attempt. All failed declarations and full diagnostics
are archived below. The source and any newly created module TTC/TTM are removed.
A new supervisor ruling is required before continuing; no implicit budget reset.

A wrapper startup before A1 failed because non-isolated Python imported the
unrelated `/tmp/nt.py` through pathlib/ntpath. It spawned NO Idris process;
not a compiler attempt or verdict. Every compiler invocation uses Python -I
thereafter. There was no orphan or compiler overlap.

### D1-1 removed declaration and full diagnostic

```idris
module DGamma.R175OldGroupingPolicyCycle

import Data.List
import Data.Nat

%default total
%unbound_implicits off

||| Cheap ABSTRACT policy regression, not a full O17-input execution fixture.
||| Encode Begin1; Begin0; Finish0; Finish1 by ownership word [1,0,0,1].
||| For each pending actor [0,1], skip to its first node, skip its contiguous
||| run, then test for a remaining owned node: precisely the grouping-before-
||| ordering policy of canonicalWorkInspectScanned / SelectGroupingPair.
||| The first debt is actor1, moving the last node across its foreign neighbor.
||| Reinspection chooses actor0 and moves that same last position back.
||| This proves the abstract selection cycle only; no evaluator/bundle claim.
export
0 r175OldGroupingPolicyCycle :
  ((find (\actor => elem actor
       (dropWhile (== actor) (dropWhile (/= actor) (the (List Nat) [1, 0, 0, 1])))) [0, 1],
    (take 2 (the (List Nat) [1, 0, 0, 1]) ++ reverse (drop 2 (the (List Nat) [1, 0, 0, 1]))),
    find (\actor => elem actor
       (dropWhile (== actor) (dropWhile (/= actor) (the (List Nat) [1, 0, 1, 0])))) [0, 1],
    (take 2 (the (List Nat) [1, 0, 1, 0]) ++ reverse (drop 2 (the (List Nat) [1, 0, 1, 0])))) =
   (Just 1, [1, 0, 1, 0], Just 0, [1, 0, 0, 1]))
r175OldGroupingPolicyCycle = Refl
```

```text
1/1: Building DGamma.R175OldGroupingPolicyCycle (research-tests/DGamma/R175OldGroupingPolicyCycle.idr)
Error: While processing type of r175OldGroupingPolicyCycle. Maximum ambiguity depth exceeded in DGamma.R175OldGroupingPolicyCycle.r175OldGroupingPolicyCycle:
Data.List.take --> Prelude.Types.List.(++) --> Builtin.MkPair --> ===

DGamma.R175OldGroupingPolicyCycle:24:29--24:30
 20 |        (dropWhile (== actor) (dropWhile (/= actor) (the (List Nat) [1, 0, 0, 1])))) [0, 1],
 21 |     (take 2 (the (List Nat) [1, 0, 0, 1]) ++ reverse (drop 2 (the (List Nat) [1, 0, 0, 1]))),
 22 |     find (\actor => elem actor
 23 |        (dropWhile (== actor) (dropWhile (/= actor) (the (List Nat) [1, 0, 1, 0])))) [0, 1],
 24 |     (take 2 (the (List Nat) [1, 0, 1, 0]) ++ reverse (drop 2 (the (List Nat) [1, 0, 1, 0])))) =
                                  ^

Suggestion: the default ambiguity depth limit is 3, the %ambiguity_depth pragma can be used to extend this limit, but beware compilation times can be severely impacted.
```

### D1-2 removed declaration and full diagnostic

```idris
module DGamma.R175OldGroupingPolicyCycle

import Data.List
import Data.Nat

%default total
%unbound_implicits off

||| Cheap ABSTRACT policy regression, not a full O17-input execution fixture.
||| Encode Begin1; Begin0; Finish0; Finish1 by ownership word [1,0,0,1].
||| For each pending actor [0,1], skip to its first node, skip its contiguous
||| run, then test for a remaining owned node: precisely the grouping-before-
||| ordering policy of canonicalWorkInspectScanned / SelectGroupingPair.
||| The first debt is actor1, moving the last node across its foreign neighbor.
||| Reinspection chooses actor0 and moves that same last position back.
||| This proves the abstract selection cycle only; no evaluator/bundle claim.
export
0 r175OldGroupingPolicyCycle :
  ((Data.List.find (\actor => elem actor
       (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 0, 1])))) [0, 1],
    (Data.List.take 2 (the (List Nat) [1, 0, 0, 1]) ++ Data.List.reverse (Data.List.drop 2 (the (List Nat) [1, 0, 0, 1]))),
    Data.List.find (\actor => elem actor
       (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 1, 0])))) [0, 1],
    (Data.List.take 2 (the (List Nat) [1, 0, 1, 0]) ++ Data.List.reverse (Data.List.drop 2 (the (List Nat) [1, 0, 1, 0])))) =
   (Just 1, [1, 0, 1, 0], Just 0, [1, 0, 0, 1]))
r175OldGroupingPolicyCycle = Refl
```

```text
1/1: Building DGamma.R175OldGroupingPolicyCycle (research-tests/DGamma/R175OldGroupingPolicyCycle.idr)
Error: While processing type of r175OldGroupingPolicyCycle. Maximum ambiguity depth exceeded in DGamma.R175OldGroupingPolicyCycle.r175OldGroupingPolicyCycle:
Prelude.Types.List.(++) --> Builtin.MkPair --> Builtin.MkPair --> ~=~

DGamma.R175OldGroupingPolicyCycle:21:39--21:40
 17 | export
 18 | 0 r175OldGroupingPolicyCycle :
 19 |   ((Data.List.find (\actor => elem actor
 20 |        (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 0, 1])))) [0, 1],
 21 |     (Data.List.take 2 (the (List Nat) [1, 0, 0, 1]) ++ Data.List.reverse (Data.List.drop 2 (the (List Nat) [1, 0, 0, 1]))),
                                            ^

Suggestion: the default ambiguity depth limit is 3, the %ambiguity_depth pragma can be used to extend this limit, but beware compilation times can be severely impacted.
```

### D1-3 removed declaration and full diagnostic

```idris
module DGamma.R175OldGroupingPolicyCycle

import Data.List
import Data.Nat

%default total
%unbound_implicits off

||| Cheap ABSTRACT policy regression, not a full O17-input execution fixture.
||| Encode Begin1; Begin0; Finish0; Finish1 by ownership word [1,0,0,1].
||| For each pending actor [0,1], skip to its first node, skip its contiguous
||| run, then test for a remaining owned node: precisely the grouping-before-
||| ordering policy of canonicalWorkInspectScanned / SelectGroupingPair.
||| The first debt is actor1, moving the last node across its foreign neighbor.
||| Reinspection chooses actor0 and moves that same last position back.
||| This proves the abstract selection cycle only; no evaluator/bundle claim.
export
0 r175OldGroupingPolicyCycle :
  (Equal {a = Maybe Nat} {b = Maybe Nat}
    (Data.List.find (\actor => elem actor
      (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 0, 1])))) [0, 1]) (Just 1),
   Equal {a = List Nat} {b = List Nat}
    (1 :: 0 :: Data.List.reverse (the (List Nat) [0, 1])) [1, 0, 1, 0],
   Equal {a = Maybe Nat} {b = Maybe Nat}
    (Data.List.find (\actor => elem actor
      (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 1, 0])))) [0, 1]) (Just 0),
   Equal {a = List Nat} {b = List Nat}
    (1 :: 0 :: Data.List.reverse (the (List Nat) [1, 0])) [1, 0, 0, 1])
r175OldGroupingPolicyCycle = (Refl, Refl, Refl, Refl)
```

```text
1/1: Building DGamma.R175OldGroupingPolicyCycle (research-tests/DGamma/R175OldGroupingPolicyCycle.idr)
Error: While processing type of r175OldGroupingPolicyCycle. Undefined name Data.List.reverse.

DGamma.R175OldGroupingPolicyCycle:28:16--28:33
 24 |    Equal {a = Maybe Nat} {b = Maybe Nat}
 25 |     (Data.List.find (\actor => elem actor
 26 |       (Data.List.dropWhile (== actor) (Data.List.dropWhile (/= actor) (the (List Nat) [1, 0, 1, 0])))) [0, 1]) (Just 0),
 27 |    Equal {a = List Nat} {b = List Nat}
 28 |     (1 :: 0 :: Data.List.reverse (the (List Nat) [1, 0])) [1, 0, 0, 1])
                     ^^^^^^^^^^^^^^^^^
Did you mean any of: Prelude.Types.List.reverse, Prelude.Types.SnocList.reverse, Prelude.Types.reverse, Reverse, or traverse?
```

### D1 authorized repair and redesign note (BEFORE D2 code)

Supervisor explicitly authorized EXACTLY one further invocation, D1-4, changing
ONLY `Data.List.reverse` to the compiler-suggested
`Prelude.Types.List.reverse`. It passed fresh (00:10:35–00:10:37 UTC), committed
`9bfd15f`. The stopped D1 ledger above is retained, not silently reset. The
fixture is an abstract ownership-policy regression, never a checked operational
O17 countermodel. D1 counts as one of the 12 authorized redesign micro-units.

The redesign measure is the inversion count of the WHOLE reached ownership
word under the SAME fixed desired support order, not distance to the currently
selected actor. An owned registration has its parent block's rank, not its
child's actor rank. Equal-ranked nodes do not contribute inversions. Sorting
by this rank simultaneously orders and groups all covered owned nodes; a
separate grouping debt is unnecessary for the fully covered internal word.
External/unowned nodes MUST be treated as barriers by a future operational
bridge; this shift does not attempt to move them or build any root placement.
A selector may only return a strictly descending adjacent rank pair. In the
old cycle, [1,0,0,1] selects the FIRST 1/0 ordering inversion, never the last
0/1 pair; the inverse move is then forbidden. This is ordering-first in a
single measure rather than an independently reset per-actor grouping phase.

Implementation order D2–D12: simple executable natural-number crossing count
and whole-word inversion function; explicit arithmetic lemmas; a dependent
progress packet tying an ACTUAL adjacent decomposition, its exact swapped
word, preservation of every outside-node contribution and strict whole-word
decrease; head/lift producers; a structurally recursive selector constructing
that packet SIMULTANEOUSLY with its choice. No candidate result is computed
and subsequently assumed to decrease. The final bounded slots attempt the
trace/worklist observation bridge. Until the ACTUAL sealed suffix replay is
shown to preserve this observation and the operational selector consumes the
same packet, this is only ranked-word progress capital, NOT the requested
complete worklist measure or operational progress proof. No existing S17 or
O17 signature/body is replaced by a weaker theorem. If D12 is reached before
that integration, audit-park the remaining measure and proceed to B/C.

## Redesign cap gate (D1–D12 consumed; no D13 authorized)

| Unit | Declaration | Immediate commit | Fresh source check |
|---|---|---|---|
| D1 | `r175OldGroupingPolicyCycle` | `9bfd15f` | PASS D1-4, 2026-09-07T00:10:35.827678+00:00–2026-09-07T00:10:37.891379+00:00, 0 KiB sampled |
| D2 | `rankCrossing` | `9a88147` | PASS D2-1, 2026-09-07T00:14:01.973913+00:00–2026-09-07T00:14:04.005368+00:00, 0 KiB sampled |
| D3 | `rankInversions` | `44a723b` | PASS D3-1, 2026-09-07T00:14:14.975908+00:00–2026-09-07T00:14:17.030331+00:00, 0 KiB sampled |
| D4 | `rankPlusSwap` | `c823562` | PASS D4-2, 2026-09-07T00:14:42.036729+00:00–2026-09-07T00:14:44.068344+00:00, 0 KiB sampled |
| D5 | `rankCrossingAsymmetric` | `07f1364` | PASS D5-1, 2026-09-07T00:14:55.690453+00:00–2026-09-07T00:14:57.744481+00:00, 0 KiB sampled |
| D6 | `rankHeadInversionDrop` | `7497737` | PASS D6-2, 2026-09-07T00:15:29.463366+00:00–2026-09-07T00:15:31.500518+00:00, 0 KiB sampled |
| D7 | `RankedAdjacentProgress` | `bbc5f97` | PASS D7-1, 2026-09-07T00:15:49.212322+00:00–2026-09-07T00:15:51.252568+00:00, 0 KiB sampled |
| D8 | `rankHeadProgress` | `f48f604` | PASS D8-1, 2026-09-07T00:16:06.808598+00:00–2026-09-07T00:16:08.857299+00:00, 0 KiB sampled |
| D9 | `rankLiftProgress` | `ef9099f` | PASS D9-3, 2026-09-07T00:17:13.718750+00:00–2026-09-07T00:17:15.773718+00:00, 0 KiB sampled |
| D10 | `rankSelectProgress` | `d496401` | PASS D10-1, 2026-09-07T00:17:31.050118+00:00–2026-09-07T00:17:33.112398+00:00, 0 KiB sampled |
| D11 | `canonicalWorkRankSegments` | `93820ac` | PASS D11-1, 2026-09-07T00:18:32.394507+00:00–2026-09-07T00:19:29.373047+00:00, 20063824 KiB sampled |
| D12 | `canonicalWorkGlobalInversionMeasure` | `ffb58ef` | PASS D12-1, 2026-09-07T00:20:04.471950+00:00–2026-09-07T00:20:59.440583+00:00, 18092192 KiB sampled |

D4-1 rejected a reserved `total` lambda binder; D4-2 renamed it `combined`.
D6-1 exposed that Prelude `sum` is a left fold, not a definitionally reducing
right fold. D6-2 changed the already-new D3 implementation (same signature,
same intended numerical function, no external consumer yet) to explicit
`foldr (+) Z` and used that same transparent fold throughout the proofs.
D9-1 rejected reserved `prefix` in the constructor pattern. The intended BSD
sed replacement before D9-2 matched nothing, so D9-2 was a repeated parse
rejection (counted, not hidden). D9-3 used Python's exact word replacement to
`prior`; PASS. All other D2–D12 declarations passed first invocation. Each
successful compiler invocation introduced exactly one new top-level declaration.
No fourth invocation occurred except the explicitly authorized D1-4 repair.

The mathematics is PROVED: runtime first-descent selection constructs a
concrete adjacent decomposition, invariance of every outside-node contribution,
and exact WHOLE-WORD inversion drop by one in the same recursive construction.
The old selector's changing selected actor cannot reset this measure. D11/D12
also define the barrier-separated rank observation and sum of inversions on
the ACTUAL whole CanonicalSortingWorklist with its original fixed desired
order. Non-owned orchestration creates a barrier; no external node is moved.
The new Data.List import produces one benign shadowing warning at the existing
`abstractTwoBirthOneWithdrawalAccounting` implicit `sorted` binder; no error.

CAP RESULT: PARTIAL / AUDIT-PARK. The operational bridge is NOT proved: a
ranked-segment selection must locate the same checked adjacent transitions,
produce their applicable orientation diamond, and show the ACTUAL sealed
suffix replay preserves the rank segments. `SealedSuffixReplaySpine` hides its
constructors from CanonicalSort; such transport needs a producer-local lemma
or an already sealed ordinal/action fold argument, not a scoped/raw cast.
No wrapper accepts rank decrease as an output-shaped operational premise.
No total sorter or canonical-form theorem is claimed when the numerical
selector returns Nothing. Structural BlockBefore, exact registration fold,
selected Iter/Finish early applicability and the remaining actual A/A, O/A,
O/O producers also remain OPEN. Existing A/O capital and S17 are intact.
Proceed only after the cap gate; next authorized bounded work is Unit B then C.

## Unit B bounded raw-premise attempt — B6 exhausted gate

The supervisor ratified the D12 park and authorized B (15 micro-units maximum)
then C. B1–B5 below are fresh-checked capital. They establish exact executable
action observation and authenticity of its ordinal, then prove that ANY TWO
authenticated O-Insert births of the same raw name carry the SAME component
under `UniqueRawNameInsertions`. B5 also proves that a successful raw action at
an absent owner MUST be O-Insert, excluding every other action by its evaluator.
None of this yet identifies the birth of a fiber observed at a later prefix.

| Unit | Declaration | Immediate commit | Fresh source check |
|---|---|---|---|
| B1 | `rawClosingActionAt` | `763696d` | PASS B1-2, 2026-09-07T00:26:08.035640+00:00–2026-09-07T00:26:10.075753+00:00, 0 KiB sampled |
| B2 | `rawClosingActionAtSplit` | `8598c0e` | PASS B2-1, 2026-09-07T00:26:27.753762+00:00–2026-09-07T00:26:29.808474+00:00, 0 KiB sampled |
| B3 | `rawClosingActionAtLocated` | `b1b2e96` | PASS B3-1, 2026-09-07T00:26:52.011768+00:00–2026-09-07T00:26:54.047950+00:00, 0 KiB sampled |
| B4 | `uniqueRawBirthComponents` | `5741519` | PASS B4-1, 2026-09-07T00:27:18.511047+00:00–2026-09-07T00:27:20.568256+00:00, 0 KiB sampled |
| B5 | `rawAbsentOwnerInsertion` | `3a7ca9e` | PASS B5-2, 2026-09-07T00:28:26.167715+00:00–2026-09-07T00:28:28.224261+00:00, 0 KiB sampled |

B1-1 rejected runtime use of transitionAction because its state parameters are
not erased; B1-2 matches Fired and returns the stored action directly. B5-1
rejected implicit type inference at polymorphic lookupFiber; B5-2 explicitly
supplied all five type parameters. All other B1–B5 first attempts passed.

B6 (`rawComponentBirthStep`) attempted the authentic one-step birth invariant
using the actual `applyActionLocalUpdate`. B6-1 failed a rewrite of action
classification under dependent owner equality. B6-2 replaced it with explicit
Equality transport and reached a COMPUTED-LOCAL-UPDATE refinement wall:
matching LocalInsert cannot refine a rigid `registry afterState` projection
(the LocalReplace/Delete warnings are elaborator fallout, not discarded legal
cases). B6-3 exposed source/target state constructors via as-patterns but the
as-bound state aliases remained rigid in the case block, producing a raw
execution-equation state mismatch. Budget EXHAUSTED 3/3. Entire B6 declaration
removed by restoring the B5 committed source; no fourth attempt, no hidden
signature change, no proof escape or deletionTheoremProof call.

B used 6 of 15 micro-units; B7–B15 unspent. A plausible future structural
separation is a generic EXPLICIT RegistryLocalUpdate induction helper rather
than case elimination on a computed update with rigid state projections, then
a producer invoking that helper on the actual evaluator result. That is a
new design proposal, NOT a tried repair or an assumed provenance theorem.
The target `rawClosingMaximumUnderUniqueInsertions` remains UNPROVED; immutable
component coherence at arbitrary reached prefix lookups, common-rank transport
and finite closing-rank maximum are all still missing. THM73-PLAN.md must NOT
reclassify CP3 satisfiability on these partial results. Gate before continuation.

### Removed final B6 candidate

```idris
||| Every observed component after one step has an authentic birth in the
||| chosen global trace, or inherits the SAME immutable component from before.
public export
0 rawComponentBirthStep :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (occurrence : LocatedActionOccurrence action global) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry before) = Just fiber ->
    (parent : Parent name ** LocatedActionOccurrence
      (OInsert selected parent (fiberComponent fiber)) global)) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry afterState) = Just observed ->
  (parent : Parent name ** LocatedActionOccurrence
    (OInsert selected parent (fiberComponent observed)) global)
rawComponentBirthStep name key world error value nameEq keyEq global action
  before@(MkSystemState beforeWorld sourceRegistry)
  afterState@(MkSystemState afterWorld targetRegistry) tag raw occurrence sourceBirth selected observed targetFound =
    case decEq @{nameEq} selected (actionOwner action) of
      No distinct => sourceBirth selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected (actionOwner action) distinct
          (registry before) (systemRegistryUpdate
            (applyActionLocalUpdate nameEq keyEq action before afterState tag raw)))) targetFound)
      Yes same => case same of
        Refl => case systemRegistryUpdate
          (applyActionLocalUpdate nameEq keyEq action before afterState tag raw) of
          LocalInsert next absent =>
            case rawAbsentOwnerInsertion name key world error value nameEq keyEq action
              before afterState tag raw absent of
              (parent ** (component ** inserted)) =>
                (parent ** replace
                  {p = \chosen => LocatedActionOccurrence (OInsert selected parent chosen) global}
                  (cong fiberComponent (justInjective
                    (trans (sym (oInsertResultLookup nameEq keyEq selected parent component
                      before afterState tag (replace
                        {p = \chosen => applyAction @{nameEq} @{keyEq} chosen before = Just (tag, afterState)}
                        inserted raw))) targetFound)))
                  (replace {p = \chosen => LocatedActionOccurrence chosen global} inserted occurrence))
          LocalReplace {oldFiber} {oldFound} {staticComponent} next =>
            case sourceBirth selected oldFiber oldFound of
              (parent ** born) =>
                (parent ** replace
                  {p = \chosen => LocatedActionOccurrence (OInsert selected parent chosen) global}
                  (trans (sym staticComponent) (cong fiberComponent
                    (justInjective (trans (sym (lookupReplacedFiber selected oldFiber next
                      (registry before) oldFound)) targetFound)))) born)
          LocalDelete => void (nothingIsNotJust
            (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq}
              selected (registry before))) targetFound))
```

### B6-1 full diagnostic

```text
2/2: Building DGamma.CP5RawClosingRankSpike (research/DGamma/CP5RawClosingRankSpike.idr)
Error: While processing right hand side of rawComponentBirthStep. Rewriting by ?y = action did not change type applyAction (OInsert selected parent component) before = Just (tag, afterState).

DGamma.CP5RawClosingRankSpike:171:46--171:73
 167 |                 (parent ** replace
 168 |                   {p = \chosen => LocatedActionOccurrence (OInsert selected parent chosen) global}
 169 |                   (cong fiberComponent (justInjective
 170 |                     (trans (sym (oInsertResultLookup nameEq keyEq selected parent component
 171 |                       before afterState tag (rewrite sym inserted in raw))) targetFound)))
                                                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^

```

### B6-2 full diagnostic

```text
2/2: Building DGamma.CP5RawClosingRankSpike (research/DGamma/CP5RawClosingRankSpike.idr)
Warning: Unreachable clause: case block in case block in case block in rawComponentBirthStep key value error world name initial finalState observed afterState nameEq action targetFound before global sourceBirth occurrence tag keyEq raw selected same ?postpone

DGamma.CP5RawClosingRankSpike:175:11--182:73
 175 |           LocalReplace {oldFiber} {oldFound} {staticComponent} next =>
 176 |             case sourceBirth selected oldFiber oldFound of
 177 |               (parent ** born) =>
 178 |                 (parent ** replace
 179 |                   {p = \chosen => LocatedActionOccurrence (OInsert selected parent chosen) global}
 180 |                   (trans (sym staticComponent) (cong fiberComponent

Warning: Unreachable clause: case block in case block in case block in rawComponentBirthStep key value error world name initial finalState observed afterState nameEq action targetFound before global sourceBirth occurrence tag keyEq raw selected same ?postpone

DGamma.CP5RawClosingRankSpike:183:11--185:57
 183 |           LocalDelete => void (nothingIsNotJust
 184 |             (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq}
 185 |               selected (registry before))) targetFound))

Error: While processing right hand side of rawComponentBirthStep. Can't solve constraint between: insertBinding (actionOwner ?_) ?next (?_ .registry) ?absent and ?_ .registry.

DGamma.CP5RawClosingRankSpike:163:11--163:34
 159 |             (applyActionLocalUpdate nameEq keyEq action before afterState tag raw)))) targetFound)
 160 |       Yes same => case same of
 161 |         Refl => case systemRegistryUpdate
 162 |           (applyActionLocalUpdate nameEq keyEq action before afterState tag raw) of
 163 |           LocalInsert next absent =>
                 ^^^^^^^^^^^^^^^^^^^^^^^

```

### B6-3 full diagnostic

```text
2/2: Building DGamma.CP5RawClosingRankSpike (research/DGamma/CP5RawClosingRankSpike.idr)
Error: While processing right hand side of rawComponentBirthStep. When unifying:
    applyAction action (MkSystemState beforeWorld sourceRegistry) = Just (tag, MkSystemState afterWorld targetRegistry)
and:
    applyAction action before = Just (tag, afterState)
Mismatch between: MkSystemState afterWorld targetRegistry and afterState.

DGamma.CP5RawClosingRankSpike:160:79--160:82
 156 |     case decEq @{nameEq} selected (actionOwner action) of
 157 |       No distinct => sourceBirth selected observed
 158 |         (trans (sym (registryLocalUpdateForeign nameEq selected (actionOwner action) distinct
 159 |           (registry before) (systemRegistryUpdate
 160 |             (applyActionLocalUpdate nameEq keyEq action before afterState tag raw)))) targetFound)
                                                                                     ^^^

```

## Unit B cap result — immutable cross-time rank seam PROVED, raw maximum OPEN

Supervisor ratified B6, then explicitly authorized the materially different
observed-update design B7–B15, with hard stop at another 3/3, the 15-unit cap,
or 01:50 UTC. That cure succeeded: B7 inducts on an EXPLICIT
RegistryLocalUpdate with explicit source/target registries and a generic
immutable-component predicate; B8 only passes the ACTUAL evaluator update to
it. No computed update is eliminated against a rigid state projection. B8
reuses the intended `rawComponentBirthStep` statement via this structural
producer, NOT a fourth B6 invocation. No second exhausted seam occurred.

| Unit | Declaration | Immediate commit | Fresh source check |
|---|---|---|---|
| B7 | `rawImmutableComponentUpdate` | `c5dcd9e` | PASS B7-1, 2026-09-07T00:32:16.209592+00:00–2026-09-07T00:32:18.257682+00:00, 0 KiB sampled |
| B8 | `rawComponentBirthStep` | `a291b86` | PASS B8-1, 2026-09-07T00:32:55.569461+00:00–2026-09-07T00:32:57.623284+00:00, 0 KiB sampled |
| B9 | `rawComponentBirthInvariant` | `c24f43d` | PASS B9-2, 2026-09-07T00:33:58.699108+00:00–2026-09-07T00:34:00.739899+00:00, 0 KiB sampled |
| B10 | `rawComponentBirthAtPrefix` | `1a46382` | PASS B10-1, 2026-09-07T00:34:56.775104+00:00–2026-09-07T00:34:58.808814+00:00, 0 KiB sampled |
| B11 | `uniqueRawComponentsAcrossPrefixes` | `f0a98d5` | PASS B11-1, 2026-09-07T00:35:43.412025+00:00–2026-09-07T00:35:45.470668+00:00, 0 KiB sampled |
| B12 | `rawProtocolRanksAtPrefix` | `7ec13b6` | PASS B12-1, 2026-09-07T00:37:38.114068+00:00–2026-09-07T00:37:40.146609+00:00, 0 KiB sampled |
| B13 | `uniqueRawRanksAcrossPrefixes` | `bba2819` | PASS B13-1, 2026-09-07T00:38:21.061512+00:00–2026-09-07T00:38:23.091695+00:00, 0 KiB sampled |
| B14 | `rawPrecedenceRankAcrossPrefixes` | `0dab1fc` | PASS B14-1, 2026-09-07T00:39:36.696713+00:00–2026-09-07T00:39:38.736110+00:00, 0 KiB sampled |
| B15 | `rawClosingEpisodeProtocolRank` | `44faf76` | PASS B15-1, 2026-09-07T00:40:42.796171+00:00–2026-09-07T00:42:02.149985+00:00, 4789184 KiB sampled |

B9-1 rejected use of the pre-case `head` alias after AlignedStep exposed the
actual Fired constructor. B9-2 uses that same explicit checked Fired value in
the structural occurrence embedding and passes. Every other B7–B15 first
attempt passed. B15's full DeletionChain check was detached/monitored (~79s);
its surviving-binder warning is inherited, not an error. No overlapping Idris
process or hidden signature change occurred. All retained additions have
explicit signatures and no with/let/as-pattern/escape. The rejected B6
as-pattern source appears ONLY in this audit, not retained code.

What is now PROVED, independently of the missing maximum:

1. Every present fiber at ANY aligned prefix from the empty initial registry
   has an authentic global O-Insert of its EXACT immutable component.
2. Uniqueness identifies those births; therefore the same raw name has the
   same COMPONENT and protocol RANK at ANY two reached prefix lookups. This
   allows multiple activations of that one birth; it does not assume one
   activation, key freshness, no removal, or final presence.
3. A raw precedence edge at a consumer's reached cut strictly increases the
   provider rank even when that provider rank was chosen at ANOTHER reached
   cut. This is genuine cross-time raw coherence, not a scoped negative cast.
4. Every actual located closing episode has a protocol-ranked actor at its
   OWN closedStartState, derived from the full replay bundle's actual
   provenance, alignment and emptiness, not only its final ranked registry.

CAP RESULT: PARTIAL / PARK at B15. `rawClosingMaximumUnderUniqueInsertions`
has NOT been stated as an unproved code declaration or proved. Remaining:
(a) give O7's finite erased occurrence list the rank projection from B15;
(b) use its ordinal-completeness field plus authenticated opening action
identity (B3) and cross-time rank coherence (B13) to transfer a finite maximum
bound to EVERY located closing episode; (c) choose a nonempty-list maximum
and contradict any raw outgoing precedence using B14, returning the selected
actor, that same genuine episode, and frozen NoDependentClosingEpisode.
No calling frozen deletionTheoremProof, no unsupported scoped-to-raw cast,
no strengthener supplied as the main theorem's output-shaped hypothesis.
THM73-PLAN.md is UNCHANGED: CP3 raw-premise satisfiability remains UNVERIFIED
until this exact existential has a compiler verdict. The mechanism that the
R174 recon needed is now real capital, but is not the selection theorem.

The next work is Unit C analysis-only, bounded to 40 minutes; no B16 attempt.
