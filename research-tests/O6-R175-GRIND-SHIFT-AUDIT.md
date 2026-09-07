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

## Initial Unit B plan — superseded by the cap result below

At start, not started. The target is the existential `rawClosingMaximumUnderUniqueInsertions`
from R174 reconnaissance, via immutable cross-time rank coherence. It does not
cast an arbitrary scoped maximum to raw maximality or call the frozen deletion
proof. No satisfiability discharge is claimed before its actual source checks.

## Initial Unit C plan — superseded by the completed analysis below

At start, not started; no signature edits authorized.

## Initial status

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

## Unit C — exact uniqueness-threading plan (ANALYSIS ONLY)

Window began **2026-09-07 00:43:47 UTC**, hard stop 01:23:47 UTC. References
below are to source at `22799e9` (B15 source already committed in `44faf76`).
No signature, body, record, fixture, or suite entry is revised by this plan.
No O19 or O21 withdrawal proof is attempted. All 4+1 holes stay inherited.

### C1. Where the currently available evidence stops

- `research-tests/DGamma/R8FullPipeline.idr:67–153` already accepts quantity-0
  `leftUnique/rightUnique` for the TWO ORIGINAL traces (83–84). At 103/130 it
  sends their ACTUAL reduction transports to O17. At 115–117 and 142–144 it
  assembles left/right capitals but drops freshness. Calls to O19/O20/O21 at
  145–152 cannot recover that fact from their arguments.
- `R16ConfluenceTheoremAssemblyPositive.idr:78–119` already accepts both original
  uniqueness inputs and passes them to R8. It is explicitly a CONDITIONAL
  research assembly, not the unchanged production CP3 theorem.
- `CanonicalSort:4809–4840` IndependentCanonicalSchedule stores the exact
  premises/reduction/ordering/sorted/accounting/schedule/classification chain,
  but NO freshness. `assembleIndependentCanonicalSchedule:4935–4966` and
  `independentCanonicalScheduleSpike:4972–4995` accept arbitrary already-supplied
  sorted capital. An inhabitant is NOT necessarily the output of O17.
- `SortedClosingFreeTrace:117–166` owns `sortingAdjacentDerivation:130`, but
  neither it nor its ReplayInvariantBundle contains original freshness.
  `ReplayInvariantBundle` (LocalDiamond:2415–2445) likewise has no such field.
- `RenamingComposition:1869–1911` AcceptedDeletionScannerCapital owns the EXACT
  accepted scanner and the actual left/right withdrawal membership and original
  closing classifications. Its producer at 1918–1960 does NOT use uniqueness.
  Neither the scanner nor generation-name bijections manufacture global raw
  insertion freshness. Keep this general scanner result general.

### C2. Recommended minimal future surface change (requires owner approval)

Thread the TWO ORIGINAL quantity-0 hypotheses explicitly beside the SAME
left/right capitals at consumers that need them. Do NOT strengthen all
IndependentCanonicalSchedule inhabitants, silently infer freshness from a
sorting call, or store freely chosen target-uniqueness/registration maps.
The intended added telescope fragments (documentation, not declarations) are:

- `0 leftUnique : UniqueRawNameInsertions ... nameEq keyEq leftTrace`
- `0 rightUnique : UniqueRawNameInsertions ... nameEq keyEq rightTrace`

Place them immediately after the two capital arguments. Their trace indices
already provide the required authentication; they need not be over-indexed by
proof identity or by an arbitrary ordering/accounting constructor. A proof of
original freshness is legitimately reusable for two capitals of THAT SAME
original trace, but never for another trace merely sharing an endpoint.
All pre-existing output types, exact schedule/occurrence indices, and sealed
constructors remain unchanged. Do not add a parallel legacy theorem solely to
preserve the old stronger statement; replace only the owner-approved research
consumer signatures, leaving genuinely more general scanner/assembly lemmas
untouched for their separate purpose.

| Exact surface | Planned evidence / actual consumer | What it does NOT fix |
|---|---|---|
| CrossTrace:970–986 `canonicalSupportOrdersMatchSpike` | Both original uniques, next to its two capitals; use original/canonical current-birth coherence when proving the two support-TRUTH directions. R8:145 calls it. | Support fixed-point/path transfer through withdrawn intermediates is still a separate theorem. |
| CrossTrace:1048–1067 `selectOperationalCanonicalPermutationSpike` | Both original uniques; derive the canonical-left initial unique and then the unique of each ACTUAL reached operational target. R8:147 calls it. | Membership is not list equality; finite linear-extension selection and safe enabled swaps remain open. |
| CrossTrace:699–714 `operationalAdjacentBlockSwapSpike` | If its future proof uses freshness, add ONE quantity-0 UniqueRawNameInsertions for its exact `sourceTrace`; propagate through each authenticated local crossing. No concrete call site exists outside its currently-holed declaration; the future selector will be its consumer. | Current AdjacentActorSwapSafety:114–139 lacks consumer early applicability/support incomparability. Unique names do not repair O19's provider/consumer guard. O19 body remains forbidden until its separate owner gate. |
| CrossTrace:1304–1325 `canonicalSchedulesConvergeSpike` | Both original uniques if needed to construct the exact four-clause replay→right bridge; R8:149 calls it. Canonical/replayed uniques are derived, not new arbitrary output inputs. | No automatic ambient/table/control/birth agreement. The operational permutation is already an input and cannot be fabricated from freshness. |
| RenamingComposition:2693–2723 `replayedCanonicalToOriginalEndpointSpike` | Both original uniques alongside EXACT capitals and existing accepted scanner; consume only at authenticated current-birth identity branches. Sole code caller is CrossTrace:1354. | No withdrawal branch is discharged merely by raw-name membership; actual absent/present and full vestigial evidence remain required. |
| CrossTrace:1328–1362 `originalEndpointsConvergeSpike` | Both original uniques; forward them to O21. R8:151 is the genuine caller; R6MixedScheduleNegative exercises its capital index. | Freshness must not detach convergence from the actual left/right capitals, replayed trace or occurrence relation. |

The purely sufficient assemblers need NO new assumptions:
`canonicalSupportOrdersFromTruth:939–967`, `canonicalConvergenceFromBridge:1270–1299`,
`confluenceResultFromCanonicalCapital:1367+`, `canonicalActorBlockDecomposition:990–1002`,
`acceptedDeletionScannerCapitalSpike`, and the fixed-bijection
ReplayedCanonicalEndpointBridge:1753–1810 / CanonicalConvergenceResult:1241–1268.
Do not change their records just to thread a fact an outer producer can carry.
The general SameRawNameScannerRegression:2054–2145 and concrete discard-word
fixtures:2188+ intentionally test scanner generation identity under reuse;
they are not asserted to inhabit the freshness-restricted O21 telescope.

### C3. Exact derivation chain and missing semantic bridge

A small research-only companion MODULE (not a stronger capital record) should
provide these erased projections from existing sealed data:

1. **Original → actual reduced:** existing
   `CP5UniqueRawNameDeletion.uniqueInsertionsAfterReduction:217–227`, using
   `capitalReduction capital` and originalUnique. This is an injective
   all-action deletion-source-position argument, not a generation cast.
2. **Reduced → actual canonical:** existing
   `CanonicalSort.uniqueInsertionsAfterFiniteDerivation:2338–2350` with
   `sortingAdjacentDerivation (capitalSorted capital)`. Reindex through the
   existing `capitalCanonicalScheduleExact`/producer equation to reach
   `canonicalTrace (canonicalSchedule capital)`. One explicit observed-capital
   eliminator can mirror canonicalReplayPremises (4900–4905); never copy a
   caller-selected correspondence. Import CP5UniqueRawNameDeletion in the new
   module rather than creating a CanonicalSort↔deletion import cycle.
3. **One operational block result:** CrossTrace
   `wholeBlockFiniteDerivation:632–638 (blockSwapWholeDerivation step)` feeds
   the SAME finite-derivation uniqueness transport. Its output is indexed by
   `blockSwapTrace step`, not an asserted renamed/canonical endpoint.
4. **Whole operational permutation:** structural induction on
   `OperationalActorPermutation:721–757`: Done preserves sourceUnique; Step
   derives the actual block target unique as in (3), then passes it to the
   exact stored `rest`. No data/signature change to OperationalActorPermutation
   or OperationalAdjacentBlockSwap:645–672 is necessary for this projection.
   A bare RAR or ActionRegistrationReplayCorrespondence is INSUFFICIENT:
   the authenticated injective occurrence fold is essential.
5. **O21's actual identity need:** correlate the accepted scanner's precise
   current generation and each original endpoint lookup with an ORIGINAL
   located birth. B10 now gives a real birth of the present component, and
   B11/B13 prove immutable component/rank coherence, but they do NOT identify
   an arbitrary scanner's current birth ordinal. That scanner/lookup
   authentication is still a proof obligation. Only AFTER both births are
   authenticated may `uniqueInsertionPosition` identify their ordinal and
   exclude the specific later-birth/same-name escape. Preserve the accepted
   generation bijection and both original action-origin maps throughout.

Original uniques are independent side assumptions. SameOrchestrationModuloGenerated
is not a freshness transfer theorem (discarded births differ between sides).
A rename likewise needs an actual injective action/name transport theorem;
no name-bijection slogan or effect equivalence licenses a trace cast.

### C4. Withdrawal branch boundaries and non-goals

- **Outside both withdrawn sets:** existing
  `replayedCanonicalOuterControlOutsideSpike:2578–2620`, ambient:2622–2639,
  tables:2641–2683 remain the available composition capital. R147's
  constructor-owned `expectedBridgeBijection:1735–1744` already removed the
  free-bijection obstruction; no freshness theorem is needed merely to rename
  that fixed value.
- **Left-only / right-only / both withdrawn:** first split the ACTUAL endpoint
  lookup. Absence needs its actual equation. Presence needs the accepted
  scanner's exact current generation, classified original birth, retirement,
  clean inactive lifecycle, empty installed keys, no children, and unsupportedness
  required by frozen VestigialEndpointGeneration (CP3:2851–2878).
  CurrentEndpointRenaming (CP3:2977–3004) still offers either that full vestigial
  package or exact mapped current birth; exclude a mapped case only by a
  contradiction at THAT authenticated birth. Do not introduce a global
  withdrawal-name negation/G31 substitute or infer absence from withdrawal.
- R175 B11–B14 make the immutable raw-name/component/rank argument available,
  not the endpoint table/retirement/no-children facts. They do not establish
  support correspondence, canonical existence, or O21 by themselves.
- A8's different names/same declared key remains independent. No global key
  freshness or “retired therefore no longer reserves provisions” assumption.
  No root-placement, guard, production CP3, O19 body or O21 branch revision.

### C5. Ripple estimate (source-counted, not a proof-time promise)

**Recommended explicit-parameter route:** six research producer/forwarder
signatures (five CrossTrace, one RenamingComposition), one R8 pipeline body
already holding both assumptions, and about three new structural uniqueness
projections (canonical, block, permutation; the block can be inlined if useful).
R16's existing public inputs and call to R8 need NO new parameters. All output
record constructors, seven existing capital eliminators, schedule/accounting
assemblers, accepted scanner producer, and general same-name scanner fixtures
stay unchanged. Expected mechanical work: roughly **10–14 declarations in
4–7 existing/new research/test modules**, plus **6–8 focused fixture units**;
semantic O19/O21 proofs are explicitly NOT included in that estimate.

Repository direct negative caller updates are precisely:
`R6OldPollutionNegative:41` and `R6MixedScheduleNegative:33`. Give these fixtures
legitimate hypothetical left/right original uniques so they still reach their
ORIGINAL intended mismatch (pure certificate vs operational package; wrong
capital) rather than passing via missing-argument/arity errors. R8's four calls
at 145–152 and CrossTrace's one O21 call at 1354 are the direct threading sites.
No matching producer call occurs in src/ or dgamma.ipkg. Import-based
rechecks ripple through CanonicalSort/Renaming/CrossTrace and their downstream
fixtures, but not into production source changes.

**Alternative not recommended without explicit scope decision:** adding an
original-unique field to IndependentCanonicalSchedule would strengthen every
capital, require both assembly signatures plus the constructor and all six
CanonicalSort constructor-pattern eliminators (4867/4880/4894/4905/4915/4929),
CrossTrace's block projection (998), the direct R11TreeOnlyCapitalCloneNegative
constructor and the R11 assembly positive/negative and R4VestigialSimultaneous
wrappers. It also changes the meaning of the general reuse/scanner interfaces.
That wider ripple buys no theorem that cannot be stated with actual original
uniqueness beside an existing exact capital. This is a semantic surface change,
not a harmless field fill or backward-compatibility patch.

### C6. Negative/positive fixture plan (NOT implemented this shift)

Each compiler-negative fixture must fail at its named target boundary and
required diagnostic, not an unrelated missing argument, import or parse error.

| Planned check | Required evidence boundary |
|---|---|
| Bare-capital freshness projection negative | An arbitrary IndependentCanonicalSchedule / public CanonicalSchedule / ReplayInvariantBundle alone cannot produce original UniqueRawNameInsertions. Do not fill it with a new hole or assume the desired unique. |
| Wrong-original trace negative | Feed an actual uniqueness witness for another trace (even same endpoints) at the revised consumer; expected trace-index mismatch. |
| Reduced-to-original negative | Do not reverse the proved reduction transport: deletion may erase one birth of a reused raw name. Use a statement-boundary mismatch unless a full concrete reduction is actually constructed; no fake full countermodel claim. |
| Unsealed-origin negative | Attempt to derive replay-target freshness from a bare RAR/all-action map without authenticated ordinal injectivity; must be rejected at the missing sealed source-position boundary. |
| Reused-name exclusion positive | Reuse R173UniqueRawNameInsertionsFixtures.r173ReuseRejectsUniqueInsertions (actual births at 2 and 5); derive contradiction from authentic distinct births, not generation-name equality alone. |
| Different-names/same-key survival positive | Retain R174O17ProvisionCollisionUnique's actual original freshness. It must NOT be excluded by the new input. No Q9 retry or full-input A8 restatement. |
| Existing purity/capital attacks | Update R6OldPollutionNegative and R6MixedScheduleNegative as above; retain exact old intended diagnostic. R8WrongTraceBridgeNegative / R8WrongOccurrenceBridgeNegative / R11BridgeWrongGenerationNegative must still reject their actual trace/occurrence/generation mismatch. |
| Successful threading positive | R8/R16 conditional assembly passes with its existing explicit original uniques; canonical and operational transports consume the actual sealed derivation, not copied outputs. Keep R4ScannerProducerConsumers and the general scanner-reuse fixtures valid WITHOUT global freshness. |

Validation for any later approved change: one new declaration per compiler
invocation, each ≤3 attempts; seeded source checks only; existing protected
LocalDiamond/O6 hashes; the source-counted 5 research / 57 positive / 50 diagnostic-negative
suite in run-r11-suite.sh if the owner requests the full historical suite,
plus all new freshness-specific fixtures; seeded production cache 207/207;
CP3/production hashes and holes audited. This plan does not preauthorize those
future edits, a legacy stronger theorem, or any blocked semantic proof body.

Unit C finished **2026-09-07 00:49:38 UTC**, under 40 minutes. Analysis/documentation only; ZERO compiler attempts or signature edits. The script's stale 5+54 comment was not trusted: its actual arrays contain 5 spikes, 57 positives, 50 negatives (62 successful research markers in fresh mode). No aggregate suite was run or claimed.

## Final validation and frozen boundary

- Toolchain reconfirmed: Idris 2 **0.8.0**. All changed Idris modules retain
  `%default total`; no with/let/as-pattern/nonlinear-pattern/proof escape in
  retained additions. No production, package, CP3, O17/O19/O21 body, root-phase,
  Q9, G31, archived-C58, or adversarial-review edit.
- Final retained DeletionChain rebuilt on B15-1 (00:40:42–00:42:02), followed
  by NO further Idris source change. Whole WorkMeasure last source check D10-1;
  whole RawClosingRank last source check B14-1; abstract fixture D1-4.
- Final seeded package PASS **00:50:07–00:50:24 UTC**, sampled RSS 219,904 KiB.
  This is an actual `idris2 --build dgamma.ipkg`, NOT a cold rebuild. All
  **207/207 production TTC seeds** are preserved.
- Final CanonicalSort fresh source check PASS **00:50:34–00:51:29 UTC**, sampled
  RSS 18,199,824 KiB; actual Building marker. Benign existing-variable `sorted`
  shadowing warning from the new Data.List import is recorded, not suppressed.
- Final R8FullPipeline fresh source check PASS **00:51:35–00:53:15 UTC**, sampled
  RSS 36,697,408 KiB; actual Building marker. Final R16 conditional assembly
  fresh source check PASS **00:53:20–00:53:23 UTC**, actual Building marker.
  Both remain conditional through late-capital assumptions and six open holes.
- Committed `O6-R175-COMPILER-LEDGER.json`: **49 serialized checks**, **36 clean
  passes**, **13 diagnostic rejections**, **0 engineering interrupts**. Of the
  passes, 32 are immediate committed declaration units and 4 are final checks
  with no new declaration. Zero RSS samples on fast units mean no sampled
  nonzero process before completion, not zero memory use.
- D1's three rejections were stopped/reverted/gated; EXACT spelling-only D1-4
  was expressly supervisor-granted. B6's three rejections were stopped/reverted/
  gated; B7/B8's structurally different explicit-update cure was expressly
  authorized and passed. No self-reset or other fourth attempt occurred.
- LocalDiamond SOURCE delta vs starting HEAD and vs `8b68e37`: **EMPTY**.
  Protected LocalDiamond TTC remains present, 125,344,796 bytes, mtime
  **2026-09-06 12:04:30 UTC**, before this shift; it was never deleted/rebuilt.
  CrossTrace and RenamingComposition SOURCE deltas: **EMPTY**. DeletionChain
  delta: only one new import + B15 (38 added lines, zero removed). CanonicalSort
  delta: 205 added lines, zero removed. THM73-PLAN.md unchanged.
- No aggregate R11 suite or independent reviewer pass is claimed. The supervisor
  owns review fanout. C's future-fixture list is a plan, not test verdicts.
- The machine-readable frozen snapshot will accompany this audit in
  `O6-R175-FINAL-VALIDATION.json`, including exact protected hashes, six-hole
  names, cache census, additive-only source checks, allowed untracked files and
  no compiler orphan.

## Status

| Ordered assignment item | Status at gate | Checked capital / exact remainder |
|---|---|---|
| Selected Iter/Finish early applicability | OPEN | R174 selected non-Begin provenance remains; no new early-applicability producer this shift. |
| Four orientation producers / sealed adjacent results | PARTIAL | A/O ACTUAL selected generated-insertion diamond, exact external evidence, sealed O6 result and reached update proved in A1–A6. A/A, O/A, O/O still lack the requested full selected early/execution integrations. |
| Structural BlockBefore | OPEN | No numeric-range-to-structural connector added. |
| Whole-worklist decreasing measure | PARTIAL, authorized cap PARK | Abstract old-policy cycle checked D1; D2–D10 prove exact adjacent selection + whole-word drop simultaneously; D11–D12 define the actual fixed-order whole-worklist barrier measure. Missing checked-pair location, orientation applicability and rank-segment preservation across sealed suffix. |
| Exact registration fold alignment | OPEN | No replacement by a caller-supplied map or output-shaped law. |
| Raw closing maximum under uniqueness | PARTIAL, authorized cap PARK | Authentic prefix births, immutable cross-time components/ranks, cross-time raw precedence increase and ranked genuine closings proved B1–B15 (B6 reverted). O7 finite rank maximum + completeness transfer + raw existential assembly remain open. CP3 satisfiability NOT reclassified. |
| CrossTrace/O21 uniqueness-threading plan | COMPLETE (analysis) | Exact six future surfaces, sealed transport chain, unchanged general consumers, ripple estimate, diagnostic-negative/positive fixture plan committed; ZERO signature/body edits. |

The six inherited holes remain **6 = 1/4/0/0/1** in CanonicalSort / CrossTrace /
DeletionChain / LocalDiamond / RenamingComposition. No new hole or unproved
postulate was added, and no conditional result is called the paper's full
confluence theorem. The abstract selector cycle is NOT a full O17 countermodel.
A8 remains an owner-scoped canonical-form/guard issue, not solved by raw
freshness or by the new maximum capital. No attempt to restart the capped
seams is authorized by unused wall time.

**Next after owner approval:** finish the ranked-segment→authentic sealed O17
progress bridge; separately finish finite O7 closing-rank maximum using the
now-proved cross-time coherence; apply C's explicit-original-uniqueness
threading only after its surface gate. Root placement and O19 safety/O21
withdrawal proofs remain separately paused. Final supervisor gate at the
committed validated boundary; no further Idris declaration proposed this shift.

Final automated frozen snapshot PASS **2026-09-07 00:56:35 UTC** at verified
HEAD `ad6616d`; committed alongside this note as
`research-tests/O6-R175-FINAL-VALIDATION.json`. The subsequent commit changes
ONLY these reporting artifacts, not Idris source or TTCs. The O6 full/statement
hashes match their protected values; CP3 blob matches; production/package,
LocalDiamond/CrossTrace/RenamingComposition, O17 declaration and THM73-PLAN are
unchanged; new existing-module deltas are additive; all 207 seeds are present;
all 49 compiler checks serialized; no compiler or staged/tracked change at
snapshot. Only `paper/` and the frozen adversarial review remain untracked.
