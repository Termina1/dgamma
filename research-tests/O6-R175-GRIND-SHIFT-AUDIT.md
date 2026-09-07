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
