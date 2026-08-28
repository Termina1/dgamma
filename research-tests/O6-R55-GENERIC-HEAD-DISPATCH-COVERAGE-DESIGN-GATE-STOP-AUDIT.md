# O6 revision 55: tag helpers closed; generic dispatcher coverage design gate

## Scope

Shift #63 (overall #117) resumed at revision-54 HEAD `1ce1346`. The three
supervisor-authorized quantity-0 tag helpers each closed on their first attempt
and were committed independently before any dispatcher work. The subsequent
private eight-clause aligned dispatcher exhausted its fresh three-attempt budget
at Idris coverage checking. All dispatcher and local L-Begin helper code was
reverted while preserving the three committed helpers.

No whole-suffix composition, final adjacent assembly, frozen signature,
production file, or research hole changed.

## Retained helper commits

### `d5d2c5f` — `pointwiseDivertTag`

The helper eliminates `foreignDivertPlanView` entirely inside a quantity-0
function and returns only `tag = LDivertTag`. Its located owner, lookup proof,
and dependent source plan view cannot escape. Source module and R16 both passed.

### `80d3094` — `pointwiseLeaveTag`

The helper eliminates `foreignLeavePlanView`, then consumes
`foreignLeaveReplayData`, returning only `tag = LLeaveTag`. No new import was
needed and no lifecycle replay witness crosses the boundary. Source module and
R16 both passed.

### `935a062` — `pointwiseUnloadTag`

The helper constructs and immediately consumes the retained
`pointwiseUnloadSourceObservation`, projecting only `tag = LUnloadTag`. The
complete table, accumulator, reliance, and endpoint observation remains sealed
at its producer. Source module and R16 both passed.

All three helpers compiled on attempt 1 and are independently useful for any
future aligned or joint-record dispatcher representation.

## Dispatcher attempt 1: bodies clear, coverage rejects aligned-only dispatch

The eight clauses used the accepted revision-53 representation:

- source step wildcarded;
- dispatch on `AlignedStep action tag checked NoTransitions AlignedEnd`;
- all raw and tag equalities parenthesized;
- L-Begin used its internal lookup rewrite;
- Divert/Leave/Unload used the three new erased helpers;
- L-Advance delegated directly.

Every clause body elaborated. Idris then rejected totality with a very large
missing-case set. The generated cases began at L-Advance and repeated
Divert/Leave/Unload across rule-tag and dictionary shapes. Thus the tag-helper
wall was fully cleared, but the coverage checker would not use the
`AlignedTransitions` index alone to refine the wildcard source transition.

## Dispatcher attempt 2: explicit source action, wildcard aligned fields

Each clause additionally matched the source step as:

```idris
Fired _ _ action tag checked
```

and matched its aligned singleton with wildcard action/tag/check fields. This
made the action split syntactically visible without equating independently
stored dictionaries. Idris still generated the same non-covering family.

## Dispatcher attempt 3: source-owned dictionaries, formal dictionaries hidden

To avoid even an apparent duplicate dictionary match, the explicit `nameEq` and
`keyEq` function arguments were wildcarded and each source `Fired` pattern bound
its own dictionaries:

```idris
replayPointwiseAlignedHead _ _
  (Fired nameEq keyEq action tag checked)
  (AlignedStep _ _ _ NoTransitions AlignedEnd) ...
```

The bodies again elaborated, but coverage remained unchanged. This confirms the
obstruction is not tag production, parser syntax, or a semantic head. Idris's
coverage checker does not treat the aligned singleton as sufficient to discharge
all independently stored `DecEq`/checked-proof shapes after the action split.
No equality of arbitrary dictionaries was introduced or assumed.

## Reversion and design gate

The full dispatcher and its local L-Begin helper were reverted after attempt 3.
There is no partial dispatcher or metavariable. The three separately committed
tag helpers remain.

Per the accepted revision-54 ruling, the next examination requires a design gate:
the retained spine may need to consume a per-action joint record that packages
one source `Fired`, its exact `AlignedStep` singleton, and the resulting closed
head together, so coverage performs only one dependent elimination rather than
two correlated arguments. Such a record must preserve the existing constraints:

- no dictionary identity or UIP;
- no detached checked transition, endpoint, RAR, occurrence, ordinal, map, or
  alignment capital;
- eight producer clauses, each calling its already closed head;
- no widened caller interface;
- no change to `PointwiseRelationalHeadReplayer`, the frozen adjacent theorem, or
  any public result boundary without a separate gate.

No joint record has been proposed or retained in this revision.

## Status

- fixed-tag helpers: **3/3 closed and committed**;
- semantic head families: **8/8 retained**;
- generic all-action dispatcher: **STOP; fully reverted**;
- generic spine recursion: **typed, not instantiated**;
- whole-suffix RAR/ordinal composition: **unopened**;
- final adjacent-result assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- estimate: **3–15 shifts held pending the required joint-record design gate**.
