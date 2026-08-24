# O5 dictionary-coherence audit-lite

Audit date: 2026-08-24  
Audit base: `cp5-thm73-scoping@117f17978fb79a611540bc00c018dc3ab1f1d678`  
Scope: the still-open O/O local-diamond body
`orchestrationOrchestrationDiamondSpike_rhs`. Revision-14 is closed and accepted;
this audit does not change either reviewed O3/O4 interface, any declaration,
frozen manifest entry, hole, production file, or package file.

## Verdict and gate request

O5 independently reaches the executable-dictionary boundary already repaired for
O3/O4. Revision 14 expressly left O/O unchanged, so proof work stops before any
O5 declaration change.

The narrow producer-authenticated premise specification is to add to
`orchestrationOrchestrationDiamondSpike` exactly:

```idris
(0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
  (MoreTransitions left (MoreTransitions right NoTransitions))) ->
```

and, after the existing `safety` argument,

```idris
(0 earlyRightAligned : AlignedTransitions name key world error value
  nameEq keyEq (MoreTransitions (earlyRight safety) NoTransitions)) ->
```

The source premise authenticates both original nodes. The singleton premise
authenticates the exact `earlyRight` already sealed inside
`OrchestrationSwapSafety`; its dependent index prevents a caller from supplying
an unrelated transition. No raw dictionary equality, caller-selected action,
tag, checked equation, evaluator output, effect, control, or endpoint is added.

**Gate request:** authorize only these two erased premise occurrences for O5,
followed by an O5-specific positive producer probe and independent-dictionary
negative, and update exactly the O5 manifest signature. O3/O4 and
`OrchestrationSwapSafety` itself remain byte-for-byte unchanged.

## 1. Reproduced blocker

`Transition.Fired` stores unrestricted executable `DecEq` dictionaries. Neither
`PaperOrchestrationStep` nor the registration/generation fields of
`OrchestrationSwapSafety` constrain those stored values to the separately
supplied outer `nameEq`/`keyEq`.

The total diagnostic probe `/tmp/O5DictionaryAudit.idr` projected the checked
equation of the exact `earlyRight safety` under the outer dictionaries:

```idris
0 safetyEarlyOuterChecked :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (safety : OrchestrationSwapSafety name key world error value protocol
    nameEq keyEq left right) ->
  checkedApplyAction @{nameEq} @{keyEq}
    (transitionAction (earlyRight safety)) first =
  Just (transitionTag (earlyRight safety), earlyRightFinal safety)
safetyEarlyOuterChecked nameEq keyEq protocol left right safety =
  case earlyRight safety of
    Fired storedNameEq storedKeyEq action tag checked => checked
```

Idris 2 0.8.0 rejects `checked` with:

```text
Mismatch between: storedKeyEq and keyEq.
```

The same mismatch occurs when projecting `left` or `right`. O5 needs all three
outer-dictionary equations immediately: it must invert both source
orchestrations, reuse the checked early-right rule, reconstruct moved-left, and
relate outer-dictionary effects, controls, and well-formedness. The safety
record's action/tag equalities do not identify executable dictionaries.

## 2. Consumer trace

O5 will be selected only inside the adjacent-swap/sorting pipeline. Every
genuine current source trace already carries outer-dictionary authority:

- `ReplayInvariantBundle.replayAligned` aligns the exact replay trace;
- exact prefix/pair/suffix decomposition plus immutable `alignedAppendSplit`
  extracts the two-node source premise;
- `AdjacentActorSwapSafety.sourcePremises` owns that exact bundle at the O6
  whole-block boundary;
- O17 recursion receives `replayAligned (swappedPremises result)`; and
- O19 current, recursive, initial sealed, and target sealed bundles retain the
  same indexed authority.

The accepted revision-14 review at `review-cp5-r14-scoped.md`, sections 3 and 5,
independently typechecked these exact O6/O17/O19 producer sites and confirmed
that pair alignment is orientation-independent. O/O therefore requires no new
source capital beyond what the genuine consumer already owns.

`OrchestrationSwapSafety.earlyRight` is operational applicability, not an
arbitrary source occurrence. A genuine O5 producer evaluates the right
orchestration under `nameEq`/`keyEq`, constructs

```idris
early = Fired nameEq keyEq action tag earlyChecked
```

and definitionally supplies

```idris
AlignedStep action tag earlyChecked NoTransitions AlignedEnd
```

for that exact indexed transition. This is the same producer shape independently
checked by the revision-14 review for O/A. The proposed singleton premise merely
retains its authority at the O5 consumer boundary.

## 3. Premise minimality

Source alignment alone says nothing about the independently stored
`earlyRight safety`. Early singleton alignment alone says nothing about the two
source transitions. Both are therefore consumer-needed. Conversely, six
`DecEq` equalities, raw checked equations, or moved endpoints would be wider and
less source-authenticated.

Adding fields to `OrchestrationSwapSafety` would also work, but is a wider public
record-interface change and has no current concrete constructor producer.
Keeping the exact alignment as erased theorem premises changes only the open O5
interface and leaves the reviewed provenance package unchanged. The exact
indices still prevent detached evidence.

No operational O/O commutation claim is made by this audit. After a gate, the
proof must still handle all nine OInsert/ORetire/ORemove rule pairs, freshness,
generation/licensing exclusions, checked reconstruction, effects, ordered
controls, and endpoint well-formedness.

## Status

- Revision-14 report read and accepted; N1 exclusions remain untouched.
- Reviewed O3/O4 signatures and `OrchestrationSwapSafety`: unchanged.
- O5 declaration and manifest: unchanged.
- O5 hole: unchanged.
- Production `src/`, `dgamma.ipkg`, and immutable CP3: unchanged.
- Proof work: stopped pending an explicit O5 interface gate.
