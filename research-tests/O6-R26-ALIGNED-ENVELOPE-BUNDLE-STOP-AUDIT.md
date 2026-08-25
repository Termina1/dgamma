# O6 revision-26 aligned-envelope and target-bundle stop audit

## 1. Scope and baseline recovery

Shift 36 resumed from `cp5-thm73-scoping@97e9b98` under the declaration-free
producer-envelope authorization.  After the interrupted process was revived,
the repository was checked before further work.  The last durable checkpoint
was `3ca744a` (`transport target bundle totality`); the only tracked dirty file
was `R23CorrectedInternalFixturePositive.idr`.  Its in-progress iterator/map
proof was checked, then given the prescribed three-attempt budget.  The
iterator transport and actual-map projection did not jointly elaborate.  The
probe was reverted to `3ca744a`, restoring a compiling tree, and the exact
projection failure was isolated as revision 26 rather than leaving a
half-broken positive.

The pre-existing untracked `paper/` directory was not touched.

## 2. Producer-owned aligned envelope

`r25AlignedDiamond` is a test-local
`CandidateAlignedLocalRelationalDiamond`.  Its base is exactly `r23Diamond`.
The aligned field is populated only with
`activationActivationConstructorMovedAlignment`, using:

- the same concrete early transition `r23EarlyBegin2`;
- the same checked singleton `r23EarlyBegin2Aligned`; and
- the exact moved transition returned by that concrete A/A producer, tied back
  by an authenticated heterogeneous equality.

No second A/A proof body and no caller-supplied moved alignment were introduced.
`r25BaseIsR23 = Refl` verifies the projection definitionally.

The replay transfer terms are definition-only aliases:

- `r25FirstFinishReplay = r24FirstFinishReplay`;
- `r25SecondFinishReplay = r24SecondFinishReplay`; and
- `r25FinalEndpoint = r24FinalEndpoint`.

They contain no rewrite, replacement, or reconstructed replay proof.  This
satisfies the hard definitional-projection condition.

`R25AlignedEnvelopeForgeryNegative` reproduces the independent-dictionary
attack.  It is rejected at the alignment index with:

```text
Mismatch between: storedRightKeyEq and keyEq.
```

Thus the successful concrete envelope cannot be generalized into detached
alignment capital.

## 3. Whole target bundle, strict field order

The whole target trace is constructed against
`baseDiamond r25AlignedDiamond`.  Fields close in declaration order as follows:

1. **`replayAligned` — closed.** `r25WholeAligned` appends the checked insert
   prefix, `movedPairAligned r25AlignedDiamond`, and the two singleton replay
   alignments.
2. **`replayDiscipline` — closed.** `r25WholeDiscipline` reconstructs each
   checked step.  The replayed L-Finish actions are normalized only by their
   authenticated `replayedActionExact` fields.
3. **`replayInitialWellFormed` — closed.** Reuses the exact common initial
   state theorem.
4. **`replayInitialEmpty` — closed.** Reuses the exact common empty registry.
5. **`replayFinalWellFormed` — closed.** Projected from `r25FinalEndpoint`.
6. **`replayQuiet` — closed.** A target-entry induction uses
   `controlEquivalentTargetHasSource` from revision 22 and the exact controls
   in `r25FinalEndpoint`.  Every target binding is looked up under the target
   registry's own uniqueness certificate, mapped to one of the two concrete
   source-active fibers, and shown quiet by its related Active/EmptyView
   control.  No domain list premise is supplied.
7. **`replayNoFailure` — closed.** A second target-entry induction uses
   revision 22's `targetEntryNotFailedFromSource`, source no-failure, and the
   same endpoint.  No detached no-failure/domain premise is used.
8. **`replayTotal` — closed.** `R23Key` is empty, so the recursively checked
   target trace is component-total.
9. **`replayIndependent` — hard stop.** See below.

No provenance, ranking, precedence, or support field is claimed after the
independence stop.

## 4. Independence stop: erased transition projection

The attempted constructive route first derived iterator-freedom for the moved
L-Begin steps and transported each replayed L-Finish iterator stage through its
per-step RAR to the source singleton.  It then tried to prove actual map
totality by transporting a canonical `ActualForwardGenerator` along the exact
checked transition projection.

The pointwise replay record owns:

```idris
replayedTransitionExact : replayedTransition =
  Fired r23NameEq r23KeyEq (LAdvance actor) LFinishTag replayedChecked
```

Revision 26 exports only the direct normalization
`r25CanonicalTransitionExact`, which is definitionally the producer's existing
proof and adds no premise.  Nevertheless, after transporting the generator,
Idris does not reduce its executable generator map back to
`partialEffectMap (replayedTransition replay)`.  The tracked negative
`R26FinishMapProjectionNegative.transportedFinishActualMapDoesNotReduce` fails
at:

```text
Can't solve constraint between:
  Fired ... (LAdvance ?_) LFinishTag (?_ .replayedChecked)
and:
  ?_ .replayedTransition.
```

A simpler projection rewrite had already failed to reduce the corresponding
`lookupFiber`/`fiberAdvanceRuntimeEffectMap`.  Three bounded attempts were made:
pattern refinement, explicit canonical transport, and an isolated generator
map equality.  The final failure is pinned instead of continuing unbounded
proof rewriting.

This is the same executable-dictionary/projection disease class as the earlier
alignment stop, but at a different producer boundary: the replay producer
proved target map identity internally while constructing its RAR, yet
`R24CheckedEmptyFinishReplay` does not retain that exact identity as a field.
The next safe delta is therefore a test-local corrected replay envelope that
retains producer-derived map identity (or a directly usable transported actual
generator-map equality).  It must be populated inside `r24ProduceEmptyFinish`,
not accepted from callers.  No frozen record change is authorized by this
audit.

## 5. Gate and estimate

The test-local aligned-diamond envelope is successful and supplies a direct
prototype/consumer proof for combined item A.  End-to-end bundle closure is not
reached, so the frozen A/B/C/D package remains **unissued**.  There is no
manifest or hole-forecast change: 21 research holes remain and the prepared
21→20→19 forecast remains suspended.

The remaining estimate stays at **26–44 shifts**.  Closing eight target fields
compensates for the newly concrete producer-retention work at independence.
The next gate must decide whether a test-local corrected finish-replay envelope
may retain the already-proved internal `targetMapIdentity`.  Frozen declarations,
O6 bodies, the manifest, production source, `dgamma.ipkg`, and CP3 remain
unchanged.
