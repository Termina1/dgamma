# O6 revision 35: provider equality, L-Begin closure, and target-query stop

## Scope

This checkpoint stays inside the private O6 research implementation. The frozen
`adjacentSwapSuffixSpike` declaration and body hole, sealed suffix spine,
opaque adjacent result, hole manifest, production `src/`, `dgamma.ipkg`, and
immutable CP3 theorem are unchanged. No caller-supplied target capital is added.

## Pointwise provider selection closes

`pointwiseProviderOfSame` implements the corrected four-branch construction.
The `Just` branches pass `leftSelected` and `rightSelected` directly to
`selectedProviderCandidate`. Their symmetric forms occur only in the two
absence contradictions, where a transported candidate reconstructs an
impossible `Just` scan against the branch's `Nothing` scan. When both scans
succeed, the transported left candidate and selected right candidate are
identified by the target registry's producer-owned pairwise provision
invariant.

This elaborated on the first fresh attempt; the conditional recurrence probe was
therefore not triggered.

Commit: `1b9e376` — transport provider selection pointwise.

`pointwiseResolveViewSame` lifts the per-key provider equality structurally to
exact dependency-view resolution. Its first attempt exposed only a lazy `case`
normalization mismatch; the second splits both provider scans explicitly,
rejects asymmetric branches using `pointwiseProviderOfSame`, and maps the
recursive equality through the common provider name.

Commit: `7fac4fc` — transport dependency resolution pointwise.

## L-Begin semantic head closes

`replayPointwiseBeginHead` is a complete generic semantic producer:

1. `beginSourceIngredientsPointwise` supplies the exact clean source owner and
   public plan view.
2. Pointwise control locates the related target owner.
3. `pointwiseResolveViewSame` reconstructs the exact target dependency view in
   an independently ordered registry.
4. Both owners are replaced by related `Reloading` states with the same
   component program and resolved view.
5. The producer constructs the target raw and checked transitions, preservation,
   source/target effect frames, next pointwise endpoint, definitionally identical
   effect map, singleton non-advance RAR, alignment, occurrences, and relative
   ordinal evidence.

The head used three bounded elaboration attempts: the first required the public
right-endpoint reification helper; the second required explicit dependent
`{name,key,value,world,error}` arguments for target resolution; the third
elaborated. No endpoint, target transition, map, view, RAR, occurrence, ordinal,
or target bundle is accepted from the caller.

Commit: `a67bc8f` — replay pointwise begin suffix heads.

Fully closed generic semantic heads are now O-Insert, O-Retire, and L-Begin.

## L-Divert/L-Leave target-query stop

Before duplicating the two large lifecycle bodies, a reusable target-query lemma
was attempted. The mathematical intent is to expose the shared component from
`FiberControlRelated`, use `pointwiseResolveViewSame`, and transport the current
view-mismatch guard needed by both L-Divert and L-Leave.

Three attempts were exhausted and all changes were reverted:

1. A direct equality over arbitrary `leftFiber`/`rightFiber` was rejected before
   pattern matching because the two `targetFiber` result types mention different
   component dependency indices.
2. A concrete same-component helper removed that dependent mismatch but used the
   wrong lifecycle type name (`FiberLifecycle` rather than indexed `Lifecycle`).
3. The corrected indexed helper reached the genuine remaining split:

```text
Can't solve constraint between:
  if rightRetired then Nothing else
    resolveView (dependencies (componentDependencies component))
      (registry right)
and:
  resolveView (dependencies (componentDependencies component))
    (registry right).
```

The next fresh attempt must accept the producer-owned
`leftRetired = rightRetired`, eliminate it, then branch on the shared Boolean.
The `True` branch identifies two `Nothing` queries directly; only the `False`
branch invokes `pointwiseResolveViewSame`. That helper must be established before
opening either full L-Divert or L-Leave producer. No partial helper or new hole
was retained.

L-Unload and L-Advance were not opened because the lighter target-query family
had exhausted its budget.

## O-Remove design for the next shift

The pinned R34 direct nested-`with` normalizer was not retried. A genuinely
different source representation is available for review:

1. Place a source observation beside the already elaborating
   `removeBindingObservation` section later in this module, where the private
   `removeSuccessView` constructor is demonstrably consumable by existing code.
2. Package its owner lookup, producer-owned composite removability guard,
   exact `sourceNoChild : hasChild actor source = False`, tag, and concrete
   delete endpoint in one indexed record. Do **not** reconstruct these fields
   from separate `with` proofs and do not store an independently oriented
   `childView`.
3. The future head destructs that observation directly, transports
   `sourceNoChild` with `pointwiseNoChildPreserved`, transports the related
   owner and guard fields, constructs the target delete, and uses
   `removeEffectFrameRelated` for the empty-table effect boundary.
4. Keep the observation and head in the later elaboration zone rather than
   moving or widening the frozen suffix replayer interface.

This changes the source proof representation, not its premises or outputs, and
avoids the exact R34 `sym childView` term. Per authorization, it is design-only
in revision 35; no ORemove retry budget was consumed.

## Safe boundary and estimate

One of six open semantic heads closed, leaving O-Remove, L-Divert, L-Leave,
L-Unload, and L-Advance. Whole-suffix RAR/ordinal composition and final adjacent
assembly remain gated. Holes remain **20**, split **6/4/8/1/1**.

The O6 band remains **18–34 shifts** as required for this checkpoint. L-Begin
and provider resolution materially reduce the remaining proof body, but the
unopened heavy L-Unload/L-Advance families and the two bounded source/target
representation stops remain fully charged.
