# O6 revision 36: remove observation and target-query closure

## Scope

All retained work remains private to the research O6 body. The frozen
`adjacentSwapSuffixSpike` declaration/body hole, sealed suffix spine, opaque
adjacent result, manifest, production `src/`, package, and immutable CP3 theorem
are unchanged. No output-shaped premise or caller-selected target evidence was
introduced.

## Approved O-Remove source representation

The reviewed representation change now elaborates. The indexed
`PointwiseRemoveSourceObservation` record lives beside the existing
`removeBindingObservation` section in the later elaboration zone and seals:

- the exact source owner;
- its exact source lookup;
- the producer-owned composite removability guard;
- the exact `hasChild actor source = False` proof delivered by
  `removeSuccessView`;
- the exact O-Remove tag; and
- the concrete delete endpoint.

`pointwiseRemoveSourceObservation` constructs the record by destructing one
`removeSuccessView`; it never constructs or symmetrically reorients an
independent `childView`. It elaborated on the first attempt.

Commit: `82ff231` — package pointwise remove source observation.

The R34 orientation diagnostic did **not** reappear. The earlier wall is therefore
confirmed as representational rather than semantic at this checkpoint, and the
conditional new expected-failure probe was not triggered.

## Bounded O-Remove head stop

The full head then received its remaining bounded foundation attempts. Two
pieces elaborated together during attempts two/three before the uncommitted block
was reverted:

1. lifecycle inactivity and the composite removal guard transport through
   `FiberControlRelated` plus exact source/target childlessness;
2. pointwise controls after deleting the same actor from independently ordered
   registries.

The second piece stopped at the self-delete lookup normalization. The local
self-delete lemma retained an independently inferred dictionary inside its
result, and the apparent direct replacement is private:

```text
Undefined name lookupDeleteSelf.
Did you mean ... DGamma.CP4Support.lookupDeleteSelf (not exported)?
```

The preceding attempt's smaller diagnostic was:

```text
Rewriting by lookupFiber actor (deleteBinding actor ?nameEq) = Nothing
  did not change type
FiberControlMaybeRelated
  (lookupBinding actor (deleteBinding actor leftRegistry))
  (lookupBinding actor (deleteBinding actor rightRegistry)).
```

The source observation is retained because it elaborates independently. The
guard/delete-control block and partial head were fully reverted after the third
attempt. No R34 term resurfaced and no new negative was added.

The next fresh attempt must pattern-match each registry as
`MkCoeffectContext entries unique` inside `pointwiseControlAfterDelete` and use
`localLookupDeleteEntriesSelfO5 nameEq actor entries unique` directly in the
actor branch. That keeps the exact `nameEq` dictionary visible in the
`lookupEntries` goal and avoids both the inferred wrapper dictionary and the
private imported helper. The already successful guard transport should then be
committed separately before the full head is reopened.

## Shared target-query lemma closes

`pointwiseConcreteTargetFiberSame` implements the reviewed correction. Its type
accepts the producer-owned equality `leftRetired = rightRetired`. Four total
clauses eliminate that equality before target normalization:

- `True/True`: both queries reduce to `Nothing` without dependency resolution;
- `False/False`: only this branch invokes `pointwiseResolveViewSame`;
- `True/False` and `False/True`: the producer equality is impossible.

The first attempt showed that a local `case` did not refine the left flag. The
second used an equality-indexed `with` but failed total coverage because Idris
still requested mismatched Boolean branches. The third explicit four-clause
form elaborated.

Commit: `91e14e4` — transport related owner target queries pointwise.

## L-Divert/L-Leave boundary

A complete L-Divert producer was attempted three times and reverted. It reached
the public source plan/replay data, pointwise owner lookup, reloading-control
relation, shared target-query lemma, and target mismatch transport. The final
blocker was not target-query semantics but dependent reification of the target
owner after destructing `reloadingRightControls`:

```text
Mismatch between: replayedRemaining and remaining.
```

The failed term tried to force the target remaining program and view to the
source indices before reifying `fiberControlRelatedRightIsRight`.

The next fresh design must keep the target owner's *native* dependent indices:

1. reify `fiberControlRelatedRight` immediately after the pointwise lookup;
2. after destructing the relation, retain
   `Reloading replayedRemaining replayedAccumulator replayedView` unchanged;
3. apply `pointwiseConcreteTargetFiberSame` to those native lifecycles;
4. transport source mismatch first to the target query at `sourceView`, then use
   `viewsSame` only to change the comparison view to `replayedView`; and
5. construct the next lifecycle directly with
   `divertLifecycleControlRelated lifecycleSame`, avoiding manual replacement of
   remaining/view indices.

Because L-Leave has the same dependent-owner reification shape, it was not
opened after L-Divert exhausted the shared family budget. L-Unload/L-Advance were
also not opened.

## Safe boundary and estimate

Fully closed semantic heads remain O-Insert, O-Retire, and L-Begin. The approved
O-Remove source observation and the shared retired-aware target-query lemma are
proved. O-Remove, L-Divert, L-Leave, L-Unload, and L-Advance heads remain open,
as do whole-suffix RAR/ordinal composition and final adjacent assembly.

Holes remain **20**, split **6/4/8/1/1**. The mandated O6 estimate stays
**18–34 shifts**: two prerequisite representations closed, but no additional
semantic head closed and the heavy lifecycle families remain fully charged.
