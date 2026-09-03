# O6 revision 131: Canonical O12 scan-helper budget stop audit

## Scope and coordinate

This grind shift started at the required coordinate
`40ee490ce19f765cadda1a23bdfd4fe3c5f79f7c` on branch
`cp5-thm73-scoping`.  The worktree contained only the permitted untracked
`paper/` directory and `review-o6-body-adversarial.md`; neither was modified,
staged, or committed.

O6 remained closed.  The deferred R129 end-to-end integration was not
reattempted.  Production `src/`, `dgamma.ipkg`, the immutable CP3 theorem, and
the frozen adjacent-swap declaration remained untouched.

The supervisor granted O12 a fresh three-attempt fill budget, conditional on
landing the actor/owner bridge, a research-side active-to-installed proof, and
an explicitly telescoped executable ordinal scan first.  Helper commits do not
consume the O12 fill budget.  This shift remained entirely in that preparation
phase: `closingFreeTraceShapeSpike_rhs` was never replaced or otherwise opened.

## Retained helper units

The following research-only, total helper commits were retained.  Every commit
was followed by a visible fresh check of
`DGamma.CP5ConfluenceCanonicalSortSpike` with no `Error:` diagnostic.

| Commit | Attempts | Result |
|---|---:|---|
| `a2a94c3` | 1 | Exhaustive `canonicalTransitionActorActionOwner` bridge over all eight actions. |
| `70fbb1d` | 1 | Research-side `canonicalActiveImpliesInstalled`, independently derived from lookup and lifecycle elimination. |
| `fe8ff01` | 1 | Structural installed-trace endpoint fold. |
| `456f790` | 2 | Quiet plus installed implies Active; attempt 1 did not rewrite the abstract lifecycle into `quietFiber`, while attempt 2 matched the complete fiber once. |
| `e2a687a` | 1 | Right-suffix extension of an exact located closing episode. |
| `11c94f4` | 1 | A lifecycle occurrence before an uninstalled segment endpoint forces a forbidden closing episode. |
| `26f8251` | 1 | Structural fold from pointwise lifecycle exclusion to `NoLifecycleBy`. |
| `f66da78` | 2 | Unsupported lifecycle occurrence exclusion; attempt 1 used a forbidden nonlinear equality-dictionary pattern, while attempt 2 accepted exact aligned action/equation inputs. |
| `7dc3050` | 1 | Aligned occurrence-exclusion fold which exposes the producer dictionaries to classifiers. |

These helpers satisfy the mandated transition-actor/action-owner and
active-to-installed preparations without changing the private CP3 surface.
They also retain the closing-classification path needed by O12: a classifier
result either becomes an exact `LocatedClosedEpisode`, contradicting
`NoClosingEpisodes`, or remains installed through its endpoint.

## Executable ordinal scan budget stop

The final preparation helper was an executable scan for the ordinal of the
first selected lifecycle occurrence.  It used no reserved identifier, no local
`let` alias, and declared the complete type telescope
`name/key/world/error/value`, both endpoint states, the equality dictionary,
and the selected actor.  Its fresh three-attempt helper-unit budget was
exhausted before a retained declaration was possible:

| Attempt | Result |
|---:|---|
| 1 | The structurally generic `Transition` head made its existential `middle` state inaccessible at the `transitionActor` classifier scrutinee. |
| 2 | Matching the `Fired` action directly removed the classifier problem, but the recursive tail call still required the inaccessible existential `middle`. |
| 3 | Both endpoint states were made explicit function arguments and `{middle}` was named on `MoreTransitions`; Idris 2 v0.8.0 still marked `middle` inaccessible inside the nested `with` branch at the recursive call. |

The decisive diagnostic was:

```text
Error: While processing right hand side of with block in with block in
canonicalFirstLifecycleOrdinal. middle is not accessible in this context.
```

This is an elaboration/scoping stop, not evidence that the ordinal proposition
is false and not a stored-vs-reconstructed existential-index correlation wall.
Nevertheless the three-attempt unit budget is binding.  Per the standing stop
rule, the entire uncommitted scan candidate was removed, including all generated
TTC/TTM output from its checks.  No restatement, copy-probe, O12 fill attempt,
second CanonicalSort hole, or DeletionChain pivot was opened afterward.

A future authorized shift should avoid carrying the existential middle through
nested `with` branches.  The most direct next probe is a top-level one-head
classifier returning an executable `Either`/small data value, followed by plain
structural recursion outside `with`; this audit does not authorize that probe.

## Hole and plan status

The research-hole census remains **19**, split **6/4/8/0/1**:
CanonicalSort 6, CrossTrace 4, DeletionChain 8, LocalDiamond 0, and
RenamingComposition 1.  `THM73-PLAN.md` was not changed because no obligation
class or hole progressed.  O12 used **0/3 fill attempts**; the stopped ordinal
scan helper used **3/3 helper attempts**.  All retained helper units and their
attempt counts are listed above.

## Validation and disposition

The terminal gate rechecks the seeded production package, all research suite
units, production-byte identity, CP3 blob identity, and both frozen
adjacent-swap surface hashes.  Those exact outputs are reported to the
supervisor with this audit commit coordinate.

The shift ends at a safe committed boundary with only the two permitted
untracked paths.  No staged files or disposable probe sources/interfaces
remain.
