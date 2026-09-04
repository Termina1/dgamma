# O6 R144 — O17 stable-sort base and body-budget stop audit

## Coordinate and scope

R144 started at exact commit `569446ac955c965193dd770889e3874f7ca795cb` on
`cp5-thm73-scoping`.  The tracked tree was clean; the only untracked paths were
the permitted `paper/` directory and `review-o6-body-adversarial.md`.  The R143
audit and `THM73-PLAN.md` were read before work.  O14, O9, and the later
DeletionChain class were not opened.

The supervisor had already completed the required clean 207/207 production
build and seeded the production TTC cache.  R144 did not remove `build/` or run
another clean build.

## Retained O17 capital

Three small base-case units were checked independently and committed
immediately:

- `canonicalElemEmpty` is the local quantity-0 eliminator for empty withdrawal
  lists;
- `canonicalSortingIdentityEndpoint` constructs the exact no-withdrawal
  reflexive endpoint required by sorting; and
- `canonicalSortedIdentity` assembles a complete `SortedClosingFreeTrace` when
  the actor blocks, their order/disjointness, lifecycle coverage, input
  placement, and registration tree are already available.  It uses an actual
  zero-step `FiniteAdjacentSwapDerivation`, reflexive external orchestration,
  and the reflexive endpoint above.

This closes the terminal/base assembly of O17 without weakening its output and
without a postulate, unsafe cast, local `let`, or new `with` block.

## O17 body attempt accounting

`sortClosingFreeTraceSpike` consumed its fresh **3/3** body budget.  Every failed
body was removed.

1. **Attempt 1:** applied the checked identity/base assembler to the actual O17
   inputs.  Idris exposed the complete remaining telescope: exact contiguous
   blocks, their ordered/disjoint coordinate proofs, lifecycle coverage,
   canonical input placement, and an authenticated registration tree.
2. **Attempt 2:** supplied the direct supported-episode selection from
   `ClosingFreeTraceShape`.  This does not discharge the remaining telescope:
   the input only locates an interleaved installed episode, while the base
   assembler requires the result of operationally hoisting it into a contiguous
   actor block.
3. **Attempt 3:** fixed the candidate's intended `LocatedOpenEpisodeBlock` type
   explicitly and reached the same incomplete stable-sort boundary.  No
   definitional coercion turns the input interleaved episode into the output
   block package; finite adjacent swaps must be produced first.

The stable-sort statement does **not** smell false and no countershape was
found.  The stop is constructive implementation debt, not a surface defect.
The next O17 campaign must introduce a producer-owned recursive sorting state
that simultaneously carries the current trace/bundle, accumulated
`FiniteAdjacentSwapDerivation`, stable external-input relation, exact moved
block ranges, and operational registration correspondence.  It must not retry
the exhausted identity-as-complete-sort representation.

## Validation at the stop boundary

After restoring the O17 hole, a fresh direct check removed only
`CP5ConfluenceCanonicalSortSpike.ttc/.ttm` and rebuilt the module successfully
under Idris 2 v0.8.0.  The tracked tree was then clean.  Production sources,
package configuration, immutable CP3, and the byte-frozen adjacent-swap surface
were not edited.

O17 remains open at 3/3.  The hole census remains **13**, split
**CanonicalSort 2 / CrossTrace 4 / DeletionChain 6 / LocalDiamond 0 /
RenamingComposition 1**.  Per the ordered scope, CanonicalSort is now closed for
this shift and the next class is CrossTrace.
