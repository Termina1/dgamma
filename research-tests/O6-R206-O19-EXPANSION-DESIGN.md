# R206 → R207: O19 attached-grammar redesign proposal

**Proposal only; no production/frozen change authorized or applied by this document.**
This is exactly the semantic consumer re-proof obligation predicted by the CP3
unfreeze draft, not a new claim that its Tier1 definitions are ill-typed.

## Why the old proof cannot be repaired by renaming

`ActorLifecycleOnly` is now `core ++ bundle`, with owned-child Retire/Remove in
the core, and forced root inserts/Retire/Remove in the bundle. The old
`O19SourcePairObservation`/`O19PairObservation` classify only lifecycle AA,
child-insert OA/AO, and child-insert/child-insert OO. They require `ChildOf actor`
for each insert. An actual `OInsert root Root component` cannot inhabit that
case; a child/root Retire/Remove is not an insertion or activation.

`NoGeneratedChild forbidden` prohibits a **new child insertion** only. It says
nothing about controlling an existing child or the owner of an attached root.
An action-word observation can retain the original source lookup, but cannot
transport it to a replay cut merely because the action labels agree.

## Proposed source observation and pair interface

Use occurrence/source-state-indexed observations with seven semantic forms:
actor lifecycle, yielded child insert, owned child Retire, owned child Remove,
forced-root insert, same-bundle root Retire, same-bundle root Remove. Preserve
exact source tags, parent/fiber lookup and native occurrence equations at
quantity0; retain executable action/component values. Preserve bundle insertion
reason, prior-root membership and the source `AttachedRelease` occurrence when
transporting the **grammar**, even if a weaker word-only observation does not
expose all of these fields.

The pair interface must cover all admitted products of these forms (at most49
before incompatibility pruning), not just the old four. Separate static
source-value observations from obligations about the reached pair. Never store
a desired diamond/row/guard as a new "observation" field.

Required new pair analyses include:

- lifecycle versus owned-child Retire/Remove, both orientations;
- child insert versus child control, both orientations, including same raw name
  and generation freshness/retirement/removal conditions;
- control/control (Retire/Retire, Retire/Remove, Remove/Retire, Remove/Remove),
  with real action-domain and parent metadata transport;
- forced-root insert/control versus lifecycle, child insert/control and another
  bundle's root insert/control; root external order is observable and cannot be
  erased as an internal action;
- genuine impossible pairs proved from reached-state/protocol invariants,
  rather than omitted by pattern coverage or an attached-to-core cast.

## Which frozen statements require a separate gate

- `CP5ConfluenceLocalDiamondSpike`: existing local relational diamonds may
  already contain some raw orchestration orientations. Inventory and reuse
  their precise hypotheses first. Any missing orchestration-control case,
  altered adjacency hypotheses, or change to `adjacentSwapSuffixSpike` requires
  exact statement probe + native positive/negative fixtures + owner gate.
- `CP5ConfluenceCrossTraceSpike.operationalAdjacentBlockSwapSpike` (frozen O19
  body): cannot continue to consume an unconditional four-case classifier for
  the enlarged blocks. Re-derive the column/Cartesian producer, external-order
  preservation, reached safety and decomposition for attached blocks first.
  Do not change the frozen body merely to accept a caller-supplied final result.
- `CP5O19ReachedBlocksSpike`: rebuilding a production attached body from label
  words requires transport of child lookup/parent facts and `AttachedReason`,
  not just a fold rebuilding the old lifecycle/yield spine. Preserve core/bundle
  split and original occurrence matching through the actual Cartesian run.
- `BlockBefore` has a revised append association. Native ordered-cut equations
  must be re-derived, not converted through an assumed old prefix shape.
- The four frozen hole declarations, CanonicalSort, DeletionChain and endpoint
  bridge are unchanged in R206; no hole-body change follows from this proposal.

## A10/A12 paper-gap cases to audit

A10 owned-child controls can release provision collisions without being an
actor lifecycle edge. A12 attaches forced roots after the releasing core and
preserves SAME-BUNDLE root controls. Strict-root-first and root-before-OTHER-
child claims are retired by A8/A12, not counterexamples to revised placement.
Cross-bundle controls require authenticated prefix/generation history; the
present empty-start same-bundle grammar intentionally does not solve that debt.

Moving bundles may violate observable root input order or change why a root was
forced. Incomparability of the two supported actors plus NoGeneratedChild does
not itself discharge those obligations. Establish exact sufficient conditions
from existing orchestration and support witnesses; if impossible, seek a
separate theorem-statement gate instead of claiming unrestricted commuting.

## Acceptance plan for the proposed redesign

1. Minimal native fixtures for each added action form and representative
   crossing (including release→forced insertion and same-bundle control).
2. Total source-state observations and separately proved reached-state frames.
3. Conditional row producers with every missing primitive premise visible.
4. Discharge premises from actual input invariants or explicitly report the
   weaker theorem; no new postulates/holes, no scoped→raw cast.
5. New Cartesian/reached attached-grammar proof, then frozen-body gate and full
   invalidation closure validation. CrossTrace fresh PASS is not presumed.
