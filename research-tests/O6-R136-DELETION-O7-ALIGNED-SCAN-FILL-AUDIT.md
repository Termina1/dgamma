# O6 revision 136: aligned O7 closing-scan fill audit

## Scope and result

This audit completes the revision-136 O7 work after the separately committed
minimal surface revision in
`O6-R136-DELETION-O7-ALIGNED-SURFACE-REVISION-AUDIT.md`.

`closingEpisodeOccurrenceScanSpike` is now total and hole-free.  It performs a
structural quantity-0 scan of the authenticated trace.  Every tail occurrence
is lifted through the head, and an exact L-Begin head contributes one occurrence
iff `classifyInstalledContinuation` finds that activation's first L-Unload.
The output continues to provide:

- actual erased `LocatedClosedEpisode` payloads;
- unique opening ordinals;
- membership for every located closed episode; and
- `NoClosingEpisodes` when the erased occurrence list is empty.

No output field, quantifier, state index, dictionary index, or downstream
consumer was weakened.

## Proof architecture

The retained proof is split into top-level total helpers with no local `let`
aliases and no new `with` blocks:

1. Prefix lifting constructs a located episode under one trace head and proves
   every lifted opening ordinal is a successor.
2. List algebra transports membership and `UniqueKeys` through that successor
   map; zero is fresh from every lifted tail ordinal.
3. `LocatedClosingHeadView` is an erased, actor-indexed view.  Its head case
   carries the exact equality between the supplied trace head and the located
   episode's `beginTransition`; its tail case carries an exact located episode
   in the tail.  The view is produced by eliminating the located decomposition,
   not by comparing proof terms or assuming proof irrelevance.
4. An installed continuation is proved incompatible with any supplied
   `FirstClosingResult`: `splitInstalledAtOccurrence` says the closing target is
   installed, while `lUnloadBoundary` says that exact target is uninstalled.
5. Separate empty, no-head, and closing-head scan builders establish
   completeness, uniqueness, and the closing-free consequence.
6. `scanActionHead` exhausts all eight action constructors.  The seven
   non-L-Begin forms are rejected as head openings by constructor disjointness.
   L-Begin uses `lBeginBoundary` and the existing total
   `classifyInstalledContinuation` to choose the closing or still-installed
   builder.
7. The final body recurses only on the aligned tail.  `AlignedTransitions`
   supplies the exact external dictionaries, action, tag, checked equation, and
   recursively aligned suffix required by the helpers.

All newly stored proof payloads and scan evidence remain quantity 0.

## Attempt accounting

The body used **2/3** fresh O7 fill attempts:

1. The first body was semantically complete but the empty-trace equation used
   two distinct pattern variables for definitionally equal endpoints.  Idris
   rejected this as a nonlinear pattern (`initial` unified with `finalState`).
2. Replacing the erased endpoint with `_` and retaining one named state made the
   same body check.  No third body attempt was used.

An earlier private helper assembly explored indexing the head-view constructor
by an exact `beginTransition opening`.  Its three helper checks showed that this
would force proof-term identity when consumers eliminated the view.  That
uncommitted assembly was fully restored.  The retained actor-indexed view instead
stores an erased head equality and passed fresh checks; it does not assume proof
irrelevance.

## Retained commits

The proof was landed in lemma-sized commits, each followed by deletion of the
terminal DeletionChain TTC/TTM and a visible fresh check:

- `d357681` — prefix lift for closing occurrences;
- `7dce592` — successor ordinal list algebra;
- `6bff658` / `ca13cec` — erased located-head decomposition, then the final
  actor-indexed/equality-carrying view;
- `d6a6a09` — contradiction between installed traces and first closing steps;
- `13282d2` — scan lifting and empty-trace lemmas;
- `a49955d` — exact head occurrence construction;
- `5e78fd7` — head uniqueness and completeness;
- `ce10250` — no-head completeness and closing-free transport;
- `3623844` — empty/head/tail scan builders;
- `82df642` — non-begin and still-installed head impossibility;
- `d9d5103` — L-Begin continuation classification;
- `1e3d6d9` — exhaustive aligned action dispatch; and
- `5d1ebe2` — the recursive O7 body.

## Fresh evidence and invariant audit

Before and after `5d1ebe2`, deleting the terminal TTC/TTM files produced:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
1/1: Building DGamma.R7DeletionBoundariesPositive
exit 0; no Error: diagnostic
```

The positive fixture still checks both direct alignment and the real
`CanonicalizationPremises` discharge through
`replayAligned (chainReplayCapital premises)`.

At `5d1ebe2`:

- branch: `cp5-thm73-scoping`;
- production `src/` and `dgamma.ipkg` diff from the required start: empty;
- DeletionChain source holes: 7;
- canonical family split: **5/4/7/0/1**, total **17**;
- O7 body hole: absent;
- `believe_me`, `assert_total`, `postulate`, and `unsafePerformIO` in the
  DeletionChain spike: absent;
- new `with` blocks and local `let` aliases in the revision-136 proof delta:
  absent; and
- O14 remained parked and unopened.
