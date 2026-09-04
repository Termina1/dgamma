# O6 revision 137: O8 generation-start / activation-interval surface revision

## Authority and necessity

Supervisor ruling selected the research-only activation-interval option and
explicitly forbade edits to the frozen CP3/CP4 production surface.  Commit
`2a92a1b` is the mandatory necessity witness:

- a real 24-step checked trace contains first-generation `ActorA -> ActorB` and
  later-generation `ActorB -> ActorA` edges;
- both corresponding consumer activations have genuine located closes;
- every pointwise finite precedence graph satisfies a strict rank check; and
- the old raw-name `NoDependentClosingEpisode` rejects both O7 closing actors.

Therefore the old O8 field cannot be filled.  This revision changes only the
research DeletionChain candidate surface and consumes **0/3** fresh O8 body
attempts.

## New exact witness

`GenerationScopedClosingStart` authenticates that a consumer close is relevant
to the selected deletion candidate.  It stores:

1. `scopedSelectedGeneration` — the exact registration generation;
2. `scopedSelectedCurrent` — that generation is current in the selected
   episode's already-computed `selectedStartLive`;
3. `scopedSelectedOrdinal` — the selected episode's global opening ordinal is
   exactly `selectedStartOrdinal`;
4. `scopedConsumerOpening` — an exact located `LBegin consumer` inside
   `closedInside (locatedEpisode selectedEpisode)`; and
5. `scopedConsumerOrdinal` — the consumer episode's global opening ordinal is
   the selected start plus one plus that local occurrence ordinal.

The two ordinal equations tie the local occurrence to the supplied global
consumer episode without equality of erased transition proof terms.

`NoDependentClosingEpisodeForGeneration` retains the negative edge conclusion
but requires this witness.  A later raw-name birth, or any reactivation outside
the selected installed interval, cannot manufacture it.

## Clause-by-clause old → new mapping

Old field:

```idris
selectedNoDependentClose :
  NoDependentClosingEpisode selectedActor trace
```

New field:

```idris
selectedNoDependentClose :
  NoDependentClosingEpisodeForGeneration
    {global = trace}
    selectedActor selectedStartOrdinal selectedStartLive selectedEpisode
```

Mapping:

| Old clause | New clause | Ruling |
|---|---|---|
| raw `selectedActor` | same actor plus `scopedSelectedGeneration` and exact `scopedSelectedCurrent` at `selectedStartLive` | strengthened authentication; separates births |
| global `trace` | same global trace | unchanged |
| arbitrary `consumer` | same arbitrary consumer | unchanged |
| genuine global `LocatedClosedEpisode consumer trace` | same located episode | unchanged |
| `PrecedenceEdge selectedActor consumer` at consumer start | same exact edge/state | unchanged |
| no temporal/generation correlation | exact selected opening ordinal, exact selected current generation, exact located consumer opening inside selected `closedInside`, exact global consumer ordinal | added minimal relevance scope |
| result `Void` | `Void` | unchanged |

No O7 occurrence payload, scan uniqueness/completeness field, maximal-selection
result constructor, deletion-step result, dictionary parameter, runtime action,
or endpoint type changed.

## Replay soundness

Deletion removes only the selected activation episode: its opening, internal
selected lifecycle actions, and closing unload.  A foreign consumer can observe
that activation as a committed provider only when the consumer's `LBegin` occurs
while the selected fiber is installed.  Such an opening is exactly what
`scopedConsumerOpening` locates in `closedInside selectedEpisode`; the closing
transition itself cannot be an `LBegin`.

A consumer opened before the selected `LBegin` could not have committed that
inactive selected activation.  A consumer opened after its `LUnload` observes
either no selected provider, a later activation, or a later birth.  Deleting the
selected interval therefore does not justify a global raw-name prohibition for
those episodes.  Interval scoping is the smallest repair that preserves O8's
role: forbid precisely the dependency that would make removal of this selected
activation invalidate a foreign committed view.

The explicit current-generation and ordinal fields prevent the interval from
being detached from the generation scan already carried by
`DeletableClosingEpisode`; the interval evidence is not merely a raw action-name
membership.

## Downstream research consumers

Repository search found `selectedNoDependentClose` had no projection consumer;
it was only a field of the not-yet-constructible `DeletableClosingEpisode`.
`MkDeletableClosingEpisode` also had no existing construction site because O8
remained a hole.  Consequently the exact research ripple is confined to the
field type and the new supporting types.  The entire DeletionChain spike checks
with all later declarations unchanged.

Positive and negative ratifications are mandatory next and will be committed
before any O8 body attempt.

## Explicit frozen CP3/O9 adapter obligation

**FLAGGED NEXT GATE:** production `deletionTheorem` still accepts the old global
raw-name `NoDependentClosingEpisode`.  O9's eventual adapter therefore cannot
silently pass the revised O8 field to CP3.  Supervisor ruling makes CP3 and all
CP4 consumers immutable in this campaign.  O9 must receive a separate audited
resolution (for example, an admissible research adapter or an explicit stop);
no coercion from the revised interval predicate to the refuted raw predicate
exists, as commit `2a92a1b` proves.

This obligation is intentionally not hidden by a hole move or a weakened
projection.  It must also be recorded in `THM73-PLAN.md` in the revision-137
status update.

## Fresh check and invariants

After deleting terminal `CP5ConfluenceDeletionChainSpike` TTC/TTM files:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
exit 0; no Error: diagnostic
```

At this surface point:

- branch: `cp5-thm73-scoping`;
- `src/` and `dgamma.ipkg` diff from the required baseline: empty;
- O8 body remains the same single hole;
- the surface revision spent 0/3 O8 fill attempts;
- no `believe_me`, `assert_total`, postulate, or `unsafePerformIO` was added;
- the checked evaluator, O7 scan, occurrence ordinals, and later DeletionChain
  result shapes are unchanged.
