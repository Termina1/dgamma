# O6 revision 135: Deletion O7 erased-interface restatement audit

## Authorization and impossibility witness

This is the supervisor-pre-authorized O7 surface revision, made only after Unit
A was parked at its binding helper-budget stop.  It precedes every O7 body
attempt.

R134's disposable `R134O7RuntimeMiddleProbe` is the impossibility witness for
the old relevance: matching `MoreTransitions transition rest` and attempting to
place its hidden middle state, transition, and suffix into an unrestricted
runtime result failed with `{middle:74780} is not accessible in this context`.
The parallel quantity-0 view succeeded.  Consequently this revision changes
quantities, not the mathematical quantifiers or obligations.

## Field-by-field old to new mapping

### Occurrence entry

| Old surface | New surface | Preservation argument |
|---|---|---|
| `ClosingEpisodeOccurrence = (selected ** LocatedClosedEpisode ... selected trace)` | public erased-view family `ClosingEpisodeOccurrence ... trace`, constructor `ErasedClosingEpisodeOccurrence (0 selected) (0 episode)` | The actor quantifier, episode quantifier, dictionaries, trace index, and endpoint indices are unchanged.  Both payloads move to quantity 0 so the erased middle states inside `LocatedClosedEpisode` cannot escape to runtime. |
| unrestricted `scannedClosingOrdinal` eliminator | global quantity-0 `scannedClosingOrdinal`, eliminating only `ErasedClosingEpisodeOccurrence` | The result remains exactly `transitionCount (traceBeforeOpening episode)`.  No ordinal equation changes. |

### `ClosingEpisodeScan`

| Old field | New field | Preservation argument |
|---|---|---|
| unrestricted `scannedClosingOccurrences : List ClosingEpisodeOccurrence` | `0 scannedClosingOccurrences : List ClosingEpisodeOccurrence` | The entire exact list, including order and multiplicity, remains in the record; only runtime availability changes.  Each entry still carries an actual located episode through the erased view, so scan soundness is not weakened. |
| `0 scannedClosingOrdinalsUnique : UniqueKeys (map scannedClosingOrdinal scannedClosingOccurrences)` | unchanged proposition and quantification | Exact opening-ordinal uniqueness is retained. |
| `0 everyClosingOccurrenceScanned : (selected) -> (episode : LocatedClosedEpisode ...) -> Elem (transitionCount ...) (map ... scannedClosingOccurrences)` | unchanged proposition and quantification | Completeness for every actor and every located closed episode is retained verbatim. |
| `0 emptyScanIsClosingFree : scannedClosingOccurrences = [] -> NoClosingEpisodes ... trace` | unchanged proposition and quantification | The empty-scan implication is retained verbatim. |

The producer `closingEpisodeOccurrenceScanSpike` keeps both explicit endpoint
arguments and the exact trace/result indices, but the global definition moves
to quantity 0.  Thus there is no quantifier weakening and no dropped obligation.

## Downstream quantity closure inside the spike

All O7 consumers in `CP5ConfluenceDeletionChainSpike` were checked in the same
surface revision:

- `MaximalClosingSelection.scan` is now an erased index.
- `NoMaximalClosingEpisode.empty`,
  `SelectedMaximalClosingEpisode.candidate`, and its exact scanned-ordinal
  membership are quantity 0.  The membership formula is unchanged.
- `selectMaximalClosingEpisodeSpike` and its scan argument are quantity 0.
- `ClosingStepChoice`'s closing-free evidence, candidate, and exact
  `DeletionChainStep` are quantity 0, permitting the already-quantity-0
  `chooseClosingStepSpike` to consume the erased selection without relevance
  leakage.
- `chooseClosingStepSpike` itself is unchanged and still routes the empty branch
  through `emptyScanIsClosingFree` and the selected branch through the same O9
  adapter.

No downstream consumer genuinely requires runtime relevance: every path out of
O7 already ends in the quantity-0 deletion/canonicalization theorem chain.
`DeletableClosingEpisode` and `DeletionChainStep` retain their complete internal
records; only the constructor bindings by which O8/O7 pass them onward become
erased.  Therefore no runtime-dependent downstream hole is silently weakened.

## Fresh check and fill status

After deleting the terminal DeletionChain TTC/TTM, the visible check reported:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
exit 0; no Error: diagnostic
```

The O7 body is still exactly `?closingEpisodeOccurrenceScanSpike_rhs`.
Restatement consumes **0/3** O7 fill attempts.  Hole counts remain **18**, split
**5/4/8/0/1**, until a separately committed body fill succeeds.
