# O6 revision 135: Deletion O7 dictionary-correlation stop audit

## Scope after the erased restatement

The quantity-only O7 restatement landed independently at `30c762c` and its full
DeletionChain consumer graph checked.  O7 then received a fresh **3-attempt**
body budget.  Before editing the body, the standing correlation-wall rule
required a disposable copy-probe.

The remaining surface still quantifies arbitrary explicit `nameEq` and `keyEq`
dictionaries independently of the dictionaries stored by each `Fired`
transition.  Unlike actual canonicalization consumers, O7 receives no
`AlignedTransitions nameEq keyEq trace` premise.

## Disposable exact-shape probe

Temporary module `DGamma.R135O7DictionaryProbe` exposed one syntactic L-Begin
head's four dictionaries separately.  Its total quantity-0 function attempted
the minimum reconstruction required for a sound scan entry:

```idris
0 reclassifyCheckedBegin :
  (externalNameEq : DecEq name) ->
  (externalKeyEq : DecEq key) ->
  (transitionNameEq : DecEq name) ->
  (transitionKeyEq : DecEq key) ->
  ... ->
  checkedApplyAction @{transitionNameEq} @{transitionKeyEq}
    (LBegin actor) before = Just (LBeginTag, afterState) ->
  BeginStep externalNameEq externalKeyEq actor before afterState
```

The only possible direct body, `MkBeginStep checked`, failed freshly with:

```text
1/1: Building DGamma.R135O7DictionaryProbe
Error: While processing right hand side of reclassifyCheckedBegin.
...
Mismatch between: transitionNameEq and externalNameEq.
```

The temporary source and both possible TTC/TTM outputs were removed.  This is
the same executable `DecEq` correlation obstruction that required explicit
aligned premises for the already-ratified O3/O4/O5 dictionary repairs; moving
values to quantity 0 does not make distinct dictionary computations
definitionally equal.

## Why this stops the exact O7 body

The restated scan deliberately retains the old implicit soundness obligation:
every element of `scannedClosingOccurrences` is still an actual
`LocatedClosedEpisode ... nameEq keyEq ...`, now wrapped by
`ErasedClosingEpisodeOccurrence`.  A structural finite scan must therefore
reconstruct `BeginStep nameEq keyEq` (and eventually `UnloadStep nameEq keyEq`)
from trace transitions before it may add an entry.  The trace only provides
those checked equations under its stored transition dictionaries.

Conversely, omitting an uncorrelated syntactic opening does not solve the
problem: `everyClosingOccurrenceScanned` quantifies every episode under the
external dictionaries.  Replacing the occurrence list by all raw ordinals
would make completeness easy but would drop the old list's occurrence-soundness
obligation, violating the binding content-preservation condition.

The narrow constructive repair would be to supply
`AlignedTransitions nameEq keyEq trace` to O7 (available from
`CanonicalizationPremises` at every real consumer), or to index the scan by the
trace's own dictionaries and add an authenticated alignment transport.  Either
changes the theorem's premise/correlation surface and was not authorized by the
quantity-only restatement.  It is therefore not made here.

## Attempt and source status

This probe is a mandatory pre-attempt semantic stop, not an O7 fill attempt.
O7 remains at **0/3** body attempts and its body remains exactly
`?closingEpisodeOccurrenceScanSpike_rhs`.  No helper, probe source, or generated
artifact remains.  The erased restatement stays committed because it is
independently correct and closes the R134 runtime-relevance defect, but it is
not claimed to solve this separate dictionary-correlation requirement.

Unit A is already parked at its binding 3/3 helper-budget stop.  Unit B now hits
a binding semantic stop before its first fill attempt.  Per the shift rule, no
O8 or other hole is opened.  The campaign gates at **18 holes**, split
**5/4/8/0/1**.
