# O6 R141 — O9 generation-scoped surface revision audit

## Scope and necessity

This research-only revision changes the `enrichDeletionChainStepSpike` boundary
before any O9 body attempt. Production remains frozen.

Two checked witnesses make the revision necessary:

- R137 commit `2a92a1b` constructs a permitted two-generation raw-name-reuse
  trace. It has first-generation `ActorA -> ActorB` and second-generation
  `ActorB -> ActorA` precedence edges while every pointwise precedence graph is
  acyclic. Therefore the raw-name-global `NoDependentClosingEpisode` premise is
  false for both raw closing actors.
- `O6-R140-DELETION-O8-CLOSED-O9-ADAPTER-MISMATCH-STOP-AUDIT.md` records that O8
  now soundly produces `NoDependentClosingEpisodeForGeneration`, whereas frozen
  CP3 `deletionTheorem` still requests the refuted raw-global predicate.

A coercion from the scoped predicate to the raw predicate is unsound and is not
introduced.

## Clause-by-clause old → new mapping

| Old O9 clause | Revised O9 clause | Effect |
|---|---|---|
| `nameEq`, `keyEq`, `protocol` | identical | unchanged |
| `initial`, `finalState`, `trace` | identical | unchanged |
| `CanonicalizationPremises ... trace` | identical | unchanged |
| `candidate : DeletableClosingEpisode ... trace` | identical | unchanged |
| scoped dependency evidence only reachable as the candidate projection | explicit erased `noDependent : NoDependentClosingEpisodeForGeneration ... (selectedActor candidate) (selectedStartOrdinal candidate) (selectedStartLive candidate) (selectedEpisode candidate)` | exposes the only sound dependency premise at the adapter boundary |
| `DeletionChainStep ... premises candidate` | identical | unchanged |

The extra explicit premise is exactly `selectedNoDependentClose candidate` at
the genuine `chooseClosingStepSpike` consumer. It adds no assumption unavailable
to an existing candidate and weakens no quantifier inside the predicate. The
consumer actor, global located closing episode, pointwise `PrecedenceEdge`, and
`Void` conclusion are unchanged from R137; only the previously ratified exact
generation/activation-interval relevance witness remains required.

`R7DeletionBoundariesPositive.enrichOnly` is revised in the same series and
continues to pin the full public O9 boundary. `chooseClosingStepSpike` supplies
the exact candidate projection. No other research consumer exists.

## Mandatory production flag

Frozen `src/DGamma/CP3.idr`'s `deletionTheorem` premise is invalid under
permitted raw-name reuse, as witnessed by R137. Consequently
`DGamma.CP4DeletionTheorem.deletionTheoremProof` inherits an invalid public
interface even though its internal algorithm may only need interval-relevant
uses. Fixing that production interface and its CP4 dependency chain is a
flagged obligation for a future unfreeze campaign.

R141 does not edit, coerce, wrap, or silently rely on that production premise.
The authorized next unit is a research-local Lemma-72 analogue whose explicit
premise is the generation-scoped predicate and whose result supplies the spike
chain.

## Attempt accounting and checks

Surface revision: 0/3 O9 body attempts. The O9 RHS remains a named hole in this
commit. Direct spike and R7 consumer checks are required before commit. The
production tree, CP3 blob, adjacent-swap surface, hole census, and repository
hygiene are checked at the commit gate.
