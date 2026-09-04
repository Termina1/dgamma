# O6 R147 — O21 sealed-bijection surface revision audit

## Scope and coordinate

R147 began at exact `44b26d348c7b18daa7892d1d652dbec07efdb506` on
`cp5-thm73-scoping`, with only the permitted untracked `paper/` directory and
`review-o6-body-adversarial.md`. This commit is the bounded Part 1 surface/build
revision ratified by `O6-R146-STRATEGY-MEMO.md`. It attempts none of O21's three
withdrawal branches and changes no production source.

## Constructor-owned bijection

`ReplayedCanonicalEndpointBridge` no longer accepts either a caller-selected
`NameBijection` or a proof equating that selection with the endpoint renaming.
Its sole constructor now accepts exactly four clauses, each directly indexed by
`expectedBridgeBijection sameInputs`. The old public eliminator names remain:
`replayBridgeBijection` computes the expected endpoint bijection and
`replayBridgeBijectionFixed` computes to `Refl`.

This implements the R146 old-to-new clause map without weakening a clause:

| R146 current clause | R147 revised clause |
|---|---|
| free `replayBridgeBijection` constructor argument | removed; eliminator returns `expectedBridgeBijection sameInputs` |
| caller proof `replayBridgeBijectionFixed` | removed; exported eliminator is definitionally `Refl` |
| `replayBridgeAmbient` | stored unchanged at the sealed bridge indices |
| `replayBridgeTables` | stored directly at `expectedBridgeBijection sameInputs` |
| `replayBridgeControls` | stored directly at `expectedBridgeBijection sameInputs` |
| `replayedGeneratedBirthMatched` | stored directly at the expected renamed child/parent and retains the exact generation equation |

The positive authenticated bridge rebuilder and wrong-birth attack fixture were
migrated from six constructor arguments to the four real proof obligations.
`CanonicalConvergenceResult`, `canonicalConvergenceFromBridge`,
`canonicalSchedulesConvergeSpike`, `originalEndpointsConvergeSpike`, and the
public O21 result type retain their existing indices and propositions. The O20
producer is still a hole, so there was no retained constructor body to respell.

## Fresh checks and boundary evidence

Before every fresh check, orphan `idris2` processes were terminated. Only each
terminal module's TTC/TTM was removed; the seeded build tree was not deleted.
All checks used Idris 2 v0.8.0 and the seeded `build/ttc/2025081600` path.

Passing checks:

```text
CP5ConfluenceRenamingCompositionSpike: 4/4, exit 0
R8BridgeAuthenticatedDirectionPositive: 1/1, exit 0
CP5ConfluenceCrossTraceSpike: 5/5, exit 0 (pre-existing lowercase warnings only)
R8FullPipeline: 1/1, exit 0
```

The required attacks continue to be rejected:

```text
R8BridgeWrongBirthNegative: exit 1
  missing exact generationForward ... = registrationGeneration ... equation
R8WrongTraceBridgeNegative: exit 1
  operationalTargetFinal cannot unify with otherFinal
R8PublicScheduleCannotReachBridgeNegative: exit 1
  CanonicalSchedule cannot unify with IndependentCanonicalSchedule
R8WrongOccurrenceBridgeNegative: exit 1
  first occurrence correspondence cannot unify with second
```

The wrong-birth failure occurs at the deliberately supplied `()` in place of
the retained exact birth equation, confirming that constructor sealing did not
weaken generation authentication.

## Disposition

The R146 Part 1 cure is complete. The research-hole census remains 13, split
CanonicalSort 2 / CrossTrace 4 / DeletionChain 6 / LocalDiamond 0 /
RenamingComposition 1. `replayedCanonicalToOriginalEndpointSpike` remains at
its original hole: this revision intentionally does not attempt its
left-withdrawn, right-withdrawn, or both-withdrawn branches.
