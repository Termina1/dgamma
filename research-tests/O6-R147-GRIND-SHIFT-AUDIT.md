# O6 R147 — grind-shift gate audit

## Coordinate and ordered scope

R147 began at exact `44b26d348c7b18daa7892d1d652dbec07efdb506`
on `cp5-thm73-scoping`. The only inherited untracked paths were `paper/` and
`review-o6-body-adversarial.md`; neither was modified, deleted, or committed.
Production `src/` and `dgamma.ipkg` were not changed.

The shift followed the ratified `O6-R146-STRATEGY-MEMO.md`: bounded O21
sealed-bijection revision first, then O9 route B. O14, O17, O19, all O21
withdrawal branches, and all production changes remained forbidden and were
not opened.

## Part 1 — O21 sealed bridge complete

Commit `e6314b1` (`research: seal O21 bridge bijection`) completes the bounded
surface revision. `ReplayedCanonicalEndpointBridge` has one four-clause
constructor, and every clause is directly indexed by
`expectedBridgeBijection sameInputs`. A caller can no longer select a free
bijection or supply its fixedness proof. The old eliminators remain available;
`replayBridgeBijectionFixed` reduces to `Refl`.

The full clause map and fixture migration are recorded in
`O6-R147-O21-SEALED-BIJECTION-SURFACE-REVISION-AUDIT.md`. Fresh evidence:

```text
CP5ConfluenceRenamingCompositionSpike: 4/4, exit 0
R8BridgeAuthenticatedDirectionPositive: 1/1, exit 0
CP5ConfluenceCrossTraceSpike: 5/5, exit 0
R8FullPipeline: 1/1, exit 0

R8BridgeWrongBirthNegative: expected exit 1, exact generation equation missing
R8WrongTraceBridgeNegative: expected exit 1, target-final mismatch
R8PublicScheduleCannotReachBridgeNegative: expected exit 1, public/enriched mismatch
R8WrongOccurrenceBridgeNegative: expected exit 1, occurrence-index mismatch
```

The O21 hole remains intentionally unchanged because its three withdrawal
branches were forbidden this shift.

## Part 2 — O9 route-B progress and mechanics stop

### Retained checked scanner capital

Four immediately checked commits establish the reusable scanner side of the
required exact-generation accounting:

- `0a37039` — `research: preserve scanner deleted indices`
  - exact preservation through ordinary and surviving index advances;
  - exact prepending equation for a deleted registration;
  - helper unit budget 3/3 (dependent lookup equations were made
    producer-owned on attempts 2–3).
- `1e2bff9` — `research: retain left scanner discards`
  - structural fold proving that an existing left deleted-generation
    membership survives every accepted scanner constructor;
  - helper unit budget 1/3.
- `e7a35ed` — `research: reject unload in surviving scanner tail`
  - structural contradiction between `NoParentUnload` and an exact later
    `LUnload` occurrence;
  - helper unit budget 1/3.
- `e931548` — `research: classify generated scanner heads`
  - generated birth cannot take a non-registration skip;
  - exact surviving birth plus later parent unload is impossible;
  - exact discard head is inserted and retained to the scanner endpoint;
  - helper unit budget 2/3.

Each commit received a fresh visible direct check after removing only the
terminal DeletionChain TTC/TTM:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
exit 0
```

No right-scanner mirror was attempted: the R146 attack order permits it only
after the left located-prefix recursion is stable.

### Decomposition status

1. **Pre-interval classification:** a candidate `ExactTracePrefixComparison`
   producer retained real dependent prefix/suffix witnesses and deliberately
   avoided Nat-only ordering. Its disposable unit exhausted 3/3 checks:
   constructor hidden-index binding, dependent common-tail alignment, then
   non-linear equality-view alignment. It was fully removed. This is a
   mechanics stop, not evidence against route B.
2. **Closing/reissue localization:** the existing
   `closingOccurrenceGivesLocatedActivation` and `RegistrationGeneration`
   surfaces were inspected, but no new localization adapter was retained after
   the exact prefix classifier stopped.
3. **Committed-provider exclusion:** existing checked
   `crossingActivationExcludesSelectedProvider`,
   `SelectedUnloadRelianceAnchor`, `relianceAnchorProviderExcluded`, and
   `committedSelectedContradictsUnload` remain the intended semantic capital.
   New checked scanner-head contradictions establish the analogous exact
   closing-versus-surviving split on registration accounting. No accepted
   `L-Unload` with an installed committed consumer was found.
4. **O9 generation-cast adapter:** not opened because the exact pre-interval
   and left located-prefix producers did not reach a stable boundary.

The left located-birth scanner recursion helper used a separate 3/3 disposable
budget. Attempts reached (1) a reserved identifier parse correction, (2) the
required non-linear-pattern removal, and (3) a dependent final-index inference
boundary at the exact discard head. The helper was fully removed. This is the
specific mechanics stop for the left recursion.

### Hole attempt accounting

- `deletionStepOperationalOccurrenceFoldSpike`: body 3/3, fully restored.
  - constructor decomposition accepted;
  - identity occurrence correspondence was correctly rejected because the
    survivor final state differs;
  - expanding `MkActionRegistrationReplayCorrespondence` exposed the remaining
    action-origin, tag, generated-origin/coherence, generation-bijection, and
    embedding fold as one producer package.
- `deletedClassificationForcesLeftScannerDiscardSpike`: body 3/3, fully
  restored. Classification elimination, exact located-occurrence elimination,
  and the final generation-equality adapter all elaborated around one remaining
  exact located-prefix scanner fold.
- `deletedClassificationForcesRightScannerDiscardSpike`: 0/3 by ordered stop.
- `enrichDeletionChainStepSpike`: 0/3 by ordered stop; the monolithic body was
  not opened before its two prerequisites.

Thus the memo's semantic stop condition was **not** triggered. No exact
constructor case exhibited an accepted selected unload under an installed
committed consumer, and no checked result showed that route-B hypotheses are
semantically unable to locate a generation. The failures were elaboration and
dependent-index mechanics, so route B remains ratified without a route change.

## Census, safety, and final gate

The hole census remains **13**, split:

- CanonicalSort 2
- CrossTrace 4
- DeletionChain 6
- LocalDiamond 0
- RenamingComposition 1

No hole, postulate, `believe_me`, `assert_total`, unsafe operation,
`partial`/`covering` annotation, local `let`, or new `with` block was retained.
All retained additions are top-level and `%default total` remains in force.

Final fresh evidence:

```text
Idris 2, version 0.8.0
DeletionChain seeded direct check: 2/2, exit 0
seeded package closure: 207/207 DGamma.CP4ProgressProof, exit 0
src/DGamma/CP3.idr blob: 2c697e532e83989de8591fa6a4378747c6a501c0
production diff from 34b21c9 over src/ + dgamma.ipkg: empty (0 bytes)
adjacentSwapSuffixSpike full: 1470 bytes,
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
adjacentSwapSuffixSpike statement prefix: 1154 bytes,
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

No full build-tree deletion or from-scratch rebuild occurred; one `idris2`
process ran at a time, with orphan process termination before fresh checks.
