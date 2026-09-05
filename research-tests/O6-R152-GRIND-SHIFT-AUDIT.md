# O6 R152 — deletion producer/scanner closure and scoped-enrichment stop audit

## Coordinate, scope, and order

R152 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`311000ff8b2b58e215015022117b16b641ccc90c`.  The only initial untracked
artifacts were the permitted `paper/` directory and
`review-o6-body-adversarial.md`; both remain untouched and untracked.

The shift kept production frozen and followed the ratified route-B order from
`O6-R146-STRATEGY-MEMO.md`:

1. enrich the research-side deletion producer with constructor-owned RuleTag,
   replay-readiness, endpoint, generation-bijection, and generated-ordinal
   equations;
2. close the operational occurrence fold;
3. close the left scanner discard induction;
4. close its right mirror; and
5. attempt the enriched deletion-chain adapter under a fresh strict budget.

No production source, `dgamma.ipkg`, local-diamond source, O14, O17, O19, or
O21 withdrawal branch was edited.  No build-tree deletion or from-scratch
rebuild was performed.  An orphan-process check preceded every fresh compiler
invocation, and only one Idris process ran at a time.

## Unit A — constructor-owned deletion producer equations (pass 3/3)

Commit `250ecd9` (`research: enrich deletion producer equations`) retained the
missing operational capital in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr` and migrated the two
affected R11 fixtures.

### Retained surface

- `GenerationSubsequenceRuleTagsPreserved` binds source/survivor RuleTag
  equality in every kept constructor and recurses through deleted constructors.
  The equality belongs to the concrete replay producer; it is not inferred from
  action equality.
- `DeletionProducerOperationalCapital` now owns all three segment
  `GenerationReplayReady` values and `ReplayReadyEndsAt` endpoints, the three
  segment tag certificates, one global
  `RegistrationGenerationBijection`, whole-trace tag preservation, and exact
  generated-registration ordinal transport.
- The enriched capital is threaded through `DeletionChainStep` and its direct
  constructor consumers.
- `R11DeletionCertificateProjectionPositive` projects the new capital and
  checks.
- `R11DirectDeletionStepCloneNegative` was migrated to the new constructor
  arity and still rejects an independently selected occurrence map.

### Attempt record

The initial command-path corrections remained under the same attempt-1 label.
The three source-level attempts were:

1. the end constructor named invalid `GenerationActionSubsequenceEnd`
   arguments;
2. the end constructor still left the implicit live environment unbound; and
3. binding the exact end indices in the constructor telescope checked.

The retained module then passed direct checks for DeletionChain,
CanonicalSort, RenamingComposition, and CrossTrace.  The positive projection
fixture passed, while the direct clone fixture rejected at the intended
`occurrences and alternate` boundary.

## Unit B — operational occurrence fold (pass 1/3)

Commit `c6d05f8` (`research: close deletion operational occurrence fold`)
retained fully explicit producer projections for:

- arbitrary action origins;
- generated-registration origins;
- generated action/registration coherence; and
- exact generated ordinal transport.

`deletionStepOperationalOccurrenceFoldSpike` now constructs the full
`MkActionRegistrationReplayCorrespondence` from the enriched deletion producer.
The action-side tag clause comes only from the constructor-owned segment tag
certificates introduced in Unit A.  The unit checked on its first source-level
attempt.

## Unit C — left scanner deletion discard (pass 2/3)

Commit `85b9251` (`research: close left deletion scanner discard`) fills
`deletedClassificationForcesLeftScannerDiscardSpike`.

The retained proof introduces one constructor-owned head/tail view for a
located generated registration and performs structural induction over
`RegistrationTraceCorrespondence`:

- right-only scanner constructors recurse without changing the left index;
- an ordinary skipped left head is impossible when it is the located generated
  registration;
- queued or matched surviving left heads are impossible because
  `DeletedGenerationClassification` supplies the later parent unload while
  `SurvivingRegistration` supplies `NoParentUnload`;
- the exact `DiscardLeftDeletedRegistration` head is retained in
  `indexedDeletedGenerations`; and
- tail occurrences recurse at the successor scanner ordinal, with both their
  state-indexed suffix and additive ordinal transported explicitly.

Attempt 1 exposed only the orientation of `plusSuccRightSucc` in all four tail
branches.  Attempt 2 reversed those equations and checked.  No raw-name-only
membership argument is used: the result is the exact
`RegistrationGeneration` from the classification.

## Unit D — right scanner mirror (pass 2/3)

Commit `2d1f66c` (`research: close right deletion scanner mirror`) fills
`deletedClassificationForcesRightScannerDiscardSpike`.

The unit retains the direct right-side deleted-index preservation/head lemmas
and a structural symmetry of the accepted correspondence:

- `inverseRegistrationGenerationBijection` swaps the two generation maps and
  their inverse laws;
- `inverseRegistrationEventMatch` transports child generation, parent
  generation, component, activation, and position evidence;
- `symmetricRegistrationTraceCorrespondence` mirrors all nine scanner
  constructors and both pending-event match directions; and
- the public right theorem applies the already checked left induction to that
  exact mirror.

Attempt 1 showed that the two matched-registration clauses had not explicitly
bound `child`, `parent`, and `component`; it also identified the source-side
ordinal needed by the left-headed match.  Attempt 2 bound those constructor
indices, corrected the ordinal side, and checked.

## Unit E — enriched deletion-chain adapter (failed 3/3)

The fresh adapter budget stopped at the already suspected generation/global
abstraction boundary.  A disposable
`DGamma.R152EnrichDirectProbe` instantiated every premise of
`deletionTheoremProof` from `CanonicalizationPremises` and
`DeletableClosingEpisode` and asked only for the underlying `DeletionResult`.
The probe and any generated interfaces were removed after exhaustion.

### Attempt record

1. The first disposable spelling lacked the direct `Decidable.Equality` import;
   the compiler rejected `DecEq` and consequently could not expose the imported
   theorem.
2. After that correction, the otherwise deliberately minimal probe still
   lacked the direct modules exporting `RegistrationProtocol` and the replay
   bundle projections; the compiler rejected the incomplete import closure.
3. With the same explicit import closure as the research module, the complete
   call reached the intended semantic seam and rejected:

   ```text
   When unifying:
     (consumer : name) ->
     (consumerEpisode : LocatedClosedEpisode ... consumer trace) ->
     GenerationScopedClosingStart ... consumer consumerEpisode ->
     PrecedenceEdge ... -> Void
   and:
     NoDependentClosingEpisode (selectedActor candidate) trace
   Mismatch between:
     GenerationScopedClosingStart ...
   and:
     PrecedenceEdge ...
   ```

The strict budget was counted conservatively by compiler invocation, including
the two disposable import-closure failures; it was not silently extended.  No
failed body or probe was retained.

### Binding boundary

`DeletableClosingEpisode` intentionally carries
`NoDependentClosingEpisodeForGeneration`: only consumer activations whose exact
`LBegin` is inside the selected generation's installed interval are forbidden.
The frozen production `deletionTheoremProof` still requires the refuted raw-name
predicate `NoDependentClosingEpisode`, quantified over every closed consumer
episode in the whole trace.

These propositions cannot be promoted by weakening or by a cast.  With raw-name
reuse, a consumer may validly depend on an older generation of the same raw
selected name and close before the selected generation starts.  Such an episode
is outside `GenerationScopedClosingStart` but is rejected by the production
predicate.  Supplying the scoped function to the production theorem would
therefore be unsound.

The route-B producer work remains the sound next decomposition:

1. use the retained exact pre-interval classifier to split an installed foreign
   activation into inside-selected and before-selected cases;
2. in the inside case, construct `GenerationScopedClosingStart` and consume the
   scoped no-dependent proof;
3. in the before case, use closing/reissue localization plus the committed-view
   and selected-unload reliance invariants to exclude the exact selected
   generation; and
4. feed that direct `providerCandidate = False` evidence to a research-side
   generation-scoped variant of the selected and post-close replay consumers.

Because production was frozen, R152 did not change the old theorem surface and
never fabricated a global no-dependent proof.  The R146 semantic stop condition
did not fire: no checked constructor admitted selected unload while a committed
consumer remained installed, and no generation-location theorem was refuted.
The stop is a real frozen-interface mismatch, not evidence against route B.

## Final checks and fixture disposition

Fresh final evidence after disposable-probe removal:

```text
Idris 2, version 0.8.0

DeletionChain seeded direct check:
  exit 0

seeded package closure:
  exit 0

R11DeletionCertificateProjectionPositive:
  exit 0

R11DirectDeletionStepCloneNegative:
  compiler exit 1
  intended diagnostics present:
    cloneDeletionStepWithAlternateMap
    occurrences and alternate

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty

local-diamond diff from R152 start 311000f:
  empty
```

The seeded aggregate R11 script progressed through all five spike modules and
all positive fixtures through `R8FullPipeline`, including the migrated R11
projection fixture, then stopped at
`R16ConfluenceTheoremAssemblyPositive`.  Its call to
`fullPipelineFromBundles` omits the two now-required
`FullPipelineLateCanonicalPremises` arguments.  Neither that fixture nor
`CP5ConfluenceCrossTraceSpike.idr` changed in R152, so this is an unchanged
late-pipeline fixture drift rather than a deletion regression.  The affected
R11 negative was therefore checked directly at its exact expected diagnostic.

## Census, restrictions, and ordered stop

R152 closes three research holes.  The census is now **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

The remaining DeletionChain holes are exactly:

- `enrichDeletionChainStepSpike`;
- `deleteClosingEpisodesCoreSpike`; and
- `assembleClosingFreeAccountingSpike`.

No new hole, postulate, `believe_me`, `assert_total`, unsafe operation,
`partial`/`covering` annotation, retained local `let`, or retained `with` block
was introduced by R152.  `%default total` and the quantity discipline remain
unchanged.  Apart from this audit before commit, the only untracked paths are
the two permitted initial artifacts.

The mandatory ordered stop fired at Unit E, so O10/O11 bodies and all unrelated
parked holes were not opened.  A future shift must be newly authorized; it
should begin from this audit and build the research-side generation-scoped
replay consumer rather than retrying a direct call to the frozen global theorem.
