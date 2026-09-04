# O6 R145 Renaming-Composition Budget-Stop Audit

## Scope and inherited boundary

R145 started exactly at `9232660a35129a45419c5cfc1a8a97985e620610` on
`cp5-thm73-scoping`.  The only inherited untracked paths were `paper/` and
`review-o6-body-adversarial.md`; both remain untouched and untracked.
Production `src/`, `src/DGamma/CP3.idr`, and `dgamma.ipkg` remained frozen.

Unit A is recorded separately in
`O6-R145-DELETION-O9-CROSSING-CHECK-RETRY-STOP-AUDIT.md` at commit `65c7fa1`.
Its fresh countershape-fixture budget ended mechanically inconclusive at 3/3:
no overlapping-generation countershape and no operational refutation checked.
Consequently neither semantic route A nor route B was selected, O9 remains
parked at 0/3, and no route-B crossing-exclusion capital was authorized.

This audit records Unit B, the final
`replayedCanonicalToOriginalEndpointSpike` hole in
`research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr`.

## Retained checked helper capital

Every helper increment below was restored to the original single-hole body,
checked directly under Idris 2 v0.8.0, and committed before the fresh body
budget began or continued.  No helper changes a proposition, hole signature,
output constructor, or production declaration.

1. `38b2fb2` — **Compose O21 effect observations**
   - `compositionLookupBindingFromEqualBindings` converts exact ordered table
     equality into pointwise lookup equality.
   - `replayedCanonicalOuterAmbientSpike` composes the two canonical endpoint
     effect relations, relational replay endpoint, and bridge ambient equality.
   - `replayedCanonicalOuterTableSpike` composes the corresponding renamed
     table lookup chain.
   - Fresh helper budget: **3/3**, with the first two checks exposing the
     dependent-context pattern issue and the third passing via `cong
     (lookupEntries ...)`.

2. `666e926` — **Compose same-name and renamed fiber controls**
   - adds parent, lifecycle, fiber, and maybe-fiber composition on both sides of
     one `MaybeFiberRelatedBy` step;
   - retains iterators, accumulators, views, outcomes, parent shapes, retirement
     flags, and component indices;
   - fresh helper budget: **3/3**; the checks repaired renamed-view direction
     and the explicit `error` index required by `RenamedActive`.

3. `393db5c` — **Compose O21 controls outside withdrawals**
   - `replayedCanonicalOuterControlOutsideSpike` composes left endpoint,
     replay, renamed bridge, and inverse right endpoint controls whenever both
     raw names are outside their canonical withdrawal sets;
   - fresh helper budget: **2/3**, passing after the exact implicit-parameter
     form of `ControlEquivalentOutside` was used.

4. `1385405` — **Project absent domains through O21 controls**
   - adds domain-only eliminators for same-name and renamed maybe-fiber
     relations and a checked `RenamedAbsent` constructor from exact lookup
     equations;
   - fresh helper budget: **1/3**, passed.

5. `6a85ac6` — **Transport O21 absences across canonical bridge**
   - transports a canonical absence forward or backward through the full
     endpoint/replay/bridge chain, discharging the already-absent half of each
     unilateral withdrawal branch;
   - fresh helper budget: **2/3**; the second check replaced an insufficient
     dependent coverage pattern with explicit equality transport and passed.

The body stayed at its sole original hole throughout retained helper commits.

## Fresh body attempt budget: stopped at 3/3

The three body attempts were temporary, directly checked, and fully removed
before this audit.  The original declaration and sole hole are restored.

### Attempt 1/3 — effect assembly projection mismatch

A direct `MkSystemEquivalentByRenamingModuloVestigial` assembly used the checked
ambient/table helpers and left only pointwise endpoint disposition to fill.
Elaboration stopped first because the canonical endpoint field was referred to
as `endpointEffects`; the actual production projection is
`endpointEffectsEquivalent`.  No nested proof target was accepted.

### Attempt 2/3 — endpoint wrapper mismatch

After correcting the effect projection, the body split both canonical
withdrawal-name memberships and used
`replayedCanonicalOuterControlOutsideSpike` in the ordinary outside/outside
case.  Elaboration reached that case and rejected the nonexistent shorthand
constructor `RelatedEndpointFibers`: the production interface requires
`MkEndpointFiberRelatedModuloVestigial (Left related)`.  No withdrawal branch
was accepted.

### Attempt 3/3 — sealed bridge bijection is propositional

The final temporary body used the exact production wrapper and expanded the
four-way withdrawn-name skeleton, including already-absent propagation and the
remaining vestigial branches.  Elaboration reached the checked table helper but
stopped at the bridge index:

```text
Can't solve constraint between:
  bridge .replayBridgeBijection
and:
  (endpointRenaming sameInputs) .currentNameBijection
```

`ReplayedCanonicalEndpointBridge.replayBridgeBijectionFixed` supplies exactly
this equality propositionally, not definitionally.  A future attempt needs a
separately checked reindexing adapter before the ambient/table/control helpers
can consume bridge projections under the output bijection.  Because this was
attempt 3/3, no such adapter or fourth body was opened in R145.

The temporary four-way skeleton also made the next semantic boundary explicit,
but it did not elaborate past the bijection mismatch and is not retained:
withdrawn `VestigialNameWithdrawn` evidence has only retired/uninstalled/empty
runtime facts, while the CP3 output requires a full
`VestigialEndpointGeneration` indexed by the accepted scanner's *current exact
generation*.  Raw names may be reused, so `endpointNameHasGeneration` alone
cannot identify that current birth.  The accepted outer scanner and
`CurrentEndpointRenaming` remain the legitimate sources for a future sealed
withdrawal induction; no caller-selected membership or vestigial witness was
added.

## Validation and frozen-surface evidence

After restoring the original body, only the target `.ttc/.ttm` interfaces were
removed before the final direct check:

```sh
IDRIS2_PATH="$PWD/build/ttc/2025081600${IDRIS2_PATH:+:$IDRIS2_PATH}" \
  idris2 --source-dir research --check \
  research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr
```

Result: **exit 0**, `4/4: Building
DGamma.CP5ConfluenceRenamingCompositionSpike`.

The final seeded package closure also passed:

```sh
IDRIS2_PATH="$PWD/build/ttc/2025081600${IDRIS2_PATH:+:$IDRIS2_PATH}" \
  idris2 --build dgamma.ipkg
```

Result: **exit 0** with no diagnostics.

Frozen-surface comparisons against the mandated start commit all pass:

```text
git diff --quiet 9232660 -- src                 PASS
git diff --quiet 9232660 -- src/DGamma/CP3.idr PASS
git diff --quiet 9232660 -- dgamma.ipkg        PASS
```

The retained R145 RenamingComposition delta adds no `believe_me`,
`assert_total`, postulate, `unsafePerformIO`, `partial`/`covering` annotation,
new `with` block, or local `let`.  It adds no proof hole.  The only untracked
paths remain the two inherited permitted paths.

## Final census and safe gate

The research-hole census is unchanged at **13**:

- CanonicalSort: **2**
- CrossTrace: **4**
- DeletionChain: **6**
- LocalDiamond: **0**
- RenamingComposition: **1**

Unit A is mechanically inconclusive at 3/3, O9 remains unattempted at 0/3, and
route A/B remains unresolved.  Unit B retains substantial checked compositional
capital but the sole RenamingComposition body is budget-stopped at **3/3**.
Resume Unit B only with a fresh authorization and begin with a bridge-bijection
reindexing helper; after that, audit the exact-current-generation source for the
withdrawal branches before attempting the body again.  Units C and later remain
unauthorized because Unit A selected neither semantic route.
