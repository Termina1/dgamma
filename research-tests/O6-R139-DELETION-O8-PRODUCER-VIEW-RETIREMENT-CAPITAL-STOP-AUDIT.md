# O6 R139 — Deletion O8 producer-view and retirement-capital stop audit

## Scope and verdict

**Verdict: PARTIAL ACCEPT / HELPER-UNIT STOP.**

R139 completed the supervisor-authorized producer-owned lookup/lifecycle equation
family and used it to prove the exact generated-child retirement callback needed
by the O8 inventory. It also completed exact episode/global lifting, closing-tail
localization, child-name distinctness, and a candidate assembler whose only
remaining argument is `selectedChildrenHaveNoEpisode`.

O8 itself remains deliberately unopened at **0/3**. O9 was not edited. The next
retirement-persistence helper unit exhausted its independent **3/3** budget and
was reverted, so this audit stops the unit rather than hiding a hole or
transplanting the unchecked R137 reference patch.

## Accepted checked capital

All retained commits were followed by a fresh visible check of
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`.

### Producer-owned endpoint and parent-open chain

The retained R139 chain starts after R138 at `a44c9d4` and includes exact erased
lookup inspection, `ParentEndpointLookupEquation`, reloading/active endpoint
views, `ParentOpenEquationView`, foreign/owner action transport, no-recovery
propagation, closing contradictions, aligned/discipline projections, and exact
generated-registration transport. The last pre-continuation commit was
`9688418`.

### Retirement and closing-prefix chain

- `712b370` — action occurrence head view.
- `b298978`, `0440843` — child retirement is ordered before the supplied parent
  unload, including provenance lifting.
- `8d54be1`, `469f8ba`, `37cdc4f` — retirement is restricted to the exact prefix
  containing the selected unload and connected to generated-insert capital.
- `daed2d2` — an episode-local child birth is lifted to the exact global
  generated registration.
- `c631ab5` through `8f8b89f` — exact located-action head/suffix equations and a
  proof that a distinct interior action precedes the closing singleton.
- `59640c8`, `b8e3634` — the selected unload is after every child birth and every
  generated child retires inside that birth-to-close suffix.
- `14844db`, `37591ad`, `9738ff5` — generated child/parent names are distinct and
  every generated inventory entry is outside the selected raw parent name.
- `7990cda` — `maximalCandidateFromGenerationScan` assembles every
  `DeletableClosingEpisode` field except the explicit global
  `NoRegisteredEpisode` argument.

### Beginning of the missing no-episode capital

- `5407e1a` — `retireFiber` sets the retirement flag.
- `34fb24f`, `eed38b5`, `87a4e7b` — normalized retired Inactive behavior and
  lifecycle/fiber projections showing that `beginFiberAction` returns `Nothing`.
- `455fdaf`, `a766fd0`, `920edac`, `7c73f51`, `df8c2d0` — exact lookup-to-begin
  application transport and contradiction of a successful `LBegin` from a
  retired lookup.
- `f955a6b` — exact local `RetireTargetLookupView`, retained for the next producer
  unit.

No retained helper uses `believe_me`, `assert_total`, postulates, or another
unsafe proof device. No new `with` block or local `let` alias was introduced.

## Newly exposed O8 obligation

R138 described the child inventory as complete once its retirement callback was
available. R139 proves that callback, but construction of
`DeletableClosingEpisode` additionally requires:

```idris
NoRegisteredEpisode nameEq selectedRegistrations 0 [] trace
```

This is not a definitional consequence of
`maximalClosingHasNoScopedDependent`. A complete proof must connect the exact
retirement occurrence to lifecycle inactivity/current-generation persistence,
extract a closing episode from any registered-generation begin that occurs
before retirement, globalize that close, contradict maximality, handle the
post-retirement and pre-birth segments, and combine singleton results over the
inventory list.

The old `/tmp/r137-o8-uncommitted-delta.patch` confirms the shape of this missing
chain but is **reference only**: it is unchecked and contains banned local lets,
new `with` blocks, and over-large mutually dependent proof bodies. None of it was
applied.

## Exhausted helper unit

The attempted next producer was `retireLookupMissingImpossible`, the `Nothing`
branch required to build a local retire-success view without widening imports.
Its independent budget was used as follows:

1. **1/3:** direct signature failed because Idris could not bind the dependent
   `value` implicit; the downstream contradiction was therefore inaccessible.
2. **2/3:** adding explicit `{name, key, world, error}` / `{value}` binders left
   the same dependent implicit failure.
3. **3/3:** explicitly ascribing the `ORetire` action still left the same
   implicit-binding failure.

The failed helper was fully reverted. `RetireTargetLookupView` itself remains
checked. Per the gate rule, the unit stops here rather than trying an unbudgeted
fourth spelling or widening the import surface to
`DGamma.CP4DeletionBoundaryDeleted`.

## Fresh-check evidence

Final command:

```text
idris2 --source-dir src --source-dir research \
  --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
```

Final result:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike (research/DGamma/CP5ConfluenceDeletionChainSpike.idr)
```

The canonical unresolved census remains **17**, split:

- CanonicalSort: 5
- CrossTrace: 4
- DeletionChain: 7
- LocalDiamond: 0
- RenamingComposition: 1

Production freeze checks against `34b21c9` are clean for `src/`,
`src/DGamma/CP3.idr`, and `dgamma.ipkg`. The only allowed untracked paths remain
`paper/` and `review-o6-body-adversarial.md` before this audit is committed.

## Structured acceptance report

| Check | Result |
|---|---|
| Producer-owned exact endpoint view | ACCEPT |
| Generated-child retirement callback | ACCEPT |
| Exact closing-prefix localization | ACCEPT |
| Generated inventory and outside-parent proof | ACCEPT |
| Candidate assembly except `NoRegisteredEpisode` | ACCEPT |
| Global no-registered-episode chain | OPEN; next unit stopped at 3/3 |
| O8 body | UNOPENED, 0/3 |
| O9 body/surface | UNCHANGED / GATED |
| Visible spike build | PASS |
| Production freeze | PASS |
| Unsafe proof devices | NONE |

## Required next gate

Resume with a fresh, separately authorized spelling of the retire-success
producer (prefer an explicit fully applied lookup family that avoids the failed
implicit binder), then proceed in dependency order:

1. retired/inactive/current-generation persistence;
2. future-retirement closing extraction;
3. globalized closing/maximality contradiction and segment assembly;
4. singleton-to-list `NoRegisteredEpisode` combination;
5. only then consume the still-fresh O8 body budget.

No O9 work is permitted before O8 acceptance and the mandatory supervisor
analysis gate.
