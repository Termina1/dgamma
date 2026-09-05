# O6 R153 — generation-scoped deletion replay construction budget stop audit

## Coordinate, scope, and order

R153 began on branch `cp5-thm73-scoping` at the mandated exact HEAD
`6f6d06a72e4157375de824ea14072e444985036b`.  The only initial untracked
artifacts were the permitted `paper/` directory and
`review-o6-body-adversarial.md`; both remain untouched and untracked.

The authorized target was the research-only route-B replacement for the
raw-name-global Lemma-72 replay consumer:

1. construct exact generation-scoped crossing evidence;
2. fill O9 `enrichDeletionChainStepSpike`;
3. only after O9 checks, open O10 `deleteClosingEpisodesCoreSpike`; and
4. only after O10 checks, open O11 `assembleClosingFreeAccountingSpike`.

Production source and `dgamma.ipkg` remained frozen.  No local-diamond,
canonical-sort, cross-trace, renaming-composition, or withdrawal branch was
edited.  An orphan-process check preceded each compiler invocation and only one
Idris process ran at a time.

## Route-B construction attempted

The disposable O9 unit was developed only in
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`.  It did not call the
frozen raw-name `deletionTheoremProof` and did not define any conversion from
`NoDependentClosingEpisodeForGeneration` to `NoDependentClosingEpisode`.

The attempted construction followed the R146/R152 split rather than retrying
the frozen theorem:

- remove the unused current-generation witness fields from
  `GenerationScopedClosingStart`;
- enrich the exact pre-interval classification with the erased equation
  `transitionCount foreignPrefix = transitionCount selectedPrefix +
  S (transitionCount selectedToForeign)`, propagated structurally through its
  classifier;
- localize the foreign activation's first closing episode around the installed
  lifecycle anchor and extend that prefix episode into the original trace;
- derive the selected-generation consumer ordinal from the new count equation
  and the selected episode's exact start ordinal;
- in the inside-selected branch, build the exact
  `GenerationScopedClosingStart` and spend the scoped maximality premise;
- in the before-selected branch, transport the committed provider selection
  backward to the foreign opening, invoke the ordering theorem on the prefix
  ending at the selected unload, and exclude the selected `L-Begin` from the
  containing provider's installed closed interval; and
- return direct `providerCandidate ... = False` evidence, which is the premise a
  research-side replay consumer needs without globalizing the dependency
  proposition.

The disposable source also sketched the required append-occurrence transports,
closing localization, installed-trace endpoint lookup, and the no-second-begin
lemma for one installed episode.  This is useful decomposition evidence, but no
part of it is retained because the unit did not pass its strict compiler
budget.

## O9 route-B unit — failed 3/3

The strict source-level attempt budget was counted conservatively by compiler
invocation.

1. The first large integrated spelling reached parsing and reported an
   unclosed parenthesis in the newly written provider closed-interval
   decomposition.
2. After repairing that delimiter, parsing stopped earlier at the declaration
   boundary immediately following the copied spanning-occurrence decomposition,
   reporting `Expected a type declaration` at
   `extendLocatedClosingRightScoped :`.
3. Removing the erased top-level quantity annotation from that declaration did
   not change the diagnostic; it again reported `Expected a type declaration`
   at the same colon.

The third-attempt diagnostic was:

```text
Error: Expected a type declaration.

DGamma.CP5ConfluenceDeletionChainSpike:9965:33--9965:34
 9961 |     rewrite sym (appendTransitionsAssociative beforeOpening
 9962 |       (MoreTransitions (beginTransition opening) afterOpening) rightTrace) in
 9963 |     rewrite openingSplit in Refl
 9964 |
 9965 | extendLocatedClosingRightScoped :
                                        ^
```

The budget was not extended to test the subsequent shorter-name spelling.  The
entire failed O9 edit was saved only outside the repository for local forensic
reference and the tracked research source was restored exactly to HEAD.  No
failed body, generated interface, new hole, postulate, unsafe operation, or
partiality annotation was retained.

This is an elaboration-budget stop, not a semantic counterexample.  In
particular, no constructor was found that admits selected unload while a
committed dependent consumer remains installed, and neither the
inside-selected ordinal construction nor the before-selected ordering
contradiction was rejected by the type checker: parsing stopped before either
body was elaborated.

## Ordered stop and remaining obligations

The mandatory ordered stop fired at O9.  Therefore O10 and O11 were not opened.
The three DeletionChain holes remain exactly:

- `enrichDeletionChainStepSpike` (O9);
- `deleteClosingEpisodesCoreSpike` (O10); and
- `assembleClosingFreeAccountingSpike` (O11).

The whole research census remains **10**:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 3
- LocalDiamond: 0
- RenamingComposition: 1

A future authorized shift should split route B into smaller independently
checked units rather than submitting the complete crossing consumer before its
support library parses.  The most useful order is:

1. land the exact foreign-prefix count field and its two structural producers;
2. land append occurrence and closing-localization helpers;
3. land the installed-episode no-second-begin/containment contradiction;
4. land the two-branch direct provider exclusion; and only then
5. build the generation-scoped replay fold and fill O9.

That sequence preserves the intended semantic route while giving each parser
and dependent-index repair an independent three-attempt budget.

## Final gates

Fresh evidence after restoring the failed unit:

```text
Idris 2, version 0.8.0

DeletionChain direct check:
  exit 0

seeded production package closure:
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

production diff over src/ + dgamma.ipkg:
  empty
```

The target research module retains `%default total`.  Its census contains no
`believe_me`, `assert_total`, postulate, `partial`, or `covering` declaration.
The pre-existing checked alias of `deletionTheoremProof` at
`checkedDeletionSubroutine` is unchanged from HEAD and was not invoked or moved
by R153.  Apart from this audit before commit, the working tree contains only
the two permitted initial untracked artifacts.
