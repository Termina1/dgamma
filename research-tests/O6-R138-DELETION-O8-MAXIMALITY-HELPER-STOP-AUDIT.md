# O6 revision 138: O8 maximality capital and parent-open helper stop

## Start coordinate and scope

The shift started at the required clean coordinate
`af7c8d5b2a366ec8e1c914ad887a60b8d8c8d47c` on
`cp5-thm73-scoping`; the only initial untracked paths were the permitted
`paper/` and `review-o6-body-adversarial.md`.  The three R137 audits and the
revision-137 section of `THM73-PLAN.md` were read before editing.

Work stayed inside Unit A.  O8's body was not opened, O9 was not reached, and
CanonicalSort remained parked.  The external
`/tmp/r137-o8-uncommitted-delta.patch` was consulted only as a source of ideas;
it was never applied.  Every retained helper was reconstructed without local
`let` aliases or new `with` blocks, freshly checked, and committed immediately.

## Retained checked capital

| Commit | Retained lemma-sized unit | Fresh post-commit result |
|---|---|---|
| `548f07287a9ecca5ec3f9fa26506e85efba72e52` | Erased finite `MaximumBy` witness and total `chooseMaximumBy`. | `2/2: Building DGamma.CP5ConfluenceDeletionChainSpike`; exit 0. |
| `e818d1f7eaf1bc34037b643e2dfcf97f5c7a2653` | Exact preimage recovery from membership in `map`. | same visible fresh result; exit 0. |
| `ed9e44fa7d80650a8b61c43809e449b7b4c42f26` | O7 completeness plus maximality yields an upper bound for every closing ordinal. | same visible fresh result; exit 0. |
| `fd2e85d5d6a535909139e08f79b8e177b05c6f0f` | Strict generation-interval ordinal lower bound. | same visible fresh result; exit 0. |
| `9232cdbdef7889d8c7fbce9b34c7a0124b077a93` | `maximalClosingHasNoScopedDependent`, discharging revised O8 dependency negativity by incompatible ordinal bounds. | same visible fresh result; exit 0. |
| `b453111da4d4ad555babf468f09f720b6471aa0d` | Exact located-action head/tail view and prefix lift. | same visible fresh result; exit 0. |
| `1055228d2ef6c8d62a6abc1ed217556f45c8287e` | Generation-stamp and `GeneratedDuring` prefix transport. | same visible fresh result; exit 0. |
| `7971c8c25d02933c4def91a95de7b3e22246c484` | Exact `ChildGenerationInventory` and projection to `RegisteredGenerationsDuring`. | same visible fresh result; exit 0. |
| `85f19dd0bc357ede85b3add9fd50759031f52844` | Sound/complete inventory lift across a non-child-birth head. | same visible fresh result; exit 0. |
| `a06a8d70c2bfc9d37d1d40b2aad3b55bd20aa926` | Sound/complete inventory extension at a matching child birth. | same visible fresh result; exit 0. |
| `ad1fdeca7ea89277b4408ac2ff2484962ebf9461` | Exact occurrence, retirement-tail, and closing-tail witnesses. | same visible fresh result; exit 0. |
| `66929cd1bdfcd7366f5e76f5a572f8abd9f33168` | Total scan producing the exact generated-child inventory from a supplied retirement callback. | same visible fresh result; exit 0. |

The maximality chain is therefore complete: once a maximal scanned occurrence
is selected, the revised generation-interval negative field is constructively
available.  The child inventory chain is also complete up to the callback that
every child inserted during the selected closing episode retires later in that
episode.

## Exhausted parent-open endpoint unit

The next helper unit attempted to reconstruct the private CP4 parent-open
endpoint facts needed to derive that retirement callback from
`RegistrationDiscipline`.  The production implementation exists in
`DGamma.CP4ParentSafety`, but its `reloadingEndpointOpen` and
`activeEndpointOpen` functions are private and production is frozen.

The unit used its independent **3/3** check budget:

1. Direct rewrites by an explicit `lookupFiber = Nothing/Just fiber` equation
   were rejected because Idris tried to rewrite the `ParentOpenAt` result type
   rather than the endpoint premise.
2. An explicit total `Maybe Fiber -> Bool` reification transported the premise,
   but Idris would not identify the public endpoint case tree with the separately
   named mirror.
3. Normalizing the mirror to the exact lifecycle case structure still left the
   named-function boundary opaque, so the same conversion did not check.

This is an elaboration/correlation boundary, not evidence that parent-open
preservation is false.  In accordance with the no-self-extension rule, the
entire failed unit, its temporary import, and terminal TTC/TTM were removed.
No failed declaration or disposable probe remains.

A future authorized unit should use a producer-owned exact-equation view whose
constructors expose the lookup and lifecycle chosen by the public endpoint
computation, rather than asking conversion to equate two separately named Bool
functions.  The alternative is an explicit authorization to export the already
proved CP4 helpers, but that would change frozen production and was not attempted.

## Attempt accounting and hole census

- Finite maximum and generation-scoped maximality retained units: each passed
  its fresh check; helper work does not consume O8's body budget.
- Child inventory retained units: the non-birth lift required two checks (the
  first exposed an accidentally implicit unqualified `bumpGeneration`; full
  qualification fixed it), the matching-birth extension required two checks
  (the first exposed a nonlinear dependent membership binder; replacing that
  erased index with `_` fixed it), and the other units passed their first check.
- Parent-open endpoint unit: **3/3**, exhausted and fully restored.
- O8 body: **0/3**, unchanged.
- O9 adapter gate: not reached.

The canonical census remains **17**, split **5/4/7/0/1**
(CanonicalSort/CrossTrace/DeletionChain/LocalDiamond/RenamingComposition).
No proposition, hole signature, or output constructor changed in R138.

## Frozen invariants and hygiene

The terminal gate revalidates the direct DeletionChain spike, the R7 boundary
consumer, the R137 interval ratification, seeded 207/207 production closure,
CP3 blob, production diff, and both adjacent-swap hashes.  The exact command
outputs are recorded in the shift handoff.  The proof delta contains no
`believe_me`, `assert_total`, postulate, `unsafePerformIO`, `partial`, local
`let` alias, or new `with` block.

At the committed gate, there are no staged files.  The only untracked paths are
`paper/` and `review-o6-body-adversarial.md`.
