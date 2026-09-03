# O6 revision 135: grind-shift gate audit

## Start coordinate and ordered scope

The shift started from required HEAD
`d2828ca3ff67f1729ab7c6b9d3571c54a3bcbd7d` on
`cp5-thm73-scoping`.  The only initial dirt was the permitted untracked
`paper/` and `review-o6-body-adversarial.md`.  Both R134 audits were read before
editing.  Work stayed in ordered scope: Unit A O14, then Unit B O7; O8 and all
other holes remained unopened.

## Retained commits and fresh checks

| Commit | Change | Fresh post-commit visible check |
|---|---|---|
| `75021cc73e17875f561b504d6d93774c0ee85c16` | Add standalone `canonicalRankLTETransitive`, using plain equations. | `3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike`; exit 0. |
| `e26ad0f6ae70d8b50cb1b280a9722fb6bb953c69` | Audit and park exhausted O14 rank-sort helper unit. | `3/3: Building DGamma.CP5ConfluenceCanonicalSortSpike`; exit 0. |
| `30c762cf1ab35aab5909c5625b61943dfa28eb27` | Restate O7 occurrence/scan and its proof-only consumers through a public erased view; add field-by-field audit. | `2/2: Building DGamma.CP5ConfluenceDeletionChainSpike`; exit 0. |
| `891805143555c0be0dc08e25e89b4daca302efd6` | Audit the O7 dictionary-correlation semantic stop and update `THM73-PLAN.md`. | `2/2: Building DGamma.CP5ConfluenceDeletionChainSpike`; exit 0. |

The terminal gate then freshly rebuilt both visible spikes again, reporting
CanonicalSort `3/3` and DeletionChain `2/2`, both exit 0 with no `Error:`
diagnostic.  One Idris process ran at a time, and orphan Idris process groups
were checked/killed before fresh checks.

## Attempt accounting

- Standalone O14 rank-transitivity lemma: passed its first check and landed in
  the mandatory separate commit; helper commits do not consume the body budget.
- O14 protocol-rank stable-sort helper unit: **3/3** attempts, exhausted and
  fully restored.  The retained transitivity lemma is independent.  O14 body:
  **0/3**, unchanged.
- O7 erased surface: independently checked and committed before body work.
- O7 dictionary probe: the first disposable check exposed missing explicit
  imports in the probe itself; after adding only `Metatheory` and
  `Decidable.Equality`, the next check reached the intended exact equation and
  failed on `transitionNameEq` versus `externalNameEq`.  Source and TTC/TTM were
  removed.
- O7 body: **0/3**.  The correlation failure is a binding pre-attempt semantic
  stop under the no-quantifier-weakening condition.

The class census has delta **0** and remains **18 holes**, split
**5/4/8/0/1** (CanonicalSort/CrossTrace/DeletionChain/LocalDiamond/
RenamingComposition).  The O7 surface changed only relevance; its hole did not
close.

## Frozen-surface and production evidence

Terminal evidence:

```text
seeded package closure:
  207/207: Building DGamma.CP4ProgressProof
  exit 0

src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0

production diff from 34b21c9 across src/ + dgamma.ipkg:
  empty (0 bytes, git diff --exit-code = 0)

adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf

adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

The full-definition hash starts at `0 adjacentSwapSuffixSpike :` and excludes
the terminal newline.  The statement prefix starts at the same byte and ends
after `adjacentSwapSuffixSpike =`, matching the frozen measurement convention.
The immutable `confluenceTheorem` is inside the verified CP3 blob.

## Final hygiene and disposition

`git diff --cached --name-only` is empty.  The only untracked paths are the two
permitted paths, `paper/` and `review-o6-body-adversarial.md`.  No disposable
probe source or generated probe TTC/TTM remains.  `git diff --check` passes.

Both authorized units are now binding stops: Unit A exhausted its helper budget;
Unit B exposed the unprovided dictionary correlation before a fill attempt.  No
new hole is opened.  A future O7 revision must explicitly authorize either an
`AlignedTransitions nameEq keyEq trace` premise (already supplied by real
canonicalization consumers) or a producer-owned trace-dictionary/alignment
package; silently replacing the actual-occurrence list by raw ordinals would
drop soundness and is rejected.
