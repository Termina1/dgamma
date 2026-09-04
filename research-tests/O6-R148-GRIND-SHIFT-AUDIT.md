# O6 R148 — grind-shift mechanics stop audit

## Coordinate and scope

R148 began on branch `cp5-thm73-scoping` at exact
`c7be93fad5c8066aaf06356478e08c0af34a73da`, with only the permitted untracked
`paper/` directory and `review-o6-body-adversarial.md`. Both were left
untouched. The production tree and package manifest were not edited.

The shift followed `O6-R146-STRATEGY-MEMO.md` and the ordered R148 scope. Unit A
was the mandatory erased-view redesign of the pre-interval classifier. Its
fresh 3-attempt budget stopped at a dependent tail-index elaboration boundary.
Consequently Units B and C were not opened. O14, O17, O19, O21 withdrawal
branches, and production code remained untouched.

## Unit A — erased pre-interval view

The disposable candidate was a public inductive
`ErasedFirstLifecyclePreIntervalView`, indexed by:

- the selected and foreign `BeginStep`s;
- both exact prefixes to the openings;
- the selected inside suffix and foreign installed suffix; and
- erased `InstalledTrace` evidence for the foreign activation.

Its two constructors represented `ForeignOpeningInsideSelectedInterval` and
`ForeignOpeningBeforeSelectedInterval`. Constructor arguments retained the
state-indexed intervening trace and exact prefix/suffix alignment. The total
covering lemma recursed structurally over the selected and foreign prefixes;
consumers would only eliminate the view and would not reconstruct equality
views.

### Attempt transcript (3/3)

1. **Attempt 1:** the family and covering recursion elaborated through the two
   strict-order base cases, but the equal-position branch failed while
   eliminating the erased full-trace equality:

   ```text
   Error: While processing right hand side of
   erasedFirstLifecyclePreIntervalCovering. Can't solve constraint between:
   ?_ [no locals in scope] and ?_ [no locals in scope].
   ... Refl => void (actorDistinct Refl)
   ```

   Per the mandatory rule, no restatement was made before a minimal probe.
2. **Attempt 2:** after applying the probe-backed equal-position cure, the
   covering lemma advanced to the both-nonempty recursive branch. Rebuilding a
   side-prefix equality with `cong (MoreTransitions selectedHead)` failed
   because the erased whole-trace equality did not make the two dependent head
   proofs definitionally identical:

   ```text
   Mismatch between: selectedHead and foreignHead.
   ```
3. **Attempt 3:** the view was restated so each constructor carried the complete
   caller alignment plus only the branch-local exact suffix, avoiding the
   rejected lifted head equality. The recursive call then failed at precisely
   the dependent tail index:

   ```text
   Error: While processing right hand side of
   erasedFirstLifecyclePreIntervalCovering. When unifying:
     appendTransitions selectedRest
       (MoreTransitions (beginTransition selectedOpening) selectedInside)
   and:
     appendTransitions foreignRest
       (MoreTransitions (beginTransition foreignOpening) foreignAfter)
   Mismatch between: selectedInside and foreignAfter.
   ```

The third failure is mechanics, not a constructor case or operational
counterexample. The complete view candidate was removed after exhaustion; no
unchecked helper or changed hole body remains.

## Mandatory disposable probe

`DGamma.R148ErasedViewEqualPositionProbe` reproduced only the equal-position
elimination. After an initial administrative missing-import correction, its
proper baseline check failed with the same anonymous dependent constraint:

```text
1/1: Building DGamma.R148ErasedViewEqualPositionProbe
Error: While processing right hand side of equalOpeningActorsImpossibleProbe.
Can't solve constraint between: ?_ [no locals in scope] and ?_ [no locals in scope].
... Refl => void (actorDistinct Refl)
exit 1
```

The probe cure made the common opening source an explicit telescope argument
and projected the first action through a fully instantiated function:

```text
firstActionProbe name key world error value
```

`justInjective` followed by `cong actionOwner` then yielded `actor = selected`
without asking `Refl` to infer the dependent state indices. The cured probe
passed:

```text
1/1: Building DGamma.R148ErasedViewEqualPositionProbe
exit 0
```

The probe source and its TTC/TTM artifacts were fully removed. This evidence
cured the equal-position base case but did not cure the later recursive tail
alignment.

## Units B and C

- **Unit B (left located-prefix recursion probe): 0/3.** Not opened because the
  ordered Unit A prerequisite did not reach a checked boundary.
- **Unit C occurrence fold: 0/3.** Not opened.
- **Unit C left scanner discard body: 0/3.** Not opened.
- **Unit C right scanner mirror: 0/3.** Not opened.
- **Unit C enriched O9 adapter: 0/3.** Not opened.

The R147 checked scanner capital at `0a37039`, `1e2bff9`, `e7a35ed`, and
`e931548`, and the sealed O21 bridge at `e6314b1`, remain unchanged.

## Semantic disposition

The ratified route B is unchanged. No exact constructor case showed an accepted
selected `L-Unload` coexisting with an installed committed consumer, and no
checked result showed that the candidate hypotheses cannot locate the needed
activation or generation. The R146 semantic stop condition therefore did not
fire. This is an elaboration/mechanics stop under the explicit 3-attempt rule.

A future authorized redesign should avoid recursing by re-synthesizing a tail
equality between two independently indexed append expressions. The evidence
points to a producer-owned *joint prefix spine* (one constructor owns the common
head and the tail alignment) or a family whose recursion is driven by that
single spine, rather than another spelling of the two-prefix equality
elimination exhausted here.

## Census and gate evidence

The hole census remains **13**, split:

- CanonicalSort: 2
- CrossTrace: 4
- DeletionChain: 6
- LocalDiamond: 0
- RenamingComposition: 1

After removing all disposable code, a fresh visible direct check rebuilt the
terminal spike:

```text
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
exit 0
```

Final gate invariants:

```text
Idris 2, version 0.8.0
seeded package closure:
  207/207: Building DGamma.CP4ProgressProof
  exit 0
src/DGamma/CP3.idr blob:
  2c697e532e83989de8591fa6a4378747c6a501c0
production diff from 34b21c9 over src/ + dgamma.ipkg:
  empty (0 bytes)
adjacentSwapSuffixSpike full definition:
  1470 bytes
  SHA-256 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
adjacentSwapSuffixSpike statement prefix:
  1154 bytes
  SHA-256 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

No full build-tree deletion or from-scratch rebuild occurred. Only terminal
TTC/TTM files were removed before seeded checks, one `idris2` process ran at a
time, and orphan process groups were terminated before each fresh invocation.
