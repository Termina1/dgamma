# O6 revision 34: remove negative, begin source, and provider-selection boundary

## Scope

All work remains private to the research O6 implementation. The frozen
`adjacentSwapSuffixSpike` declaration, sealed replay spine, opaque adjacent
result, hole manifest, production tree, package, and immutable CP3 theorem are
unchanged.

## O-Remove: conditional negative trigger fired

The corrected staged normalizer was retried with explicit dependent arguments
and `sym childView` in the successful `False` branch. The same revision-33 wall
recurred immediately:

```text
Can't solve constraint between:
  hasChildIn actor (source .bindings)
and:
  False.
```

Per the revision-33 rule, no further O-Remove attempt was made. The dedicated
expected-failure module
`DGamma.R34RemoveChildOrientationNegative` now reproduces that exact diagnostic
at `sym childView`. Its required declaration and diagnostic fragment are part
of the authoritative runner. Inventory changes from 41 to 42 negatives and
from 86 to 87 tracked Idris tests; positives and successful-build markers do
not change.

Commit: `bc9e56a` — pin remove child proof orientation failure.

This is still a proof-elaboration orientation wall, not an uninhabited action or
new-capital obligation. O-Remove remains stopped until the pinned failure is
resolved by a genuinely different source representation.

## L-Begin source closure

`beginSourceIngredientsPointwise` now calls public `lifecycleOwnerPresent`
before inspecting any owner lookup and passes the original raw `applyAction`
equation to `foreignBeginPlanView`. The existential owner, exact lookup, plan
view, dependent component/table/view indices, and caller endpoint are retained
together without a refining local `with`.

Commit: `0909416` — derive begin source view before lookup refinement.

The remaining L-Begin semantic producer depends on order-independent target
resolution; its source decomposition is no longer blocked.

## Provider-selection foundations

The following constructive chain now elaborates:

1. `providerOfSoundCandidateTrue` turns `ProviderOfSound` into the exact runtime
   candidate Boolean using explicit `valueFromProvider` indices.
2. `pointwiseRegistryPairwise` extracts pairwise provision disjointness from the
   executable well-formedness conjunction.
3. `LocatedProviderCandidate` seals a fiber lookup, registry entry, true
   candidate, and declared provision together.
4. `selectedProviderCandidate` packages that record from an exact provider
   selection.
5. `pointwiseTransportProviderCandidate` moves a located candidate through
   pointwise controls plus actor-table effect relation.
6. `locatedProviderCandidateSelectsSome` reconstructs a concrete provider scan
   from any located true candidate.
7. A local constructive pairwise-provision proof establishes provider-name
   uniqueness without assuming list order; `locatedProviderCandidatesSameName`
   packages its record-level consumer.

Commits:

- `8eba4cc` — extract true candidates from provider soundness;
- `dd5d181` — extract pairwise provision wellformedness;
- `51a0ad9` — package selected provider candidates;
- `a2b48e9` — transport located provider candidates pointwise;
- `e37dbb5` — derive provider selections from candidate witnesses;
- `2e863bf` — prove provider-name uniqueness from pairwise provisions;
- `3931e2e` — identify pairwise provider candidates by name.

The final `pointwiseProviderOfSame` assembly was attempted three times and
reverted. It reached all four `Maybe` branches, existence contradictions, and
the pairwise name-equality branch. The last diagnostic is only the with-proof
orientation at the first selected target:

```text
Can't solve constraint between:
  Just rightName
and:
  providerIn wanted (registryFibers (registry right)).
```

The failing expression used `(sym rightSelected)`; the branch proof already has
the required `providerOf ... = Just rightName` orientation. The next bounded
attempt must pass `rightSelected`/`leftSelected` directly to
`selectedProviderCandidate`, while absence contradictions use
`sym leftSelected` or `sym rightSelected` before the reconstructed `Just` proof.
No partial equality theorem was retained.

## Safe boundary

No new complete semantic head closes in revision 34. O-Remove is pinned and
stopped. L-Begin's source view is closed but its target resolution awaits the
last provider-selection assembly. Consequently L-Divert/L-Leave full producers
were not opened, and L-Unload/L-Advance were not started.

Fully closed heads remain O-Insert and O-Retire. Six semantic heads, whole-suffix
RAR/ordinal composition, and adjacent-result assembly remain. Holes stay 20,
split `6/4/8/1/1`. The O6 estimate stays **18–34 shifts**: the provider-selection
capital is nearly assembled, but no head closed and the pinned O-Remove wall
remains fully charged.
