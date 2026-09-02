# O6 revision 119: replay fields 10–15 complete

`AdjacentInvariantReplay` now packages the exact target suffix, producer-owned
whole field-9 correspondence, endpoint, suffix seal, and complete target
`ReplayInvariantBundle`. `produceAdjacentInvariantReplay` consumes
`AdjacentAlignedPointwiseReplay` once and populates provenance, protocol ranks,
parent-rank ordering, precedence acyclicity, support well-foundedness, and
support/active agreement from the frozen field-10–15 foundations.

Attempt 1 exposed a forbidden nonlinear `targetTrace`/`Refl` constructor
pattern. Attempt 2 made the package's trace definitionally equal to the required
append trace and eliminated the producer-owned decomposition separately; it
passed visibly fresh CP5.

```text
R119_FIELDS_10_15=passed
R119_REPLAY_BUNDLE=passed
FIELDS_10_15=complete
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

O6 body assembly was not opened. Holes remain 20, split 6/4/8/1/1.
