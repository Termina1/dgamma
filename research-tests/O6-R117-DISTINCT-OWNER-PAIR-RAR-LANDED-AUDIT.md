# O6 revision 117: distinct-owner pair RAR landed

Shift #118 used the reviewer-authorized fresh budget to land the catalogued
distinct-owner shape against frozen `adfd6dd` cross-position locators.

- Attempt 1 used explicit indices, top-level lookup calls, nested equality
  elimination, and the actor/action-owner bridge, but retained the disposable
  probe's pre-layout branch indentation and failed parsing.
- Attempt 2 corrected only that branch layout and passed visibly fresh CP5.

The private producer covers all four `CandidateRegistrationSwapSafety` cases.
Activation lookup equality is derived only by `transitionForeignLookup` and the
explicit owner inequality; orchestration singleton RARs need no lookup premise.
The two singleton correspondences are consumed cross-positionally by the frozen
`crossPairRelationalReplayCorrespondence`. No nonlinear pattern, transition let
alias, proof irrelevance, dictionary equality, or frozen/public surface change
is used.

```text
R117_DISTINCT_OWNER_PAIR_RAR=passed
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

Field 9 and later fields were not opened in this unit. Holes remain 20, split
6/4/8/1/1.
