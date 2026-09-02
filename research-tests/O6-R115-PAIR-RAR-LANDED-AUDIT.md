# O6 revision 115: ratified pair RAR landed

Shift #117 (overall #171) landed only the revision-108 ratified private unit.
`PairAlignedIdentity` consumes source alignment once with quantity-0 checked
proofs; `lookupStateBackward` transports only the Iter/Iter second lookup;
`equalOwnerPairRARFromOwnedMovedIdentity` patterns both moved `Fired` values and
their alignment directly; `equalOwnerPairRAR` is the thin R102 wrapper. Source
and moved checked proofs remain distinct, endpoints remain distinct, and no
transition let alias, proof irrelevance, dictionary equality, or frozen surface
change is used.

Fresh attempt 1 passed with visible CP5 rebuilding. Field 9 and later fields were
not changed in this unit. Holes remain 20, split 6/4/8/1/1.

```text
R115_PAIR_RAR=passed
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```
