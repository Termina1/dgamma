# Revision-23 corrected internal fixture audit

Authorized base: `cp5-thm73-scoping@3c59d9b`.

## 1. Pair selection — fixed before implementation

The selected local pair is **L-Begin 1 / L-Begin 2**, after the globally empty
initial state has executed the fixed external prefix

```text
OInsert 1 Root emptyComponent
OInsert 2 Root emptyComponent
```

and before the checked suffix

```text
LAdvance 1
LAdvance 2
```

Both selected actors are distinct. Both L-Begin transitions are lifecycle nodes,
so they are internal by action shape on both source and moved sides. This is the
exact O19 opening/opening Cartesian case already authenticated by
`genuineO19BeginBeginExternalProducer`; it does not use the weaker stable O17
root/internal cases.

The ordered root-external subsequence is therefore unchanged:

```text
OInsert 1 Root; OInsert 2 Root
```

The adjacent pair and its moved pair contribute no root observation. Pair-local
`SameExternalOrchestration` must be built by four internal-skip constructors
from the checked L-Begin transitions and moved-action equalities. It will not be
accepted as a caller premise.

### Why this replaces R20

R20 selected two distinct root insertions. That pair is a genuine local O5
commutation but is not an O6 splice preserving the immutable external sequence.
It also ended with two fresh clean inactive roots and was therefore not quiet.

The revision-23 component has empty dependencies, provisions, and program. Each
checked L-Begin records the executable empty target view and enters
`Reloading []`. Each checked L-Advance then takes the L-Finish branch and leaves
the actor `Active` at the same target. Consequently the intended source endpoint
is quiet and has no failed fibers without retirement, removal, or failure-shaped
capital.

No auxiliary retirement is needed. If later fixture changes introduce one, every
retirement must be an actual checked trace head and must participate in all
alignment, discipline, totality, occurrence, and replay evidence.

## 2. Construction obligations

Implementation proceeds in this order:

1. define the concrete empty initial state, the two checked root insertions, the
   checked L-Begin/L-Begin pair, and checked L-Advance/L-Advance suffix;
2. construct pair-local external order from internal classifications;
3. construct the source `ReplayInvariantBundle` from executable evidence:
   alignment, registration discipline, initial/final well-formedness, computed
   quietness and no-failure, trace totality, and trace independence;
4. derive provenance, rank, parent-rank, acyclicity, support well-foundedness,
   and support/active matching through the existing checked-trace theorems;
5. only after the source bundle authenticates, construct the local diamond and
   replay the exact suffix through its relational endpoint;
6. transport target fields strictly in `ReplayInvariantBundle` declaration
   order, quietness first after the already-closed first five fields.

A caller-selected quietness, no-failure, domain relation, external relation,
independence witness, or later endpoint invariant is forbidden.

## 3. Current status

Pair selection and rationale are fixed by this commit **before Idris fixture
construction begins**. The source bundle is not yet claimed. The combined
A/B/C/D package remains prepared and unissued.
