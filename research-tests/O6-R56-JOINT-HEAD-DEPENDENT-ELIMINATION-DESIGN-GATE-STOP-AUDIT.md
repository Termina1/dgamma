# O6 revision 56: joint-head producers closed; dependent elimination design gate

## Scope

Shift #64 (overall #118) resumed from revision-55 HEAD `2ff3140` under the
probe-first joint-record authorization. Both probe directions passed before any
real implementation. The private joint GADT and all eight action-specific
builders then compiled and were committed in the required order. The first real
dependent elimination attempt produced new coverage information: the same joint
package that is exhaustive under a non-dependent probe codomain is not accepted
as covering when its result is `PointwiseRelationalHeadReplay` indexed by the
packaged source transition.

The accepted gate explicitly required an immediate stop-audit if coverage still
failed through the joint package. The eliminator was therefore fully reverted
after this first exact failure; no representational iteration used the two
remaining budget slots. The probe, joint type, and all builders remain committed.
No whole-suffix composition, final assembly, frozen signature, production file,
or research hole changed.

## Probe-first evidence — `06d38f5`

`research-tests/DGamma/R43JointAlignedHeadProbePositive.idr` defines an isolated
single-constructor dependent joint package with:

- the exact source `Fired` index;
- its stored `nameEq` and `keyEq` dictionaries;
- its exact checked equation;
- the exact `AlignedStep ... NoTransitions AlignedEnd` singleton.

### Direction (a): construction

The probe supplies total builders for all eight action constructors:

- `r43BuildInsert`;
- `r43BuildRetire`;
- `r43BuildRemove`;
- `r43BuildBegin`;
- `r43BuildAdvance`;
- `r43BuildDivert`;
- `r43BuildLeave`;
- `r43BuildUnload`.

Every builder uses only a checked equation and the dictionaries/actions already
held by the structural spine clause. The first probe attempt lacked the explicit
`Decidable.Equality` import. The second localized implicit endpoint inference and
quantity of the generic constructor helper. On attempt 3, explicit
`{before} {afterState}` indices and an unrestricted constructor helper made all
eight builders total.

### Direction (b): elimination

`r43EliminateJoint` performs one pattern match on the joint package and covers
all eight action constructors. It compiled in the same successful attempt. The
probe was added to the authoritative positive suite.

Thus the representation is constructible and its action split is exhaustive
under a non-dependent codomain.

## Retained real implementation

### Joint package — `b77c1a7`

Private `PointwiseAlignedHeadJoint` introduces source action, tag, exact checked
proof, source dictionaries, and aligned singleton through one GADT constructor.
No constructor or field is exported.

### Orchestration and begin builders — `2f38b65`

The generic constructor helper and four producer-owned builders compiled on
attempt 1:

- `buildPointwiseInsertJoint`;
- `buildPointwiseRetireJoint`;
- `buildPointwiseRemoveJoint`;
- `buildPointwiseBeginJoint`.

Each fixed-tag builder derives and eliminates the exact tag equality before
packaging. The L-Begin source lookup rewrite remains internal.

### Lifecycle builders — `0095dde`

The remaining four builders compiled on attempt 1:

- `buildPointwiseAdvanceJoint` preserves its observed runtime tag;
- `buildPointwiseDivertJoint` consumes `pointwiseDivertTag`;
- `buildPointwiseLeaveJoint` consumes `pointwiseLeaveTag`;
- `buildPointwiseUnloadJoint` consumes `pointwiseUnloadTag`.

The three lifecycle source observations remain sealed behind quantity-0 tag
helpers. All eight builders return only the private joint package. Containing
module and R16 passed after every implementation commit.

## Exact dependent-elimination failure

The real eliminator had the precise codomain:

```idris
PointwiseRelationalHeadReplay ... sourceStep replayedBefore
```

and eight branches, each matching one action inside a single
`MkPointwiseAlignedHeadJoint`, re-establishing its fixed tag where necessary,
and delegating to the corresponding already-closed head. Every branch body was
typed in the source text; totality rejected the declaration with approximately
140 indistinguishable uncovered cases:

```text
Error: replayPointwiseJointHead is not covering.
Missing cases:
    replayPointwiseJointHead _ _ _ _ _
    replayPointwiseJointHead _ _ _ _ _
    ...
```

Unlike revision 55, the uncovered cases expose no action constructor, tag, or
dictionary shape at all. Unlike the positive probe, the real codomain depends on
both the joint package's source transition index and `replayedBefore`. Idris
accepts the single action elimination for a non-dependent result but loses the
constructor refinement while checking exhaustivity of this dependent codomain.
This is new information about the exact result index, not a recurrence of the
separate-scrutinee failure.

Per the authorized rule — if coverage still fails through the joint package,
stop with the exact uncovered case and hold a further design gate — the
eliminator was reverted immediately. No specialized-constructor variant,
non-dependent envelope, coverage pragma, partiality, or second representation
was attempted.

## Gate question for the next representation

Any next design must preserve the committed builders and private boundary while
making the dependent result total. Candidate directions require explicit
approval, for example:

1. return a private existential envelope containing the source-indexed
   `PointwiseRelationalHeadReplay`, then project it only where the source index is
   definitionally fixed by the spine; or
2. refine the joint GADT into eight constructors whose result indices already
   fix the action and fixed tag, avoiding a second action split in the dependent
   eliminator.

Neither candidate is implemented or endorsed here. No dictionary identity,
UIP, caller-supplied checked proof, or detached replay capital is admissible.

## Status

- probe directions: **2/2 passed and tracked**;
- private joint type: **closed**;
- action-specific builders: **8/8 closed**;
- dependent joint eliminator: **STOP; fully reverted after exact coverage
  failure**;
- generic spine recursion: **typed, not instantiated**;
- whole-suffix RAR/ordinal composition: **unopened**;
- final adjacent assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- estimate: **3–15 shifts held pending the required dependent-elimination design
  gate**.
