# O6 revision 90: LAdvance injectivity closed; actor projection stop

## Scope

Grind shift #98 (overall #152) resumed from accepted revision 89 `bb37615` and
opened only the authorized actor-index ladder. Constructor injectivity closed.
The next bare actor-equality projection exhausted its own three-attempt budget
at the dependent endpoint identity carried by `OccursIn` and was removed in
full. The locator, correlated fallback package, family wrapper, RAR chain,
fields, and assembly were not opened.

## Retained capital

`lAdvanceActorInjective` is retained at `e7a7271`. It passed on its second fresh
attempt after replacing unsupported expression ascriptions with explicit
`the (Action name key value world error) ...` terms. Its fully explicit,
parenthesized statement proves:

```text
LAdvance leftActor = LAdvance rightActor -> leftActor = rightActor
```

by constructor elimination (`Refl`). It compares actions only and introduces no
transition-dictionary identity.

## Removed unit

The removed `singletonAdvanceStageActorSame` attempted the accepted bare
projection:

```text
cong transitionAction (singletonOccursSelected occurs)
```

followed by `lAdvanceActorInjective`.

The three fresh deaths were statement/index-shape failures:

1. a singleton `Fired {before} {afterState}` shorthand allowed a fresh implicit
   endpoint in the dependent occurrence equality;
2. changing the trace head to exact
   `{before = before} {afterState = afterState}` still left the hidden endpoints
   of the eliminated `StageFromAdvance` occurrence independently named, so
   `singletonOccursSelected occurs` reported two visually identical transition
   equalities with distinct hidden `afterState` indices;
3. attempting to pin `StageFromAdvance {before = before}
   {afterState = afterState}` in the left-hand pattern was rejected as a
   nonlinear inaccessible implicit pattern.

The retained diagnostic class is:

```text
Fired stageNameEq stageKeyEq (LAdvance selected) ... =
Fired nameEq keyEq (LAdvance actor) ...
```

where the printed transitions are identical but their hidden endpoint indices
are not accepted as the same declaration-local variable. This occurs before
action projection; it does not challenge LAdvance injectivity and does not
justify dictionary equality.

Per unit budget, the entire uncommitted equality helper was removed.

## Authorized ladder interpretation / next unit

The complete ladder has **not** exhausted: the correlated-package fallback from
the revision-89 ruling remains unused. The bare equality route is now closed.
The next shift should consume the pre-authorized fallback, not attempt a fourth
bare projection and not invent a fifth cure.

The exact package design should avoid equality of whole dependent transitions:

1. Define a `LocatedSingletonAdvanceActor` package indexed by the original
   target stage. It owns both the exact stage term and `selected = actor`.
2. Build it from one `StageFromAdvance` elimination and
   `viewConsStageOccurrence occurs`:
   - `ConsStageOccursHere` makes the stage occurrence definitionally the exact
     singleton head and should permit `Refl` for actor equality;
   - `ConsStageOccursLater _ later` is eliminated by `noOccurrenceInEmpty
     later`.
3. Eliminate this package once in the locator. In the actor-equality `Refl`
   branch, keep the package-owned stage correlated while exposing its exact
   fiber/lifecycle payload; then use the frozen lookup transport and delegate to
   `locateSingletonAdvanceStageReplay`.

This is the authorized joint-introduction pattern. It deliberately replaces
`singletonOccursSelected` with the already checked cons-occurrence view, so no
whole-transition equality and no stored `DecEq` equality cross the boundary.
If this correlated package plus its single locator consumer exhausts its
fresh-budget ladder, the stated escalation boundary applies: stop and open a
design-only campaign on singleton stage representation; no fifth cure.

## Status

- identity prefix RAR: **closed and frozen**;
- singleton advance lookup transport: **closed and frozen**;
- LAdvance actor injectivity: **closed**;
- bare stage actor equality: **removed / superseded by package fallback**;
- correlated fallback package and locator: **unopened**;
- family wrapper and singleton RARs: **unopened**;
- moved-pair and whole RAR / field 9: **unopened**;
- fields 1–8: **closed and frozen**;
- fields 10–15 foundations: **closed and frozen; population pending**;
- occurrence fold/result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The accepted remaining band is held at **1–10 shifts**. The body-closure review
boundary was not reached.

## Isolation

Production `src/`, `dgamma.ipkg`, CP3, the frozen 1183-byte adjacent interface,
revision-21 surfaces, prefix RAR, lookup transport, fields 1–8, and fields
10–15 foundations are unchanged. No escape hatch, hole, postulate, public
surface, or failed equality helper was retained.
