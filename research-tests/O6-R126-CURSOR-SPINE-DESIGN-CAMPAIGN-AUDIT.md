# O6 revision 126: cursor/spine constructor-introduction campaign audit

## Scope and coordinate

Design-only shift #124 (overall #178) started from accepted clean HEAD
`c6d0a2d7c9dfe264b763c847644f59a7d036361f`. It opened only the authorized
exact renamed copy of `CP5ConfluenceLocalDiamondSpike.idr` at
`research-tests/DGamma/R48CursorSpineCopyProbePositive.idr`. No retained proof
source or frozen interface was edited.

The disposable source had SHA-256
`af5ce37963ee63dad39d64bd2c498353bdf02262083e3e73c1159221f568b445`
and size 1,537,962 bytes at the final failed attempt. The source and all related
TTC/TTM artifacts were removed before this audit was retained.

## Probed representation

`ProbeCursorSpine` was indexed by:

- the exact prefix trace;
- the exact moved-right and moved-left transitions and suffix;
- the target action;
- the complete original `LocatedActionOccurrence`; and
- its exact ordinal.

The constructors represented all four terminal regions directly:

- `ProbeCursorPrefixHere`;
- `ProbeCursorMovedRight`;
- `ProbeCursorMovedLeft`;
- `ProbeCursorSuffix`.

The recursive constructor `ProbeCursorPrefixLater` did **not** accept either the
whole or tail occurrence as an independent argument. Its primitive fields were:

- one shared `actionBefore`/`actionAfter` pair;
- `prefixHead` and `prefixTail`;
- `tailBefore`, the exact located transition, and `tailAfter`;
- the exact action equation;
- one tail decomposition; and
- a recursively produced cursor indexed by the constructor-built tail
  occurrence.

Its result built the whole occurrence definitionally by prefixing that same
shared tail cursor. This is the constructor-introduction representation required
by the revision-125 ruling.

Two consumers were also declared in the disposable source:

- `probeCursorExactOrdinal`, a single cursor elimination with recursive lifting
  by `cong S`;
- `probeCursorRegion`, returning exactly prefix, moved-right, moved-left, or
  suffix.

Because the producer failed, the module did not typecheck and these consumers do
not count as validated proof artifacts.

## Attempt history

### Attempt 1 — infrastructure

Matching both an empty prefix and an empty occurrence-before trace in one clause
forced two separately named endpoint patterns to unify:

```text
Suggestion: Use the same name for both pattern variables, since they unify.
```

This was the known nonlinear `NoTransitions` elaboration boundary, not a
semantic result.

### Attempt 2 — infrastructure

The base-pair helper was moved out to eliminate the nonlinear pattern, but was
declared after the recursive prefix producer. Idris rejected the forward name:

```text
Undefined name probeCursorAtPairFields.
```

No cursor semantics were tested by this attempt.

### Attempt 3 — semantic stop

After moving the helper before the producer, the GADT constructors and base-pair
classifier elaborated. The recursive `PrefixLater` construction failed at the
exact head identity:

```text
Mismatch between: prefixHead and beforeHead.
```

The complete mismatch showed the requested result indexed by

```idris
MoreTransitions prefixHead prefixTail
```

but the original occurrence remained indexed by

```idris
MoreTransitions beforeHead beforeTail
```

Even after eliminating the whole occurrence decomposition with `Refl`, Idris
did not identify the two independently stored `Transition` terms. The recursive
constructor can share the state pair and all tail fields, but it cannot make the
prefix-owned head token and the occurrence-before-owned head token
definitionally identical after they have already been introduced separately.

## Countermodel-style boundary analysis

Revision 125 showed that two located-occurrence records cannot be glued after
construction because their existential intermediate states differ. This
campaign moved every occurrence field into one constructor, but a strictly
earlier split remains: the caller supplies the prefix trace and the original
occurrence independently. Consequently the recursive producer sees two head
transition tokens:

1. `prefixHead`, obtained by eliminating the supplied prefix;
2. `beforeHead`, obtained by eliminating the occurrence's supplied before
   trace.

The global decomposition proves equality of the completed dependent traces, but
eliminating that equality does not provide definitional identity of these
already stored head tokens at the recursive constructor result. A cursor that
accepts neither occurrence independently solves the endpoint/tail problem, but
cannot also solve independently supplied prefix-head identity.

Thus the cursor/spine constructor-introduction representation, under the frozen
input interface, fails at its essential recursive lift. The exact ordinal and
four-region consumers remain blocked because no total producer can inhabit the
cursor for arbitrary frozen inputs.

Per the binding ruling, this is a semantic stop. The potentially different route
of avoiding a four-region view and consuming the retained positional occurrence
and suffix-embedding foundations directly was **not** probed. It requires a new
reviewer decision.

## Honest markers

No success marker was emitted. The campaign result is:

```text
R126_CURSOR_SPINE_GADT=constructor_surface_elaborated
R126_CURSOR_RECURSIVE_PRODUCER=semantic_failure
R126_CURSOR_EXACT_ORDINAL=not_validated
R126_CURSOR_FOUR_REGION=not_validated
R126_DISPOSABLE_PROBE_REMOVED=passed
R126_RETAINED_DESIGN=not_ratified
```

## Status

- cursor/spine constructor surface: **elaborated through base cases**;
- recursive prefix lift: **semantic failure on exact head-token identity**;
- exact ordinal consumer: **declared but not validated**;
- four-region classifier: **declared but not validated**;
- retained proof edits: **none**;
- direct positional action-origin alternative: **unopened pending ruling**;
- holes: **20**, split **6/4/8/1/1**;
- frozen fields 1–15, pair RAR, external-order proof, occurrence foundations,
  revision-21 surfaces, CP3, production package, and suffix hole interface:
  **unchanged**.
