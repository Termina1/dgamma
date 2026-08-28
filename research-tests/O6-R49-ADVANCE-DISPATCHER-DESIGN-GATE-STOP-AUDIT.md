# O6 revision 49: L-Advance dispatcher design-gate STOP-AUDIT

## Scope

Shift #57 began at accepted revision-48 HEAD `49ea7b9` and exercised the final
authorized localized budget for the private exhaustive L-Advance dispatcher.
No frozen signature, production file, caller boundary, retained generator/RAR
capital, or hole changed.

## Ratified representation

All attempts used the ratified revision-48 shape:

- a top-level nonempty helper with every runtime index explicit;
- one producer-owned indexed `RuntimeIteratorOutcomeAgreement`, computed once
  in the sealed eliminator and threaded through every resolution/run split;
- the empty branch and common head packager unchanged;
- no recomputation of runtime agreement after refinement.

## Three-attempt diagnostic

### Attempt 1: indexed agreement reaches yielded-success packaging

The carried agreement removed the replay missing-capability reduction wall and
elaborated through all resolution and runtime-run splits to the successful-yield
packaging branch. Two later local issues remained:

1. inferred erased `undoMaps` lacked a declared type and produced the indirect
   diagnostic:

   ```text
   No type declaration for ... fromInteger.
   ... 0 undoMaps = ...
   ```

2. merely pattern-matching `sym retiredSame` still let elaboration choose the
   target retired index, leaving `sealedSourceFound` at the source flag.

### Attempt 2: typed undo maps and explicit sourceward lookup transport

`undoMaps` received its full `PartialMapsEquivalent` type. Retirement was no
longer left to pattern unification: `sym retiredSame` explicitly transported the
target lookup proof to the retained source retired flag. Both prior errors
cleared.

Elaboration again reached yielded-success packaging. It then needed exact
branch-local names for source/target match equations after `case matches`, and
the transported lookup annotation needed parentheses around its equality type:

```text
Can't solve constraint between: targetMatches ... and False.
Mismatch between: Maybe (Fiber ...) and Type.
```

### Attempt 3: exact match equations; parser stop

The false branch introduced fully typed `sourceFalse` and `replayedFalse`; the
true branch introduced `sourceTrue` and `replayedTrue`. The transported lookup
equality was parenthesized. Before typechecking those changes, Idris consumed
the final attempt on layout beneath the true branch's `case rest`:

```text
Expected '=>' or 'impossible'.
... sourceAfter tag sourceChecked component sourceParent
```

The body line was aligned with the pattern rather than indented beneath it. The
obvious indentation correction was **not compiled**, because the third attempt
was consumed.

The complete top-level helper, eliminator, and branch-local changes were
reverted. No incomplete dispatcher, outer head, or metavariable remains.

## Mandatory design gate

This is the third full budget cycle on the dispatcher. Per the accepted
revision-48 escalation boundary, there may be no fourth localized variation or
continuation of the monolithic helper—even for the final parser correction.

The next work must begin with a dedicated design decision. The candidate is to
split the runtime result into producer-owned sealed eliminators, analogous to
the successful L-Unload architecture:

- one sealed empty-program eliminator;
- one sealed defined-failure eliminator;
- one sealed yielded-result eliminator, internally splitting divert/finish/iter;
- a thin outer head that opens the generic owner once, constructs the indexed
  runtime agreement once, and joins the sealed branch result through
  `packagePointwiseAdvanceHead`.

Each branch package must retain its exact source/target resolutions, runs,
match equation where applicable, maps, and concrete owner indices. None may
become caller-provided or output-shaped capital.

## Status

- generator/stage provenance, singleton RAR, common head packager: **retained**;
- exhaustive runtime dispatcher: **design-gate STOP; fully reverted**;
- semantic families: **7/8**;
- whole-suffix composition: **unopened and gated**;
- adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **7–19 shifts**, held pending the mandatory dispatcher-shape
  decision; no new declaration was retained.
