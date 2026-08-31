# O6 revision 83: explicit-Type fold closes; wrapper aggregation stop

## Scope

Grind shift #91 (overall #145) resumed from reviewer-accepted revision 82 at
`1baf9c5`. It executed the last authorized explicit-Type-argument cure for the
field-6 finite fold, then opened only the separately authorized one-clause
wrapper. No field 7–15 or result/body assembly unit was opened.

## Retained fold

The explicit-Type representation closes constructively at `08be6e7`.

Retained private executable auxiliaries:

- `quietFoldStateExplicit`, whose `name`, `key`, `world`, `error`, and dependent
  `value` are ordinary explicit arguments;
- `quietFoldEntryPredicate`, likewise fully explicit and executable;
- `quietFoldLookupEquation`, an explicit-argument family sealing the concrete
  target lookup equation;
- `pointwiseQuietEntriesTrueExplicit`, whose result mentions only
  `allRecursive (quietFoldEntryPredicate ...)` and contains no generated hidden
  type argument at its boundary.

The recursive producer carries exact membership from the current suffix into
the original target entries, reconstructs the exact target lookup, obtains the
source fiber through symmetric `ControlEquivalent`, applies the retained
`pointwiseQuietFiberTrue`, and recurses with `There`. All proof premises and
locals are quantity 0.

Attempt history under its fresh budget:

1. The complete explicit representation elaborated through the previously
   blocked declaration and entire recursive body, then reported only that
   `quietFiberFromState` was not in scope.
2. Adding the direct research-only import of
   `DGamma.CP4SupportQuiescence` and explicitly passing all of that theorem's
   type arguments produced a visible successful CP5 rebuild. R16 then passed.

This closes the repeated revision-80/81/82 fold wall. The binding design
escalation is not triggered because the authorized explicit-Type representation
succeeded.

## Wrapper semantic stop

The one-clause state-pattern wrapper had its own unit boundary. It was removed
on the first unification wall class, per the binding semantic-stop rule.

1. Directly returning the explicit fold proof failed because Idris would not
   identify the executable auxiliary predicate as a function with
   `quietEntryFor`, even though both are pointwise definitionally equal.
2. A structural conversion helper was tried. Its recursive call incorrectly
   shrank both the current list and the registry owned by the predicate. Idris
   correctly rejected the resulting index change:

   ```text
   Mismatch between: tailUnique and UniqueCons headFresh tailUnique.
   ```

The wrapper unit was removed immediately after that unification death. This is
not a failure of the retained fold and not a semantic counterexample. It
identifies the exact aggregation index required next: keep
`registryEntries/registryUnique` fixed while recursing over a separate
`currentEntries` list.

## Exact next wrapper shape

A private structural converter should take:

- explicit `registryEntries` and `registryUnique`, held fixed;
- a separate `currentEntries` recursion argument;
- `allRecursive (quietFoldEntryPredicate ... registryEntries registryUnique)
  currentEntries = True`;

and return:

- `allRecursive (quietEntryFor ... (registry (quietFoldStateExplicit ...
  registryEntries registryUnique))) currentEntries = True`.

Both head predicates reduce after the head entry is supplied; the recursive
call changes only `currentEntries`. The one-clause state-pattern wrapper then
instantiates `currentEntries = registryEntries`, yielding `quiet rightState =
True` definitionally.

## Status

- fields 1–5: **closed and frozen**;
- lifecycle/fiber quietness semantic chain: **closed and frozen**;
- explicit finite target-entry fold: **closed and retained**;
- field-6 wrapper: **open at fixed-registry aggregation conversion**;
- field 6 as a bundle field: **not yet complete**;
- fields 7–15: **not opened**;
- result/body assembly: **not opened**;
- holes: **20**, split **6/4/8/1/1**.

The principal repeated fold wall is now closed, so the remaining implementation
estimate is provisionally narrowed from **1–12** to **1–11 shifts**, subject to
reviewer acceptance.

## Isolation

The frozen 1183-byte spike interface, revisions 19–21, fields 1–5, revision-80
quietness chain, registration/yield/generator/RAR capital, production `src/`,
`dgamma.ipkg`, and CP3 remain unchanged. The only research code change is the
private explicit fold plus one direct research dependency import. No new hole,
postulate, escape hatch, public surface, detached caller premise, or package
input was added.
