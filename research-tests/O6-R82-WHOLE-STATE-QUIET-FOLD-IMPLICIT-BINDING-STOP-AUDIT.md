# O6 revision 82: whole-state quiet fold implicit-binding stop

## Scope

Grind shift #90 (overall #144) resumed from reviewer-accepted revision 81 at
`fe09480`. It attempted only the newly authorized top-level finite quietness
fold. No wrapper, later bundle field, or assembly unit was opened.

The fold exhausted its fresh three-attempt budget before body elaboration and
was removed. The revision-80 lifecycle/fiber quietness chain remains frozen and
unchanged.

## Attempts

Every attempt cleared CP5 TTC/TTM and visibly rebuilt
`DGamma.CP5ConfluenceLocalDiamondSpike` directly from source.

1. Every premise and result used the authorized checked CP4 whole-state form:

   ```idris
   the (SystemState name key value world error)
     (MkSystemState concreteWorld
       (MkCoeffectContext concreteEntries concreteUnique))
   ```

   Registries were projected from that typed whole state. There were no
   as-pattern aliases and no `where` blocks. The declaration still failed while
   binding a generated dependent `value` implicit.

2. The pre-authorized fallback introduced private top-level `quietFoldState`.
   Its result is a `SystemState name key value world error` and its body alone
   contains the literal `MkSystemState`/`MkCoeffectContext`. The fold signature
   and body used only applications of that auxiliary, so no nested constructor
   application remained in the fold signature. The helper itself checked, but
   the fold declaration again failed while binding a generated dependent
   `value`, now with both generated `key` and `value` visible in the diagnostic.

3. The remaining `quietEntryFor` result predicate received explicit
   `{name}`, `{key}`, `{value}`, `{world}`, and `{error}` arguments. The same
   generated `key`/`value` binding failure remained at the declaration.

Representative diagnostic:

```text
While processing type of pointwiseQuietEntriesTrueExplicit.
Can't bind implicit ... {value:...} of type
  (... : ?...{key:...}[...]) -> Type
```

The failure is therefore not in the recursion, target membership, lookup,
control transport, fiber relation, or Boolean conjunction. Those body stages
were already reached in revision 80. Revision 82 isolates the current failure
to generated implicit inference at the fold type boundary.

## Next representation cure

A newly authorized attempt should remove generated implicits from this boundary
entirely:

1. Give `quietFoldState` **ordinary explicit type arguments** rather than hidden
   arguments:

   ```idris
   quietFoldState :
     (name, key, world, error : Type) -> (value : key -> Type) -> ...
   ```

   Every application then starts
   `quietFoldState name key world error value ...`.
2. Lift the result predicate into a second private executable auxiliary with the
   same ordinary explicit type arguments, for example
   `quietFoldEntryPredicate name key world error value nameEq keyEq ...`.
   State the fold result only as
   `allRecursive (quietFoldEntryPredicate ... rightEntries rightUnique) entries
   = True`; do not mention `quietEntryFor`, `registry`, a state constructor, or
   a hidden type argument in the fold result.
3. If needed, similarly lift the concrete lookup equation into a private
   explicit-argument family before attempting the recursive proof.

This preserves executable predicates and literal constructors in producer
bodies while eliminating the exact hidden dependent arguments Idris refuses to
bind.

## Status

- fields 1–5: **closed and frozen**;
- lifecycle/fiber quietness transport chain: **closed and frozen**;
- field 6 finite fold: **not retained**;
- field 6 wrapper: **not opened**;
- fields 7–15: **not opened**;
- result/body assembly: **not opened**;
- holes: **20**, split **6/4/8/1/1**;
- accepted remaining band: **held at 1–12 shifts**.

No frozen interface, production file, CP3, package input, hole, postulate,
escape hatch, public surface, or detached caller premise changed.
