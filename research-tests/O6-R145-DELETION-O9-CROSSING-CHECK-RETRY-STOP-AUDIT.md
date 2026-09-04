# O6 R145 — Deletion O9 crossing-check retry stop audit

## Scope and verdict

**Verdict: inconclusive after the dedicated 3/3 fixture budget; route A/B is not
selected and O9 remains parked at 0/3 body attempts.**

R145 began at exact commit `9232660a35129a45419c5cfc1a8a97985e620610`
on `cp5-thm73-scoping`, with only the permitted untracked `paper/` directory and
`review-o6-body-adversarial.md`. Production remained frozen. The retry copied
the exact R137 ratification import sequence and module placement, including the
direct `Decidable.Equality` import that was absent from the terminal R142
attempt.

The disposable module was
`research-tests/DGamma/R145O9CrossingCountershapeRetry.idr`. It targeted the
standing concrete shape: a consumer opens and commits `LinkKey -> ActorA`; the
provider retires and leaves while that consumer remains Reloading; the provider
then attempts `LUnload`, which should be rejected by the `relied` guard before a
later same-name provider activation can be inserted and begun.

## Attempt accounting

The fresh fixture budget is exhausted at **3/3**.

1. **Attempt 1/3.** The imported R137 dictionary and state constants remained
   opaque to evaluator reduction, and the transitive import did not put
   `MkCoeffectContext` in scope. The intended retire/leave/unload equations did
   not elaborate.
2. **Attempt 2/3.** Local `%search` dictionaries were added under the required
   direct `Decidable.Equality` import, but the coeffect-context constructor was
   still unavailable without its direct defining import. Imported state/fiber
   opacity continued to block the equations.
3. **Attempt 3/3.** A fully local two-stage fixture was assembled under the same
   R137 header plus the direct `DGamma.Coeffects` defining import. Its provider
   retirement, provider leave, retained `relied = True`, and terminal
   `LUnload = Nothing` declarations elaborated far enough to emit no
   diagnostics. The sole remaining error was the source consumer `LBegin`
   equality: `targetFiber r145ConsumerFresh ...` did not normalize to the
   explicitly constructed `ProviderView ActorA EmptyView` through the local
   component/spec boundary. Because the module as a whole did not typecheck,
   those later declarations are not retained as evidence.

The final exact diagnostic was:

```text
Can't solve constraint between:
  Just (LBeginTag, r145ConsumerOpenState)
and
  case targetFiber r145ConsumerFresh (registry r145BeforeConsumerState) of ...
```

This is again a mechanical fixture failure rather than a checked semantic
answer. In particular, the fact that the last spelling reduced every later
obligation to one opening-resolution equation is not promoted into proof of
route B. The 3-attempt rule forbids a fourth producer-owned target-equation
repair in this unit.

## Consequence

The disposable source and terminal TTC/TTM were removed. No crossing fixture,
helper, changed predicate, scoped-to-raw coercion, or hole body survives. The
standing R142 route remains unresolved:

- route A still requires a checked overlapping activation countershape; and
- route B still requires a checked operational exclusion theorem or a complete
  checked evaluator refutation.

Therefore no O9 helper capital, research Lemma-72 analogue, or later
DeletionChain body is opened in R145. The research-hole census remains **13**,
split **CanonicalSort 2 / CrossTrace 4 / DeletionChain 6 / LocalDiamond 0 /
RenamingComposition 1**.
