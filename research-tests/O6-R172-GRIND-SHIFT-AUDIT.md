# O6 R172 — reconnaissance and O14 probe-first grind audit

## Coordinate, authorization and immutable boundary

Required start `0e58c54`, branch `cp5-thm73-scoping`, verified **2026-09-06
11:49:38 UTC**; only allowed untracked `paper/` and byte-frozen adversarial
review. Idris 0.8.0; `%default total`; one compiler at a time, process inspection
before checks. No build tree/TTC seed deletion, production edit, from-scratch
build, subagent, forbidden body or new `with`. No-new-attempt time **15:09:38**,
safe-gate deadline **15:34:38**, timeout **15:49:38 UTC**.

Unit A is committed at **b5d6904**, with all seven full hole statements, exact
last-stop quotes, capital-to-premise routes, ranking and the current debt
register in `O6-R172-NEXT-PHASE-RECON.md` and `THM73-PLAN.md`. Its eight
sequential invocations freshly elaborate each spike once (three other calls
were explicitly cached); all pass, seeded package retains 207/207 modules.
Details and complete frozen SHA values are in that memo.

The supervisor **ACCEPTED b5d6904** and approved O14 probe-first exactly:

> one disposable fully explicit top-level lookupFiber-found ->
> supportedActiveAt = isActive (fiberLifecycle fiber) equation bridge via public
> activePredicateAtFoundQ, ≤3 checks, probe removed (source + TTC/TTM) and
> transcript committed to the R172 audit BEFORE any retained O14 helper.

On PASS, the ruling pre-authorizes an erased producer-owned lookup/rank view
and a simultaneously constructed stable-rank-sort invariant, one declaration
per invocation and immediate checked commit; O14 body only after its invariant
capital is committed. O17 probe-first is only after O14 closes/stops. No surface
revision, O19 body, O21 withdrawal or debt-register implementation this shift.
**No gate-timeout exception was used**: the reply arrived normally.

## P1 — disposable active lookup equation: PASS 2/3

The first probe was genuinely compiled before a retained helper. Command:

```sh
idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R172SupportedActiveLookupEquationProbe.idr
```

Exactly one new declaration. Full final disposable source (not retained as an
Idris module):

```idris
module DGamma.R172SupportedActiveLookupEquationProbe

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4SupportQuiescence
import Decidable.Equality

%default total

0 r172SupportedActiveLookupEquationProbe :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} selected (registry state) = Just fiber) ->
  (supportedActiveAt {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} selected state =
    isActive (fiberLifecycle fiber))
r172SupportedActiveLookupEquationProbe name key world error value nameEq state selected fiber found =
  activePredicateAtFoundQ {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq state selected fiber found
```

### P1-1 — charged infrastructure failure

**12:07:42–12:07:47 UTC**. The first source omitted only the direct
`DGamma.Coeffects` import. Full diagnostics:

```text
1/1: Building DGamma.R172SupportedActiveLookupEquationProbe (research-tests/DGamma/R172SupportedActiveLookupEquationProbe.idr)
Error: While processing type of r172SupportedActiveLookupEquationProbe. Undefined name DGamma.Coeffects.CoeffectSpec.dependencies.

Error: While processing right hand side of r172SupportedActiveLookupEquationProbe. DGamma.CP4SupportQuiescence.activePredicateAtFoundQ is not accessible in this context.

DGamma.R172SupportedActiveLookupEquationProbe:21:3--21:26
 17 |   (supportedActiveAt {name = name} {key = key} {value = value}
 18 |     {world = world} {error = error} @{nameEq} selected state =
 19 |     isActive (fiberLifecycle fiber))
 20 | r172SupportedActiveLookupEquationProbe name key world error value nameEq state selected fiber found =
 21 |   activePredicateAtFoundQ {name = name} {key = key} {value = value}
        ^^^^^^^^^^^^^^^^^^^^^^^

```

The compiler process returned **0 despite the Error diagnostics**. This is
counted as failure **1/3**, not a successful check. The check wrapper is now
explicitly diagnostic-aware in addition to testing exit status. The
`activePredicateAtFoundQ` accessibility diagnostic was secondary to the missing
dependent definition; no visibility edit or production change was made.

### P1-2 — pass

**12:08:14–12:08:19 UTC**, exit 0, no Error diagnostic:

```text
1/1: Building DGamma.R172SupportedActiveLookupEquationProbe (research-tests/DGamma/R172SupportedActiveLookupEquationProbe.idr)
```

Adding the direct Coeffects import makes the **same** fully explicit equation
check through the public theorem. It tests the actual `supportedActiveAt`, not
a manually mirrored case expression or an assumed equality. This discharges
the designated R135 observation spelling probe, not the rank-sort invariant or
O14 body.

The disposable `.idr` and its exact `.ttc/.ttm` outputs were removed; no seed or
other artifact was deleted. Source and logs are reproduced above; `/tmp` copies
are optional telemetry only. No retained research helper has been added yet.
O14 body remains **0/3**, original seven-hole census unchanged. This audit
commit precedes any retained helper, as ruled.
