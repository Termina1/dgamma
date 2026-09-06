# R173 grind-shift audit — work in progress

Start: 2026-09-06 15:13:47 UTC, branch `cp5-thm73-scoping`, HEAD `15fb0e6`.
Deadline 19:13:47; no new attempts after 18:33:47; safe final gate by 18:58:47.
Idris 2 0.8.0, seeded-only checks, one compiler at a time, one new top-level
per invocation, maximum three charged attempts per micro-unit. All successes
committed before subsequent proof work. No production edits, new `with`,
let aliases, nonlinear patterns or proof escapes introduced.

## Unit A — global raw-name uniqueness

- `5450c88` A1 1/3: `CP5UniqueRawNameInsertions.UniqueRawNameInsertions`,
  erased equality of located ordinals for ANY two insertions of one raw name,
  independently quantified parent and component, anywhere in the whole trace.
- `849d3f5` A2 2/3: `r173ReuseRejectsUniqueInsertions`: designated R172
  child birth of 1 at ordinal 2 versus reused root birth of 1 at ordinal 5.
  First check lacked the LocalDiamond import, then passed; no semantic weakening.
- `82447d8` A3 2/3: executable `rawInsertionNameAt` ordinal observation;
  first check exposed inaccessible intermediate state, fixed with erased state
  indices and matching actual `Fired` rather than projecting its action.
- `76ba893`, `0d9b095`, `90fcdf9` A4–A6 each 1/3: head/split/located
  observation authentication, explicit transition-count equality bridge.
- `9bccd9a`, `38b1bda` A7–A8 each 1/3: genuine distinct-name fixture
  `r45SourceTrace` (insert root 0; begin 0; insert child 1; retire 1), with
  lookup-based proof of unique insertion ordinals. Not a supplied-capital fake.
- Optional general checker/producer: NOT DONE; finite concrete certificates
  and executable observation are not advertised as a global UID allocator.

## Unit B — precise boundary / consumer clause map

| Site | Old | New / actual premise source |
|---|---|---|
| O17 `sortClosingFreeTraceSpike` (`511b2e6`, B1 1/3) | `... shape ordering -> SortedClosingFreeTrace ... ordering` | `... shape ordering -> (0 uniqueInsertions : UniqueRawNameInsertions ... trace) ->` SAME conclusion; explicit model-type signature binders added. |
| R8 `fullPipelineFromBundles`, left O17 call | Left reduced trace + bundle + shape + order | Additionally derives reduced uniqueness with `uniqueInsertionsAfterReduction ... leftReduction leftUnique`. `leftUnique` is original-trace caller premise, not a claimed producer. |
| R8 right O17 call | Symmetric | Same derivation using actual right reduction and right original uniqueness. |
| R8 public assembly (`57ce6a1`, B13 1/3) | Existing original inputs + two R143 late records | Additionally explicit erased `leftUnique`, `rightUnique`; both direct O17 calls updated. Fresh direct check 107s / sampled ~35GiB. |
| R16 assembly (`ed0ddc6`, B14 1/3) | Claimed frozen `confluenceTheorem` but already omitted both required R143 late records | Supervisor approved IN-PLACE CONDITIONAL assembly: explicit full CP3 telescope + two supplied late records + two original-uniqueness premises. All hypotheses documented. Fresh check passes. No immutable-type claim. |

Actual deletion premise producer (`CP5UniqueRawNameDeletion`):

- B2 `51090e8` 1/3: successor origin nonzero.
- B3 `c0a3965` 2/3: successor stripping (first: unavailable `justInjective`).
- B4 `7a2894d` 1/3: executable subsequence source map injectivity.
- B5 `16aeff4` 1/3: source position is strictly inside its segment.
- B6 `caa1f91`, B7 `d8c76dc` each 1/3: disjoint segment/offset arithmetic.
- B8 `4633a24` 3/3: WHOLE deletion embedding injectivity, all 9 pairs of
  before/episode/after regions; attempts 1/2 missed Metatheory import / count
  application parentheses, respectively. Third passed; budget not exceeded.
- B9 `c981a80` 1/3: exact operational occurrence certificate preserves uniqueness.
- B10 `a16e033` 1/3: derive for actual deletion-step result from producer capital.
- B11 `f5a5eb4` 1/3: structural actual deletion derivation fold.
- B12 `ecc3f6b` 1/3: `uniqueInsertionsAfterReduction` closes the ORIGINAL-to-REDUCED
  premise bridge. No new reduced-output assumption, cast, or frozen theorem call.

`THM73-PLAN.md` now states the revised research theorem telescope. R16 fixture
DRIFT is closed only as conditional assembly. Exact `CanonicalReplayAccountingLaws`
and shared original/reduced order producers remain OPEN and are merely supplied
by the late records. Production theorem signature remains frozen/defective.

## Unit C

Disposable probe **C-probe 1/3 PASSED** (15:41:45–15:41:47 UTC, exit 0,
no diagnostics), removed BEFORE retained worklist work. SHA256:
`38fb4943cf5e2106598d58657eb809e48eb87e6353009bcfbc1b9e38e9682396`.
It derives raw actor distinctness for a generated birth earlier than a root
birth, from the new whole-trace premise plus actual located ordinal ordering.
The ordering is structural position evidence, not assumed actor distinctness.
No applicability/hoist/complete sorter is claimed: the worklist must produce
that position evidence and the remaining swap applicability itself.

```idris
module DGamma.R173O17FreshNameProbe

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Disposable generalized same-name branch probe, not an O17 sorter.
||| Birth ordering is concrete ordinal evidence, NOT an actor-distinctness input.
0 r173UniqueGeneratedBirthBeforeRoot :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (child, parent, root : name) ->
  (childComponent, rootComponent : Component key value world error) ->
  (birth : LocatedGeneratedRegistration child parent childComponent trace) ->
  (rootBirth : LocatedActionOccurrence (OInsert root Root rootComponent) trace) ->
  (LT (registrationOrdinal birth) (locatedActionOrdinal rootBirth)) ->
  Not (child = root)
r173UniqueGeneratedBirthBeforeRoot name key world error value nameEq keyEq trace unique
  child parent root childComponent rootComponent birth rootBirth earlier same =
    case same of
      Refl => LTImpliesNotGTE earlier
        (replace {p = \position => LTE position (registrationOrdinal birth)}
          (uniqueInsertionPosition unique child (ChildOf parent) Root childComponent rootComponent
            (generatedRegistrationActionOccurrence birth) rootBirth) reflexive)
```

Retained simultaneous worklist has not yet been attempted. O17 body 0/3.

## Evidence / final gate

Pending final refresh: full invocation ledger, precise census, seeded 207/207,
all frozen SHA checks, production diff, final status/acceptance JSON.
