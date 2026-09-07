# R181 Unit C — O21 withdrawal obligations (no branch proofs)

One disposable type probe, **C-probe-1 PASS,2.080s**, Idris0.8.0; two of the
three allowed checks were unnecessary. The probe contains ONE record of debts,
no constructor application, theorem implementation, postulate or hole. Its
source is removed after the check and preserved in the compiler evidence.
SHA256 `11e6c9f08ccc5f10e0dd7c1ee13c46c10bfc10ff89db6a886d9142db84ea166d`.
No O21 signature/body/identity subcase was changed.

## Coordinates that must not be conflated

R175 C4 remains correct. Fix `sameInputs`, its `generatedRegistrationTree`,
`generatedGenerationBijection`, and the constructor-owned current name map.
Keep both ORIGINAL traces, both canonical capitals, and the accepted deletion
scanner indexed at those exact originals. A replay is not another left
canonical schedule. The required path is original-left → canonical-left →
operational replay → canonical-right → original-right, not a trace cast.

Relevant checked capital:

- `CP3.VestigialEndpointGeneration` (2851–2876): actual current generation,
  discarded membership, actual fiber lookup, retired=True, clean `Inactive
  Nothing`, complete ordered bindings=[], hasChild=False, isSupported=False.
- `CP3.CurrentEndpointRenaming` (2958–3005): each ACTUAL current lookup yields
  EITHER that full vestigial packet OR an exact mapped current birth. The second
  alternative is allowed; withdrawal of a raw name does not negate it.
- `CP3.EndpointFiberRelatedModuloVestigial` (3031–3078): the concrete four-way
  endpoint disposition below. Its alternatives are not just support booleans.
- `CP5ConfluenceRenamingCompositionSpike.AcceptedDeletionScannerCapital`
  (1877–1920): exact withdrawn generation→accepted scanner discarded membership
  and original closed-parent classification, on each side separately.
- `acceptedLeftEndpointCurrent`, `acceptedRightEndpointCurrent`,
  `acceptedLeftCurrentFiber`, `acceptedRightCurrentFiber`: accepted-scan lookup
  authentication. They provide actual identities/presence, not endpoint inertness.
- `replayedCanonicalOuterControlOutsideSpike` (2578–2620), outer ambient and
  tables (2622–2691): existing outside-both/effect composition. The identity
  subcase already closed in prior work is not reopened.

## First split ACTUAL endpoint lookups

Let `x` be the selected original-left name and `y=phi(x)` the original-right
name. `R_L` and `R_R` denote the actual canonical withdrawal-name projections;
their generation lists must remain available, not erased into set membership.

| Original lookup at x | Original lookup at y | Exact admissible disposition |
|---|---|---|
| Nothing | Nothing | `MaybeFiberRelatedBy ... Nothing Nothing` (absence equations required) |
| Just leftFiber | Nothing | FULL left `VestigialEndpointGeneration` plus actual right absence |
| Nothing | Just rightFiber | actual left absence plus FULL right vestigial packet |
| Just leftFiber | Just rightFiber | exact `FiberRelatedBy` OR BOTH full vestigial packets |

A full left vestigial packet alone does **not** solve the both-present case.
Neither raw withdrawal membership, retirement, unsupportedness nor a deleted
scanner stamp alone supplies any missing row premise.

## Three membership branches

### Left-only: x∈R_L and y∉R_R

1. Derive an actual withdrawn ORIGINAL generated birth for x, not just a raw
   name in a list. For a present endpoint, authenticate its accepted current
   generation and its own original birth before using original uniqueness to
   identify it with that withdrawn birth. Birth ordinals and component identity
   must be transported, not guessed from the raw name.
2. If the actual left endpoint is absent, use its equation; do not infer it
   from x∈R_L. Right absence, if needed, must follow along the actual canonical/
   replay/control path or accepted mapped lookup, not the set label.
3. If left is present, classify `leftCurrentGenerationMapped` at THIS birth.
   The vestigial alternative supplies left inertness but still leaves the
   opposite lookup/disposition to resolve. The mapped alternative supplies a
   particular right current generation; an authenticated right current-fiber
   producer then yields right presence. It contradicts an actual right-Nothing
   equation, but **not** the bare fact y∉R_R.
4. Any proof that the withdrawn birth has no canonical representative must use
   the actual removal/occurrence correspondence and uniqueness. It is not the
   unsupported global rule "withdrawn raw name means canonical absence".

### Right-only: x∉R_L and y∈R_R

Mirror the above using `rightCurrentGenerationMapped`, generationBackward,
renameBackward and exact right original births. Keep the inverse-map equations
explicit when returning to x. Left/right originals' uniqueness are separate
inputs; neither transfers by name-bijection rhetoric.

### Both withdrawn

Perform the same four actual-lookup cases. Both present may require TWO actual
Lemma57 packets; the two current generations need not be dropped merely because
their names are withdrawn. If the accepted scanner chooses exact mapped births,
retain that equality and discharge its endpoint-control obligation, or obtain a
contradiction at those identified occurrences. Neither a global mapped-birth
negation nor a G31/Q9 resurrection is licensed. Absence of one endpoint excludes
only an authenticated opposite-current-birth route that actually implies its
presence.

## Missing producer graph / sizing

The hard shared work is NOT the final nested Either construction:

1. Actual present endpoint → accepted current → located ORIGINAL birth, then
   equality to the specified withdrawn birth using the two original uniques.
2. That exact deleted-parent classification plus surviving endpoint lookup →
   all eight fields of `VestigialEndpointGeneration`, notably clean lifecycle,
   full empty table, childlessness and unsupportedness.
3. Exact mapped-current alternative → opposite actual original birth/fiber,
   respecting the accepted generation and name maps.
4. Where needed, actual canonical absence/retention through the stored origin
   and removal maps, without substituting an arbitrary canonical trace.
5. Only then the four lookup dispositions in each of the three membership
   branches and existing outside-both/effect composition.

This is at least two substantial shared producer families plus localized
scanner/occurrence transport and branch assembly; the final twelve-cell matrix
is not twelve independent proofs. No proof-time or fixed micro-unit completion
promise follows from the type probe. Begin with a single exact present/current
birth ownership interface and one-sided Lemma57 producer in a future authorized
shift; do not start by filling the O21 body.

## What the disposable probe checked

`R181LeftWithdrawalPresentDebts` threads the exact two original traces/capitals,
accepted scanner and maps, and states the actual lookup/current/withdrawn birth
and immutable-component debts. It separately types the continuation obligations
for BOTH CurrentEndpointRenaming alternatives into the original
`EndpointFiberRelatedModuloVestigial` goal. No record is inhabited. In particular,
its fields are outstanding obligations, NOT new assumptions added to O21 and
NOT evidence that these branches have been proved.
