# Theorem 73 (Confluence) — CP5 scoping plan, revision 5

Branch: `cp5-thm73-scoping`

Review trail:

- `review-cp5-plan-round1.md` — REJECT;
- `review-cp5-plan-round2.md` — REJECT;
- `review-cp5-plan-round3.md` — REJECT;
- `review-cp5-plan-round4.md` — REJECT, one O19 blocker and one estimate major.

This remains research-only interface scoping. Accepted statements and every file
under `src/` are immutable. Hole-bearing modules under `research/DGamma/` remain
excluded from `dgamma.ipkg` and must not merge unchanged to `main`.

## Executive estimate

The provisional budget is **70–120 engineering shifts**. Revision 4's 65–110
band is withdrawn. The corrected design makes cross-trace support-set matching
smaller, but moves all actual local block-safety and noncanonical target replay
into O20. Re-estimate after proofs of O4, O9, O15, the first complete O20
whole-block swap, and both same-name scanner inductions.

## 1. O19 design choice: option (b), operational block swappability

Revision 5 chooses reviewer option **(b)**. We do not assert a new invariant
that every intermediate of a supported-endpoint `SupportPath` is supported.
That would contradict the checked four-fiber model admitted by
`CanonicalEndpointRelation`, and no accepted replay premise currently excludes
that model.

The choice follows the actual consumer inventory:

1. The immutable `CanonicalSchedule` requires each original trace's own support
   order to linearize its own full `SupportPath` relation.
2. The local diamond theorems do **not** consume cross-endpoint `SupportPath`
   transport. They consume actual checked adjacent transitions, distinct actors,
   source applicability, insertion child/licensing-parent exclusions, and the
   current full `ReplayInvariantBundle`.
3. Therefore cross-trace O19 needs only to show that the two support orders
   enumerate the same renamed actor set and admit a pure adjacent actor-list
   permutation.
4. O20 must then realize every list swap by actual whole-block replay, expanding
   it into A/A, A/O, O/A, and O/O `AdjacentSwapResult`s and threading the exact
   returned trace, block decomposition, quotient, correspondence, and bundle.
5. The inverse-right actor order need not be another left
   `LinearizesSupport`. Consequently the operational target is deliberately not
   packaged as a left `CanonicalSchedule`.

This directly removes the false claim attacked by
`guardedTransportContradiction` and
`inverseMappedRightOrderCannotLinearizeLeft`.

## 2. Calibration rule

Every interface field must pass:

1. **Consumer necessity** — identify the exact later projection.
2. **Producer inhabitability** — include every accepted vestigial shape.
3. **Index discipline** — probe the actual trace/state/raw-name namespace.
4. **Intermediate discipline** — for any graph/path relation, inspect every
   intermediate node, not only endpoints.

Revision 5 transports no graph edges or paths across endpoints. Unsupported
intermediates are absent from actor lists and therefore never become permutation
entries, while their original paths remain valid and unmodified.

## 3. Exact producer/consumer pipeline

| Producer | Exact output | Immediate consumer |
|---|---|---|
| Relational replay | `RelationalReplayCorrespondence` and `RelationalReplayEndpoint` | independence transport and recursive replay |
| Recursive replay state | Full `ReplayInvariantBundle` | next deletion or adjacent transition swap |
| Local A/A, A/O, O/A, O/O | `LocalRelationalDiamond` with moved tags/branches and source safety | `AdjacentSwapResult` |
| One D72 step | enriched `DeletionChainStep` with typed deleted generations and next bundle | delete-all recursion |
| Delete-all recursion | `ClosingFreeReduction` with dependent deletion history and exact accounting | one-trace sorting |
| One-trace sorting | `SortedClosingFreeTrace`, minimal support transport, orchestration accounting | simultaneous enriched schedule |
| Simultaneous constructor | `IndependentCanonicalSchedule` with exact replay, bundle, independence, and withdrawal classifier | O19 and scanner producer |
| **O19 support-set matching** | `MappedCanonicalSupportOrders`: membership both ways, mapped distinctness, and `CertifiedActorPermutation leftOrder (map renameBackward rightOrder)` | O20 operational realization |
| One local actor-list swap | `OperationalAdjacentBlockSwap`: exact target trace/blocks, correspondence, quotient, full next bundle, and external inputs | next operational actor swap |
| Recursive operational permutation | `OperationalActorPermutation`: each returned bundle/decomposition is the next step's input | `PermutedCanonicalExecution` |
| O20 final execution | target trace at exact inverse-right actor order, target block decomposition, recursive operational certificate, aggregate replay/quotient/bundle | exact replay→right bridge |
| Replay→right bridge | `ReplayedCanonicalEndpointBridge` indexed by the exact noncanonical operational trace and fixed accepted bijection | O21 |
| Scanner producer | complete `acceptedDeletionScannerCapitalSpike` from `sameInputs` and two enriched schedules | O21 vestigial cases |
| Final composition | complete `originalEndpointsConvergeSpike` with original schedule scanner, source→target replay/quotient, and exact target bridge | immutable `ConfluenceResult` using the original two canonical schedules |

The removed revision-4 fields are not replaced under new names:

- no forward/backward `SupportPath` transport;
- no inverse-right `LinearizesSupport leftFinal`;
- no path incomparability certificate;
- no false `permutedLeftCapital : IndependentCanonicalSchedule`.

## 4. New regression boundaries

### 4.1 Intermediate withdrawn path

Two complementary positive regressions are required and now elaborate:

- A concrete four-fiber model retains supported `Lower` and `Upper`, a real
  `Lower → Middle → Upper` path, an unsupported retired/clean `Middle`, accepted
  withdrawal of its exact generation, right absence, and the proof that
  `[Alternate, Upper, Lower]` cannot linearize the left full path. The same model
  constructs the replacement pure actor certificate to that exact target.
- `intermediateVestigialProducerRegression` runs at actual confluence indices:
  checked enriched traces, accepted `sameInputs`, precise scanner-deleted
  `VestigialEndpointGeneration`, first edge and remaining path through the
  withdrawn intermediate, and right absence. It uses the path to prove the
  intermediate is not an actor-list member, then returns O19's exact actor
  certificate without transporting the path.

Thus the countermodel is accepted by the corrected producer story rather than
refuted by an impossible field.

### 4.2 Same raw name, multiple scanner births

`scannerSideSequence` exposes the accepted scanner's actual left/right step
order. `ScannerSidesInterleaved` requires both relative orders, witnessing at
least L…R…L or R…L…R rather than two isolated scans.

`sameRawNameScannerRegression` consumes two left and two right withdrawals with
identical raw names but pairwise-distinct birth ordinals. Its complete body calls
the accepted scanner producer for all four exact generations and returns:

- both precise left generations in `leftDeletedGenerations`;
- both precise right generations in `rightDeletedGenerations`;
- same-name equalities; and
- full-generation inequalities derived from ordinal inequalities.

The external regression supplies an explicit L-R-L scanner prefix and accepts no
scanner-capital premise.

### 4.3 Downstream index retention

External consumers check that:

- O19's certificate starts at the exact left support order and targets the exact
  inverse-renamed right actor order;
- `OperationalActorPermutation` starts at the actual left canonical trace,
  blocks, and bundle;
- the bridge is indexed by the exact operational target trace;
- scanner, replay, quotient, bridge, O21, and outer result compose without
  detached premises; and
- the outer `ConfluenceResult` retains the original valid left/right
  `CanonicalSchedule`s rather than misclassifying the noncanonical intermediary.

## 5. Proof obligations in dependency order

There remain **23 obligations: O1–O22 proof obligations and O23 validation**.
Grades are S, M, L, XL.

| ID | Obligation | Depends on | Grade |
|---|---|---|---|
| **O1** | Trace/list algebra, external-input algebra, replay-endpoint algebra, and proved bijection/correspondence composition. | accepted CP3/RAR | **M.** |
| **O2** | Lift generic replay correspondence to both `TraceIndependent` fields. | O1 | **M–L.** Structural after proved composition. |
| **O3** | A/A diamonds for Begin and Iter/Finish with exact tags, outcomes, effects, controls, and applicability. | O2 | **L–XL.** |
| **O4** | A/O and O/A with actor/child/licensing-parent exclusions. | O2–O3 | **XL gate.** |
| **O5** | O/O, especially yielded Insert/Insert with generation and freshness discipline. | O1–O2 | **XL gate.** |
| **O6** | Complete `AdjacentSwapResult` suffix replay with next full bundle and quotient. | O1–O5 | **XL.** |
| **O7** | Executable closed/open episode scanners and occurrence uniqueness. | GEN | **L.** |
| **O8** | Select generation-aware support/parent-maximal D72 candidate. | O7, Lemmas 68/70 | **XL.** |
| **O9** | Enrich one D72 call with exact typed classifications and recursive capital. | O2, O8, D72 | **XL.** |
| **O10** | Well-founded delete-all recursion. | O7–O9 | **L.** |
| **O11** | Compose typed deletion history and exact endpoint/registration accounting. | O1, O9–O10 | **XL.** |
| **O12** | Closing-free supported open-block shape. | O7, O11 | **L–XL gate.** |
| **O13** | Project Lemma-68/70 capital from every bundle. | O9 | **S–M.** |
| **O14** | Construct finite duplicate-free support linearization. | O13 | **M–L.** |
| **O15** | Minimal one-trace support truth/linearization/placement bridge under vestigials. | O11, O13–O14 | **L–XL gate.** |
| **O16** | Root/generated input placement and exact registration accounting. | O1, O6, O11 | **L–XL.** |
| **O17** | Initial one-trace actor-block sorting with all four orientations and full bundle threading. | O6, O12–O16 | **XL.** |
| **O18** | Assemble `IndependentCanonicalSchedule`. | O11, O15–O17 | **S.** Complete body. |
| **O19** | Prove renamed support-set equality and pure adjacent `CertifiedActorPermutation`; no graph transport. | O14–O18 | **M–L.** Finite unique-list permutation. |
| **O20** | For every O19 list step, derive actual source-sensitive block swappability and construct recursive `OperationalActorPermutation`, target blocks, aggregate replay/quotient/bundle, and exact replay→right bridge. | O2–O6, O18–O19 | **XL, expanded.** All safety moved here honestly. |
| **O21** | Prove left/right discard inductions including same-name ordinal reuse; complete four-way vestigial endpoint composition through the replay target. | O9–O11, O18, O20 | **XL.** |
| **O22** | Assemble original canonical schedules plus O21 equivalence into `ConfluenceResult`; inhabit `confluenceTheorem`. | O20–O21 | **S.** Composition body checked. |
| **O23** | Intermediate-node, same-name scanner, O/A, vestigial, coupling, package, review, and release-isolation validation. | O1–O22 | **M–L.** |

## 6. Phase totals and 70–120 deduction

| Phase | Obligations | Raw band |
|---|---|---:|
| A — replay algebra/independence | O1–O2 | 4–8 |
| B — four local orientations and suffix replay | O3–O6 | 10–18 |
| C — selection and enriched D72 | O7–O9 | 8–15 |
| D — recursive typed deletion history | O10–O11 | 8–15 |
| E — shape/support/minimal bridge | O12–O15 | 7–13 |
| F — one-trace accounting and sorting | O16–O18 | 9–16 |
| G — pure matching, operational block replay, scanner/O21 | O19–O21 | 22–34 |
| H — outer theorem and validation | O22–O23 | 2–5 |

Raw phase rows sum to **70–124**. Shared list-permutation, replay composition,
and scanner-membership infrastructure accounts for **0–4 shifts of overlap at
the upper end**, yielding the advertised **70–120** range. No larger undocumented
overlap deduction is assumed.

## 7. Round-4 finding closure map

| Finding | Round-4 result | Revision-5 resolution |
|---:|---|---|
| **1 blocker** | Endpoint guards did not protect unsupported `SupportPath` intermediates; inverse-right target might not linearize left. | Chose option (b). Removed every cross-endpoint path/linearization/incomparability field. O19 now returns a pure actor permutation. Added actual `OperationalAdjacentBlockSwap` and recursive `OperationalActorPermutation`; noncanonical `PermutedCanonicalExecution`; generic accepted-index and concrete four-fiber intermediate regressions. |
| **2 major** | 65–110 contradicted phase arithmetic and omitted redesign cost. | Revised to 70–120. Table sums explicitly to 70–124 and documents only a 0–4 upper-end overlap deduction. O19 is M–L finite-list work; the displaced local safety expands O20 XL and phase G to 22–34. |

## 8. Exact round-5 change closure

| # | Required change | Resolution |
|---:|---|---|
| 1 | Redesign O19 | Option (b), chosen from actual diamond consumers. Pure actor permutation plus operational block replay; no full-path transport. |
| 2 | Intermediate-vestigial producer regression | Concrete accepted endpoint countermodel now constructs the replacement target; actual indexed regression consumes path first/rest plus precise scanner-deleted vestigial birth and proves the middle is not an actor entry. |
| 3 | Re-run exact consumers | Exact left source trace/blocks/bundle, target trace, replay, quotient, scanner, bridge, O21, and outer canonical schedules elaborate end to end. |
| 4 | Same-name multiple-birth scanner | Interleaved scanner-side trace plus two distinct same-name birth ordinals on each side; all four exact deleted memberships produced without scanner premise. |
| 5 | Re-estimate | 70–120 with raw totals and overlap deduction shown explicitly. |

## 9. Retained positive results

Round-3/4 fixes remain intact: source-sensitive O/A, one-trace minimal support
transport, simultaneous schedule/replay/bundle construction, bridge/replay index
coupling, complete scanner producer, exact occurrence + same-parent-close
classification, and complete final O21/outer assembly. Both prior vestigial
variants remain regression targets.

## 10. Validation and release boundary

Before proof authorization, external round-5 review must verify:

- the old intermediate countermodel cannot derive any new false field;
- the pure actor certificate and operational recursive replay share the exact
  source and target orders/traces;
- every operational step threads its returned blocks and full bundle;
- the noncanonical target cannot be retyped as an unrelated canonical schedule;
- exact replay/quotient/bridge/O21 composition remains non-detachable;
- same-name distinct ordinals reach both accepted deleted lists under an
  interleaved scanner; and
- `src/`, `dgamma.ipkg`, and `confluenceTheorem` remain unchanged.

All five spikes must elaborate serially against an exact release-source copy.
Production remains hole-free and research-unreachable. Theorem 73 remains
unproved by design after revision 5.
