# O6 L2R16 — production integrated; Tier 2 status

This is the live successor to `O6-L2R15-CP3-DIFF-DRAFT-OVERLAY.md`. The signed L2R15 overlay remains an immutable historical handoff, **not a pending production patch**. R205 production `452420c7` was merged at `28da551d`; the authorized V19 restatement `bfe2e8d5` was merged at `b1659154`. No lane-owned `src/` edit was made. The old copy-ready diff is deliberately not repeated here.

**Labels:** “production checked” means the stated consumer/fixture typechecks against the actual merged CP3 API; it does not mean this lane rebuilt CP3 or the package. “research-copy checked” retains its exact nominal research types. A checked TYPE is not an inhabitant. Closure counts and final receipts are in the recheck state/audit, including blocked and unfinished modules.

**Final inherited validation:** 194/200 fresh green (105 unchanged +89 repaired), six external R206 blockers. All eight deferred fixtures/dependents passed; no UNCHECKED target remains. All twelve new modules freshly passed final validation V1177–V1188 by05:29:10 UTC.

## 1. Production and research correspondence

| Item | L2R16 status | Exact scope / remaining work |
|---|---|---|
| A8 availability/current-cut and terminal-earliest placement | Production integrated; actual CP3 consumer checks | No old strict-all-roots-before-any-lifecycle assertion is transferred to the new placement. S2/S3 explicitly retain only the retired strict clause. |
| A10 core plus attached grammar; A12 attachedC placement | Production integrated | Main V19 `actorLifecycleCoreIntoAttached` freshly checked; S1 is the genuine research `coreIntoAttached`. No attached→core coercion exists. |
| Production availability → research scanners | **Production checked**, `L2R16ProductionBridge.researchAvailability` | Executable constructor map preserving every native state, action, dictionary and erased trace index. It is not an arbitrary reinterpretation of research references as production references. |
| attachedC gap / normal form / control fixture / classifier adapters | **Open over production**, existing research-copy statements rechecked where unblocked | No general production zero-gap theorem or complete attachedC adapter family was built in L2R16. The priority native counter-domain work superseded the planned thin adapters. |
| Native event/source/actor alignment | Research-copy checked: L2R15 event/actor/history lemmas | Narrow alignment only; no physical interval is conjured from a scan. |
| Accepted history decoder | Research-copy checked: `PhaseHistoryPath`, `phaseReleaseHistoryDecoded` | The path DATA TYPE is not itself a native interval producer. |
| General physical phase producer | **Open**: `phaseReleaseCheckToNativeOwnedInterval`, `produceForcedRootPhases` | Locate strictly earlier lifecycle and own-child release inside a contiguous native core; preserve all phase fields. |
| Concrete different-anchor phases | **Checked inhabitants**, `L2R16AnchorPhases.anchorPhase` | Both roots in both authentic native words; anchors 4 and 6. This is not a general producer. |
| Native Root/Retire suffix transports | Research-copy checked, L2R15 suffix lemmas | Suffix-only scan/anchor/target/distance results remain valid at that scope. They do not imply prefixed global distance frames. |
| Prefixed global frame TYPE | **Conditional negative theorem checked**, `L2R16AnchorFrameRejection.anchorGlobalFrameRejectedGivenUnique` | Every antecedent is constructed except `UniqueRawNameInsertions`, which is an explicit hypothesis. Full retirement remains pending that premise; see §2. |
| PhaseIterationResult base / prepend | Research-copy checked conditional constructors | A supplied actual move and recursive result are still required. Not a normalizer. |
| GeneralAdmittedMoveExistenceUnique / normalization | **Open; scalar strategy requires reassessment** | Do not call the native crossing an `AdmittedDistanceMove`: that record already requires strict total decrease. |
| Eight native orchestration shapes | Research-copy checked at the existing general scope | Root/Child insert, retire and remove schemas do not discharge the four lifecycle premises. |
| Four lifecycle common-payload shapes | **Open** | Old/new LBegin and LAdvance/LFinish replacement shapes with common payloads; no new general proof in this shift. |
| General LOCAL square | Conditional research result remains conditional | Existing fixture checks are separate and may be unfinished at the shift cutoff. No endpoint oracle was added. |
| Cross-bundle control history | **Open research obligation** | The signed production grammar is same-bundle, not arbitrary cross-bundle history. |

## 2. Different-anchor Retire crossing: a measured design finding

Initial valid registry: dependency-free parent 0, children 1/2 declaring True/False respectively, and empty-provision child 3. Programs have no effect commands. Roots 4/5 declare True/False respectively.

Original native word:

```
Begin0, Finish0, Retire1, Remove1, Retire2, Remove2,
Retire3, Insert4(True), Insert5(False)
```

Crossed native word:

```
Begin0, Finish0, Retire1, Remove1, Retire2, Remove2,
Insert4(True), Retire3, Insert5(False)
```

`anchorNative` proves initial well-formedness and all twelve actual checked edges needed by these two words. `anchorTrail` uses **production** AvailabilityTrace; the executable identity-on-native-data bridge feeds the existing research scanners.

`anchorDistanceAgreement` proves the actual computed data, not supplied expected-frame equations:

| Observation | Original | Crossed |
|---|---:|---:|
| Root4 distance | 3 | 2 |
| Root5 distance | 0 | 1 |
| Whole-trace totalDistance | 3 | 3 |
| Root5 external-order target | 8 | 7 |

Both roots have genuine ForcedRootPhase inhabitants in both words. Their anchors are 4 and 6. The first core ends at Remove1; the second ends at Remove2. The current phase contract imposes **no maximal-core requirement**. Root5's fixed anchor 6 is dominated by the previous-root floor: 8 before the crossing, 7 afterwards.

Further checked companions authenticate the exact local classified square, the full remaining native root5 suffix frames, FrontNormal/NeverRetired, the entire two-entry catalog and absence of an earlier root before ordinal7. **None is an AdmittedDistanceMove.**

### Precise conditional conclusion

`anchorGlobalFrameRejectedGivenUnique` inhabits:

```
UniqueRawNameInsertions ... originalNativeWord ->
  GlobalDistanceFramesFromNativeSuffix ... actualSquare ... actualSuffixFrames -> Void
```

All other global-frame antecedents are constructed inside that theorem. The assumed two decompositions would entail totalDistance 3 = 4, contradicting the actual computation. Thus **uniqueness is the sole unassembled premise of this particular negative theorem**. There is no unconditional rejection/retirement claim, no general normalization theorem and no claim that the paper itself has been refuted.

### Exhausted / next statement

- **Exhausted:** `L2R16 T12: UniqueRawNameInsertions on the anchor fixture via if-reduction` — the **interface-vs-primitive wall**. Three failed checks; complete source revert. T11 separately authenticates each actual insertion ordinal, but that is not advertised as an assembled UniqueRawNameInsertions inhabitant. The authorized visibility companion did not solve the consumer wall.
- **UNATTEMPTED; first L2R17 micro-unit:** the supervisor's different statement: computed uniqueness check on the concrete native word, **explicit DecEq/Eq dictionaries**, ω-data agreement by Refl at the definition, then an erased consumer of computed Bool = True. No `if` over `selected`; no disguised T12 retry.
- **Design direction, not a proved normalizer:** lexicographic per-root distance in external orchestration order, implemented conceptually as outer root-order induction and inner distance induction with earlier roots fixed. The observed `(3,0) → (2,1)` is compatible with that direction while refuting the proposed scalar decrease under the remaining uniqueness premise. Earlier-root preservation and general move existence still need proofs.

## 3. What was not promoted

No Tier 2 residue blocks the already completed production unfreeze. No new postulate, hole, `believe_me`, `assert_total`, `partial`, `with` construct or hidden endpoint/decrease premise was introduced. Native fixtures are concrete constructor-produced proofs over actual operations; generic state remains abstract in the bridge and inherited libraries. The census of protected proof holes is unchanged because no lane-owned production source changed.

Independent mechanical verification is not mathematical review. The parent-owned review gate is still required. The audit and final closure state—not this planning table alone—determine which inherited long fixtures received fresh receipts and which remain UNCHECKED or externally blocked.
