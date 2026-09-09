#!/usr/bin/env python3
"""Docs-only bounded sync, adapted from run-l2r5-draft.py's rehome recipe.
Preserves EVERY Tier-1 code block. Updates only the authorized predecessor
CP3 draft, serialized manifest, and generator's missing manifest renamings.
No compiler, cache, source, staging, lock/window or main-worktree operation.
"""
import ast, hashlib, json, pathlib, subprocess
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
assert pathlib.Path.cwd()==ROOT
BASE='c09c0da2'
def original(path): return subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT,text=True)
placement=[('MkAvailabilityAwareCanonicalInputPlacement','MkCanonicalInputPlacement'),('AvailabilityAwareCanonicalInputPlacement','CanonicalInputPlacement'),('availableRootGenerationFresh','rootGenerationFresh'),('availableChildGenerationBeforeOwnLifecycle','childGenerationBeforeOwnLifecycle')]
generator='research-tests/run-l2r5-draft.py'
s=original(generator)
needle="closure=cut('research-tests/O6-L2R3-Sources/DGamma/L2R3ForcedClosure.idr'"
assert s.count(needle)==1
s=s.replace(needle,"# L2R6 reviewer P2: serialize every renaming actually applied above.\nmapping.update(dict("+repr(placement)+"))\n"+needle)
(ROOT/generator).write_text(s)
manifestpath='research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json'
manifest=json.loads(original(manifestpath));manifest['renamings'].update(dict(placement))
(ROOT/manifestpath).write_text(json.dumps(manifest,indent=2)+'\n')
p='research-tests/O6-L2R5-CP3-DIFF-DRAFT.md';draft=original(p)
draft=draft.replace('# L2R5 — CP3 DIFF DRAFT for owner signature','# L2R5 — CP3 DIFF DRAFT for owner signature (L2R6 research sync)')
draft=draft.replace('Tier 2 is explicitly UNCHECKED specification text with unresolved connector parameters.','Tier 2 is PARTIALLY CHECKED research code, with the exact limits below. The original proposed record fragments remain uncompiled, not drop-in CP3 definitions.')
replacements={
'| Least forced set, trace-linked classifier, anchor assignment | Generic leastness 7737a019; local KeyReleased / EarlierForcedRoot | TIER 2: no compiled global classifier/assignment |':'| Least forced set, trace-linked classifier, anchor assignment | L2R6 KeyForcedAt/keyForcedAt 4327be06/2b5609fd; ForcedOnTrace/leastness 6c0cccc4/abface27; classifyForced c05ff425; anchorAssignment d616fc24 | PARTIAL: release-ordinal scan witnesses and all three fixtures checked; general scan decoder, classifier soundness/completeness, max/stable-release proofs OPEN |',
'| RootInputsBeforeLifecycle replacement scope | Barrier-order impossibility 9c7c0a7c; old strict reading cannot hold | TIER 2 front-normal; non-insert root-action/generation disposition remains explicit |':'| RootInputsBeforeLifecycle replacement scope | L2R6 FrontNormal 71155c8e, ForcedRootNeverRetired 1eb6d5ed, actual full fixture scans 0cd3f374 | PARTIAL: accepted-scan Bools; generation/least-forcing correspondence and general scoped NF OPEN; richer controls-in-bundle grammar reserved for L2R7 |',
'| Normalizer endpoint relation and iteration | RegistryExtensional 0fbc3d33, snapshot embedding 21453f7c, two-insert endpoint algebra 71f6de67, Retire transport c60f315a | Native Insert/Insert applicability, remaining action transport, swap existence/distance iteration OPEN |':'| Normalizer endpoint relation and iteration | L2R5 extensional algebra; L2R6 actual moves bc32a5a3, one-/two-step iterations 21df2ce5, iterationEndpoint a4be84aa | Concrete 1→0 / 2→1→0 CLOSED. General existence/iteration TYPES 84b38628/98c51dd6 under ForcedRootPhase 8024d764; producers, all-kind applicability/transport OPEN |',
'| Raw catalog generated from actual traces | L2R5 ef9b9f9b; both full fixtures 8c603e3b | NOT AttachedNormalForm; catalog→placed-bundle assignment still open |':'| Raw catalog and placed bundle linkage | L2R5 raw scan completeness; L2R6 PlacedBundle 77fcf3a6 and literal L2R3 fixture bundles 6a7d0ada | Same-anchor complete catalog→ONE actual bundle checked on both fixtures at anchor4; general placement/NF/selector producers OPEN |'
}
for old,new in replacements.items():
 assert old in draft;draft=draft.replace(old,new)
draft=draft.replace('# Tier 2 — UNCHECKED specification clauses','# Tier 2 — partially checked connectors; remaining specification clauses')
start=draft.index('**NOT YET SIGNABLE — no compiled definition exists for the connectors below.**')
end=draft.index('\n## T2.1',start)
draft=draft[:start]+'''**NOT YET SIGNABLE AS A COMPLETE CURE.** L2R6 checked research declarations are listed per connector below; NONE of these global connector rows is moved to Tier 1. Actual executable scans, least closure, observed anchors/distance and concrete iterations exist, but the general correspondence/placement/existence producers do not. The old Idris fragments below are retained as **L2R5 proposed API TEXT**, not as definitions of the new modules or already compiled production signatures. Where their generic names differ from the concrete L2R6 records, the source declarations and this status table are authoritative. No assumed square oracle, supplied zero result, or generic fold is counted as a normalizer.

Source inventory, exact declaration origins/commits/checks, body-only D9 correction and final hashes: `O6-L2R6-DECLARATION-ORIGINS.md`, `O6-L2R6-MICRO-UNIT-LEDGER.json`, `O6-L2R6-GRIND-SHIFT-AUDIT.md`. All sources are under `O6-L2R6-Sources/DGamma/`; production CP3 is untouched.
''' +draft[end:]
sections={
'## T2.1 Trace-linked least forced set':'''**PARTIALLY CHECKED — L2R6ForcedScan.** `scanReleaseOrdinals` (86da71ec) computes actual earlier own-child ORemove declaration-overlap ordinals; `KeyForcedAt`/`keyForcedAt` (4327be06/2b5609fd) own an explicit Bool/equation and a conditional runtime `ReleaseWitness` in that computed list. This is NOT yet a decoded LocatedActionOccurrence/shared-key/parent proof. `ForcedOnTrace` (6c0cccc4) instantiates the independent least family with generated catalog membership and computed key seeds; `forcedOnTraceLeast` (abface27) proves leastness. `classifyForced` (c05ff425) executes prefix closure; GENERAL soundness/completeness against the inductive relation remains OPEN. `forcedClassifierFixtures` (6b40802d) checks C12 [(3,True)], barrier [(3,True),(4,True)] with S keyFalse and a genuine OrderForces derivation, and a one-origin root-before-Begin2 trace [(3,False)]. Current ordinal observations are not stable original-generation transport.
''',
'## T2.2 Last-release/anchor assignment (key roots and barriers)':'''**PARTIALLY CHECKED — L2R6Anchors.** `lastReleaseCut`/`anchorOf` (d3441e72/bb7da4ee), `AnchorAssignment`/`anchorAssignment` (2a992e14/d616fc24) compute and observe the maximum actual release-ending cut across earlier/current key roots; barriers inherit, later key release raises. Equations own the exact scan and maximum input; a GENERAL maximal-element/located-release decoder and stable anchor transport remain OPEN. `placementDistanceFixtures` (6a7d0ada, rechecked in D9 8024d764) observes R/S anchors4 and original/alternate totals0/0/1/2.

`targetPosition` now has the OWNER-GATED D9 external-order correction (8024d764): max(anchor + same-anchor rank, one past the latest earlier different-anchor/non-forced root birth). **External order forbids crossing an earlier root birth, so the target must not lie before it; in the phase + FrontNormal + NeverRetired domain non-forced controls are at the front and same-anchor roots are ordered by the outer induction.** `rootDistance`/`totalDistance` are executable current-trace arithmetic; saturating Nat zero is not structural placement. `distanceOneLeft` (858d4b1b) proves exact-one arithmetic for a fixed non-crossed target; native all-root target/anchor transport is separate.
''',
'## T2.3 Front-normal form, including non-insert root orchestration':'''**PARTIALLY CHECKED — L2R6FrontNormal.** `rootOriginAt` (eeb49fbe) selects the latest matching birth ordinal, not the first raw name. `scanFrontDisposition` (f4a65df6) inspects actual source state for root Retire/Remove as well as Insert, returning front/no-forced-control Bools. `FrontNormal` (71155c8e) and `ForcedRootNeverRetired` (1eb6d5ed) retain observed values/equations plus acceptance. `frontDispositionFixtures` (0cd3f374) proves both full original traces satisfy both scans. GENERAL latest-birth agreement with the accepted generation scanner and originForced↔ForcedOnTrace remain OPEN.

**Disposition is NOT chosen by fiat.** `ForcedRootRetireInBlock` (1211f6f5) is the explicit per-located-control TYPE for being inside the releasing attached body AFTER its bundle; current core++insertion-bundle grammar has no remaining interval. Supervisor's provisional **L2R7-only** options: (1) richer ordered bundle grammar admitting root Insert with release/barrier witness, then root Retire/Remove with an already-bundled witness (this or earlier bundle); attached body remains core++bundle-with-controls, gap statement unchanged. Fixture first: barrier extended by Retire3/Remove3 after S. NO implementation here. (2) interim `ForcedRootNeverRetired` scope; the quiescent open-set/lifecycle argument must PRODUCE it, not assume it universally.

`ForcedRootPhase` (8024d764, L2R6Phase) makes the separate phase premise precise: the assigned anchor is the ending own-child Remove of a globally located extended actor core, after a located lifecycle of that actor; key seed/barrier linkage uses a real AttachedRelease. Pre-lifecycle removal of an initially retired child is explicitly excluded. General producer **produceForcedRootPhases OPEN**; no new phase-fixture producer was within D12 cap.
''',
'## T2.4 Bundle-placement linkage and selector projection':'''**PARTIALLY CHECKED — L2R6Anchors/PlacementFixtures.** `placedRootsAt` (84b31a51) computes the complete same-anchor catalog in order. `PlacedBundle` (77fcf3a6) ties its equality to the catalog of ONE actual OrderedForcedRootBundle, with its offset exactly at release-ending anchor after the actor core. `placementDistanceFixtures` (6a7d0ada) literally uses L2R3 c12CatalogR/barrierCatalogR, not reconstructed dependent-record equalities; inherited offset equations are the L2R4 catalog anchors4. Both concrete connectors close. GENERAL PlacedBundle production and FrontNormal+NeverRetired+placed bundles→inter-block AttachedNormalForm remain OPEN: generation/forcing correspondence, all-occurrence root-control exclusion, actual region embedding and catalog-member→bundle-occurrence decoding are not produced. L2R6's residual fixture NF fields merely reuse the exact inherited EMPTY-gap proofs; they do not close this general connector or selector zero-gap.
'''
}
for heading,note in sections.items():
 assert heading in draft;draft=draft.replace(heading,heading+'\n\n'+note)
heading='## Iteration type/measure status'
note='''**L2R6 status: concrete iteration CLOSED; GENERAL TYPES ONLY.** `AdmittedCrossing` (2e60fc22) names foreign lifecycle and foreign own-child Insert/Retire/Remove shapes at actual source states. `AdmittedDistanceMove` (1fef241c) jointly owns located adjacency, exact full action-word interchange, trace-forcing, both declaration-free current cuts, observed exact-one total distance and RegistryExtensional endpoints. `iterationFixtures` (bc32a5a3) produces three real native moves (R over Begin2; then R/S over Begin2 in order, including actual S suffix replay). `fixtureIterations` (21df2ce5) closes actual six-edge 1→0 and seven-edge 2→1→0 chains on one-origin middle trails and applies `iterationEndpoint` (a4be84aa). No Finish2 suffix is added. Full-word adjacency is not advertised as a proof of frozen SameExternalOrchestration.

Checked obligation types in **L2R6IterationObligations**:
- `GeneralAdmittedMoveExistence` (84b38628): valid initial registry + FrontNormal + NeverRetired + all genuine ForcedRootPhase witnesses; selected authentic forced catalog root at positive distance; all earlier forced roots placed. Result owns a native selected-root adjacent move and transported front/control/phase invariants. Producer **produceAdmittedDistanceMove OPEN**.
- `GeneralDistanceIteration` (98c51dd6): same valid/front/control/phase input and `Accessible LT (totalDistance nameEq keyEq trail)` → `PhaseIterationResult` (52c83a64), owning actual output trace, finite DistanceIteration, zero distance, RegistryExtensional endpoint and invariants. Producer **normalizePhaseDistance OPEN**, no assumed per-step oracle.

The phase premise is necessary: an initially retired child may be removed before any lifecycle, followed by a non-forced front input and a key-forced input. Unrestricted front/never alone does not justify the old target or crossing that earlier root input. D9's floor preserves external order; phase additionally authenticates the intended actor core. Neither premise is silently declared true for all traces.

General move existence, all-kind native alternate applicability (including Insert/Insert), extensional replay and stable target/phase transport are unresolved. The two-observed-Dec insertion endpoint algebra remains L2R5 capital, not a newly produced native Insert/Insert square; no applicability attempt was made within D12 cap. Terminal earliest, general output placed/NF and zero⇔NF remain OPEN. The following older undefined normalizeAttached fragment is historical L2R5 proposal text, not the checked L2R6 type above.
'''
draft=draft.replace(heading,heading+'\n\n'+note)
draft=draft.replace('Tier 2 remains a design/specification debt.','Tier 2 remains PARTIALLY CHECKED with the exact L2R6 limits above; concrete classifier/anchor/placement/front observations and iteration instances are not the missing general producer proofs.')
draft=draft.replace('all referenced connectors here remain UNCHECKED','this original L2R5 field fragment remains UNCOMPILED; partial L2R6 counterparts are itemized above')
(ROOT/p).write_text(draft)
# The full Tier-1 fragments and original signature inventory are untouched.
for item in manifest['tier1Sections']:
 fragment=draft.split('### '+item['title']+'\n\n```idris\n',1)[1].split('```',1)[0]
 assert hashlib.sha256(fragment.encode()).hexdigest()==item['sha256']
# Validate generator's core map PLUS actual placement loop and new serialization.
tree=ast.parse(s)
base_map=ast.literal_eval(next(n.value for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='mapping' for t in n.targets)))
base_map.update(dict(placement));assert base_map==manifest['renamings']
print('SYNC PASS: Tier-1 hashes preserved; all 30 renamings serialized; Tier-2 remains partially checked')
