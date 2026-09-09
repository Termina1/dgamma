#!/usr/bin/env python3
"""Generate docs-only Tier-1 rehome text and a read-only signature inventory.
No source, cache, compiler, git staging or main worktree writes. Tier 2 is
uncompiled specification text kept in its separately labeled companion.
"""
import hashlib, json, pathlib, re, subprocess
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
assert pathlib.Path.cwd()==ROOT
BASE='769d332d'
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def sha(text): return hashlib.sha256(text.encode()).hexdigest()
def text(path): return (ROOT/path).read_text()
def cut(path,start,end=None):
 s=text(path);a=s.index(start);b=s.index(end,a) if end else len(s);return s[a:b].rstrip()+'\n'
cp='src/DGamma/CP3.idr';old=text(cp)
assert git('rev-parse',BASE+':'+cp)==git('rev-parse','HEAD:'+cp)
core=cut('research/DGamma/CP5ActorLifecycleOnlyExtended.idr','public export\ndata ActorLifecycleOnlyExtended','||| Only the SOUND')
attached=cut('research-tests/O6-L2R3-Sources/DGamma/L2R3Attached.idr','public export\nrecord AttachedRelease','||| Sound extended-to-attached')
blocks=cut('research-tests/O6-L2R3-Sources/DGamma/L2R3Attached.idr','public export\nrecord LocatedOpenEpisodeBlockAttached')
mapping={'ActorLifecycleOnlyExtended':'ActorLifecycleCore','ExtendedLifecycleEnd':'CoreLifecycleEnd','ExtendedLifecycleStep':'CoreLifecycleStep','ExtendedYieldedRegistrationStep':'CoreYieldedRegistrationStep','ExtendedChildRetireStep':'CoreChildRetireStep','ExtendedChildRemoveStep':'CoreChildRemoveStep','ActorLifecycleOnlyAttached':'ActorLifecycleOnly','AttachedWithoutRoots':'ActorWithoutForcedRoots','AttachedWithRoots':'ActorWithForcedRoots','LocatedOpenEpisodeBlockAttached':'LocatedOpenEpisodeBlock','BlockBeforeAttached':'BlockBefore','attachedPreStart':'blockPreStart','attachedStart':'blockStart','attachedEnd':'blockEnd','attachedBefore':'traceBeforeBlock','attachedOpening':'blockOpening','attachedBody':'blockBody','attachedInstalled':'blockBodyInstalled','attachedActorOnly':'blockActorOnly','attachedAfter':'traceAfterBlock','attachedNoEarlier':'noEarlierLifecycle','attachedNoLater':'noLaterLifecycle','attachedActiveAtFinal':'blockActiveAtFinal','attachedDecomposition':'blockDecomposition','attachedBetweenBlocks':'betweenBlocks','attachedBlocksOrdered':'blocksOrderedInGlobal'}
def rename(s):
 for a,b in sorted(mapping.items(),key=lambda p:-len(p[0])): s=s.replace(a,b)
 return s
placement=cut('research/DGamma/CP5AvailabilityAwarePlacement.idr','public export\nrootDeclaredProvisionsFree')
for a,b in [('MkAvailabilityAwareCanonicalInputPlacement','MkCanonicalInputPlacement'),('AvailabilityAwareCanonicalInputPlacement','CanonicalInputPlacement'),('availableRootGenerationFresh','rootGenerationFresh'),('availableChildGenerationBeforeOwnLifecycle','childGenerationBeforeOwnLifecycle')]: placement=placement.replace(a,b)
closure=cut('research-tests/O6-L2R3-Sources/DGamma/L2R3ForcedClosure.idr','public export\ndata ForcedRootInput')
coverage=rename(cut('research-tests/O6-L2R3-Sources/DGamma/L2R3AttachedGap.idr','public export\nrecord AttachedBundleOccurrence','||| A nonempty gap'))
moved='\n'.join(old.splitlines()[2092:2120])+'\n'
sections=[('T1.0 — unchanged forward dependency relocation (CP3:2093–2120)',moved),('T1.1 — actor core + attached grammar (replace CP3:1781–1804)',rename(core)+'\n'+rename(attached)),('T1.2 — full located/order records (replace CP3:1821–1846 and 1871–1889)',rename(blocks)),('T1.3 — availability-aware predicates and placement (replace CP3:3152–3195; helpers before record)',placement),('T1.4 — generic least closure and bundle-membership support types (new canonical-definition support)',closure+'\n'+coverage)]
# Syntactic DIRECT statement dependencies: full record/data signatures, function
# signature only (not body references). This is not a transitive typechecker.
words=['ActorLifecycleOnly','RootInputsBeforeLifecycle','CanonicalInputPlacement','LocatedOpenEpisodeBlock','BlockBefore','CanonicalSchedule','NoRootOrchestration']
pat=re.compile(r'^(?:(?:0|1) )?([A-Za-z_]\w*)\s*:|^(?:record|data)\s+([A-Za-z_]\w*)',re.M)
rows=[]
paths=list((ROOT/'research/DGamma').glob('*.idr'))+list((ROOT/'src/DGamma').glob('*.idr'))
for folder in ['O6-L2R1-Sources','O6-L2R2-Sources','O6-L2R3-Sources','O6-L2R4-Sources']:
 paths+=list((ROOT/'research-tests'/folder/'DGamma').glob('*.idr'))
for p in sorted(set(paths)):
 s=p.read_text();matches=list(pat.finditer(s))
 for i,m in enumerate(matches):
  name=m[1] or m[2];end=matches[i+1].start() if i+1<len(matches) else len(s);piece=s[m.start():end]
  if m[1]:
   rhs=re.search(r'^'+re.escape(name)+r'(?:\s|\{)',piece[len(m[0]):],re.M)
   if rhs:piece=piece[:len(m[0])+rhs.start()]
  piece=re.sub(r'(?:\n(?:public export|export|private|%[^\n]*|\|\|\|[^\n]*|--[^\n]*)\s*)+$','\n',piece).rstrip()+'\n'
  refs=[w for w in words if re.search(r'\b'+w+r'\b',piece)]
  if refs:
   rows.append(dict(path=str(p.relative_to(ROOT)),declaration=name,line=s[:m.start()].count('\n')+1,directCanonicalNames=refs,statementSHA256=sha(piece),classification='direct signature dependency; semantic obligations require human review',frozen=True))
inventory=dict(base=git('rev-parse',BASE),cp3Blob=git('rev-parse','HEAD:'+cp),status='READ-ONLY statement inventory, not compiler evidence or exhaustive transitive closure',method='top-level record/data statement or function signature lexical reference; body-only references excluded',scope='lane worktree snapshot only; concurrent main/R196 not read',count=len(rows),declarations=rows)
(ROOT/'research-tests/O6-L2R5-CP3-STATEMENT-FIDELITY.json').write_text(json.dumps(inventory,indent=2)+'\n')
header='''# L2R5 — CP3 DIFF DRAFT for owner signature

## Signature status (one-page decision table)

**NO production edit authorized or performed. NOT YET SIGNABLE AS A COMPLETE CURE.** Tier 1 below is exact proposed text obtained from checked research declarations by the disclosed renamings; it has NOT been compiled in CP3. Tier 2 is explicitly UNCHECKED specification text with unresolved connector parameters. A signature today could approve the Tier-1 candidate design and rebuild plan, **not** certify a normalizer, all-role retirement replay, general gap coverage, O19 adjacency or Theorem 73.

| Proposed CP3 change | Checked backing | Unchecked / blocked by |
|---|---|---|
| Move transitionCount / LocatedActionOccurrence / locatedActionOrdinal before grammar | Existing CP3 declarations, byte-exact move below | New ordering/typecheck not performed; no semantic change intended |
| ActorLifecycleOnly becomes extended core + forced-root bundle | L2R3 4974a6f9; old→extended→attached d2b26a9a / 0f19676d | Global last-release assignment, forced closure linkage, actual R191 whole relocation |
| Own-child Retire/Remove in core | R192 971fedfc (grammar); block-copy file later changed d3e6d73e; source lookup + parent witnesses | L2R5 B5 provider wall prevents lifecycle/full R191 replay |
| Full LocatedOpenEpisodeBlock / BlockBefore rehome | L2R3 a7799047 / ce0c13bd; real small/barrier blocks 1b7e1eeb / 224988a1 | Maximal nonoverlap/decomposition globally; quantities change explicitly listed |
| CanonicalInputPlacement inherited availability-aware clauses | R178 4e1043fe; L2R2 smallRootEarliest; L2R5 5822f06e / cb60b7d7 current-cut facts | Terminal earliest on all births, front-normal and last-release connectors below |
| Least forced set, trace-linked classifier, anchor assignment | Generic leastness 7737a019; local KeyReleased / EarlierForcedRoot | TIER 2: no compiled global classifier/assignment |
| CanonicalSchedule.inputPlacement original-trace index | Inherited research placement record shape | In-file constructor and all callers must be adapted/rechecked; no constructor proof here |
| RootInputsBeforeLifecycle replacement scope | Barrier-order impossibility 9c7c0a7c; old strict reading cannot hold | TIER 2 front-normal; non-insert root-action/generation disposition remains explicit |
| O19 safetyBlocksAdjacent over full attached blocks | L2R4 exact unchanged fixture applications 58b71b4f / b042b76e | General selector zero-gap still open; do not remove/assume this field |
| Normalizer endpoint relation and iteration | RegistryExtensional 0fbc3d33, snapshot embedding 21453f7c, two-insert endpoint algebra 71f6de67, Retire transport c60f315a | Native Insert/Insert applicability, remaining action transport, swap existence/distance iteration OPEN |
| Raw catalog generated from actual traces | L2R5 ef9b9f9b; both full fixtures 8c603e3b | NOT AttachedNormalForm; catalog→placed-bundle assignment still open |

## Frozen baseline and exact edit coordinates

All coordinates are OLD line numbers in this lane's unchanged CP3 at 769d332d. CP3 git blob: **CP3_BLOB**. Main worktree was never accessed. R196's concurrent changes are not silently imported into this proposal. No evaluator, O-Insert provision guard, registration scanner, vestigial relation, effect/control equivalence or confluence conclusion changes are proposed.

1. MOVE CP3:2093–2096 (transitionCount), :2098–2115 (LocatedActionOccurrence, including docstring), :2117–2119 (locatedActionOrdinal), preserving the separating blank lines through2120, to immediately BEFORE the grammar at1781. All bytes unchanged. These declarations depend only on existing transition/state primitives and appendTransitions, not block types. This avoids a forward-reference cycle when AttachedRelease is rehomed from a research module that previously imported CP3.
2. REPLACE :1781–1804 with T1.1. New core keeps the research own-child lookup/parent witnesses; attached wrapper keeps actual checked root bundle and empty initial barrier history.
3. REPLACE full record text :1821–1846 and :1871–1889 with T1.2 in their respective original locations. Keep NoLifecycleBy, prefixToBlockOpening (:1848–1858) and prefixThroughBlock (:1860–1869) under their existing names; their bodies are unchanged. Do not paste both records across/deleting those intervening definitions.
4. REPLACE :3152–3195 with T1.3's final record; insert its preceding helper declarations before that record, after RootOrchestrationStep/SameExternalOrchestration/located-occurrence definitions. Avoid importing a research module back into production. T1.4 support declarations can precede the placement record after block definitions.
5. In CanonicalSchedule:3265–3266, use the exact replacement field below. canonicalBlock (:3256–3257), blocksFollowOrder (:3258–3263), lifecycleCoverage (:3264), sameInputs (:3249), registration/endpoint/tree fields retain their text; their types now refer to the rehomed grammar. ConfluenceResult (:3756ff), confluenceTheorem (:3785ff) retain their text and endpoint relations.

```idris
  inputPlacement : CanonicalInputPlacement name key world error value nameEq keyEq
    originalFinal supportOrder original canonicalTrace
```

### Renaming and quantity fidelity

`ActorLifecycleOnlyExtended` → `ActorLifecycleCore`; Extended* constructors → Core*. `ActorLifecycleOnlyAttached` → `ActorLifecycleOnly`; AttachedWithoutRoots/AttachedWithRoots → ActorWithoutForcedRoots/ActorWithForcedRoots. Located/order record names and accessor names map back to their existing CP3 names (full machine map in REHOME-MANIFEST). No reverse coercion to the old grammar is introduced, and no legacy compatibility alias is silently preserved.

The full attached research block copy erases installedness, actor grammar, no-earlier/no-later and active-at-final specification fields, whereas old CP3:1838–1843 stored those proofs unrestricted. **This proposed quantity change is explicit and needs call-site review**; runtime body/states/opening/trace decomposition data remain. The inherited placement record also erases trace/state indices and adds an explicit original trace. These are checked-backed research choices, NOT already validated production changes. Existing old-grammar induction constructors are removed/replaced: exhaustive consumers need new cases, not wildcard forwarding.

## Tier 1 — exact checked-backed proposed text

The source-origin table is: core = CP5ActorLifecycleOnlyExtended:17–65; AttachedRelease/AttachedReason/OrderedForcedRootBundle/ActorLifecycleOnlyAttached = L2R3Attached:20–122; located/order copies = L2R3Attached:147–168 /173–193; placement helpers/record = CP5AvailabilityAwarePlacement:17–148; least family/theorem = L2R3ForcedClosure:14/27; bundle/NF records = L2R3AttachedGap:21/48. See exact current locations/hashes in the manifest. Comments copied from research retain their historical qualifications; they must not be read as production proof claims.
'''.replace('CP3_BLOB',git('rev-parse','HEAD:'+cp))
footer='''
## Root orchestration and O19 reading (statements not silently weakened)

CP3:2000–2034 RootOrchestrationStep and :2055–2091 SameExternalOrchestration are **UNCHANGED**, including root Retire/Remove classification and exact relative order. Child Insert/Retire/Remove remain internal only with their existing provenance disciplines. Forced roots are still external root inputs even when physically attached to a parent's block. Never reverse R/S to manufacture all-root-first placement. CP3:2048–2053 old RootInputsBeforeLifecycle is NOT simply relabeled: its unrestricted canonical use must be replaced by Tier-2 front-normal scope. Keep it as the strict predicate while old statements remain frozen; eventual removal/replacement requires the owner-approved dependent migration, not a false coercion.

O19 source `research/DGamma/CP5O19SurfaceSpike.idr:113–145` contains the exact field:

```idris
  0 safetyBlocksAdjacent : (transitionCount (betweenBlocks safetyBlocksOrdered) = 0)
```

**Keep this text and its strength.** After rehome, `safetyBlocksOrdered` (:130–133) compares the FULL attached bodies. `betweenBlocks` begins after the trailing forced bundle, never after only the lifecycle core. List adjacency alone is not physical adjacency. `safetyRightOpeningEarly` (:140–144), no-generated-child constraints (:134–139), registration provenance and native replay remain required. The rehome does not prove their preservation for forced roots. Do not edit O19 this shift; migration must recheck every consumer. L2R4 small/barrier applications use actual physical offsets, universal no-straddling and honest residual-gap NF; arbitrary selector zero-gap remains open.

## Statement-fidelity table and frozen declaration inventory

`O6-L2R5-CP3-STATEMENT-FIDELITY.json` enumerates **DIRECT signature** references to changed canonical types/predicates in src/, research/, and retained L2R1–L2R4 source trees, with file, declaration, old line, referenced canonical names and statement SHA256. The extraction excludes body-only references; it is not an exhaustive transitive typechecker. No listed statement was edited. After owner approval, regenerate against the exact production base and include transitive import rebuild coverage.

| Frozen declaration/family | Fidelity under proposed rehome | Required disposition (no edit here) |
|---|---|---|
| CP3 ActorLifecycleOnly + its constructors | INCOMPATIBLE API/domain: new nameEq index, core + bundled roots, new constructors | No old theorem body may be counted as proved without new cases |
| CP3 LocatedOpenEpisodeBlock / prefixToBlockOpening / prefixThroughBlock / BlockBefore | Same physical decomposition meaning, enlarged body; explicit proof erasure delta | Recheck every construction/structural induction; no zero by definition |
| CP3 CanonicalInputPlacement / CanonicalSchedule | Original-trace index added; strict global-before-lifecycle replaced by current availability/terminal earliest + pending front-normal connectors | Exact signature migration; no implicit coercion from revised to strict placement |
| CP3 ConfluenceResult / confluenceTheorem | Text unchanged; canonical schedule field semantics change transitively; final pointwise/vestigial relations unchanged | Revalidate theorem correspondence and call sites; no new proof claim |
| CP3StatementChecks canonical constructors/projections (:3398–3445,3548–3549,3586–3738) | Constructor fields/grammar matches become incompatible | Adapt only under owner signature, then serialized recheck |
| CP5ConfluenceCanonicalSortSpike root-hoist/initial-placement/O17 statements | Canonical schedule/input-placement references change; frozen holes remain holes | Availability + outer-order/distance proof required; do not relabel a conditional fold |
| CP5O19SurfaceSpike ActorBlockDecomposition / AdjacentActorSwapSafety / actorBlockTrace | Larger attached blocks; adjacency field exact strength unchanged | Native safety and selector projections must use entire block; general zero-gap debt visible |
| CP5O19OriginalBlockClassSpike / CP5O19ReachedBlocksSpike | Old grammar inductions no longer exhaustive | Own-child controls and forced-root bundle cases need proofs |
| CP5O20InversionChildSafetySpike / CP5O20RightOpeningTransportSpike | Frozen O20 statements indirectly reference new blocks; old two-constructor inductions incompatible | Do not weaken statements or consume unproved cases; distinct main-lane owner gate |
| CP5ConfluenceCrossTraceSpike / CP5ConfluenceRenamingCompositionSpike canonical-capital references | Transitive schedule meaning changes, endpoint historical/current-name distinction unchanged | A11 supported/history repair remains separate; no fresh current-name equation for removed births |
| CP5ActorLifecycleOnlyExtended.actorLifecycleOnlyIntoExtended and L2R3Attached.oldIntoAttached | Their domain currently names the OLD ActorLifecycleOnly; rehome changes that name's meaning | Cannot blindly reuse forward inclusion as a reverse attached→core coercion; owner must revise research migration strategy |
| All remaining direct frozen signatures | See machine inventory, one row per declaration | Typechecked revalidation required; byte equality here is not future proof validity |

## Serialized seeded rebuild plan / R196 coordination

Pointer: `O6-R192-CP3-REBUILD-INVENTORY.json` (old PLAN ONLY: 163 src,90 research,154 research-tests affected-module entries; baseline34b21c9, frozen CP3 blob recorded there), plus the protocol in `O6-R192-A8-A10-DECISION-MEMO.md`. This is not evidence of any L2R5 compiler series. R196 main-lane LocalDiamond producer-contract work and its expected241-module serialized recheck are concurrent; **no completed R196 receipt is available to this draft**. Obtain the owner's exact R196 experience/peak/failed-module/resume receipts before scheduling CP3 unfreeze. Do not access/build the main worktree from this lane.

Before owner-signed production change: refresh the import/signature inventory at the actual base; freeze old/new CP3 hashes, exact symbol/quantity/statement map and leaf-before-dependent plan; preserve build/ and seeded TTCs. Acquire shared `/tmp/dgamma-heavy.lock` with JSON owner for ≥19GiB checks. Run one detached/monitored compiler at a time,48GiB hard RSS stop, exact target Building line/hash/mtime receipt, no mass touch/deletion/cold rebuild. Compile changed CP3 with seeded prerequisites, then affected production modules, then research consumers in dependency order. If a single module approaches48GiB, stop/gate and redesign rather than retry a from-scratch package (historical ~138GiB wall). Negative fixtures require frozen symbol+diagnostic contracts, not exit-only acceptance. A monitored seeded package pass is only a final separately authorized validation, not a fallback.

**Main-lane fix candidate, NOT a lane edit:** lifecycle replay roles need an observed retired-head guard at the source. L2R4 B7 and L2R5 B5 both exhausted3/3; the new explicit-Bool observation record still cannot produce the native retired-head equation due to hidden dependent projection indices. A base-module producer-owned observed guard (not another wrapper) needs an owner-gated source design/change and its serialized dependent rebuild, informed by R196. No requested source edit is made here.

## Review/owner decision

Tier 1 is proposed exact syntax backed by the cited variant declarations, not a fresh CP3 PASS. Tier 2 remains a design/specification debt. Do not sign this as a complete production unfreeze until native normalizer existence/transport, trace-linked classification/assignment, lifecycle replay, full front-normal/placed-gap coverage and general selector zero-gap are resolved or the owner explicitly narrows what the production specification promises. No frozen theorem or conclusion is silently weakened in this draft.
'''
manifest=dict(base=git('rev-parse',BASE),cp3Blob=git('rev-parse','HEAD:'+cp),status='PROPOSED DOC TEXT ONLY; CP3 not edited/compiled',renamings=mapping,movedOldRanges=[[2093,2096],[2098,2115],[2117,2119]],movedCombinedSHA256=sha(moved),tier1Sections=[dict(title=t,sha256=sha(s),lines=len(s.splitlines())) for t,s in sections],directStatementInventoryCount=len(rows))
manifest['checkedSourcePaths']=['research/DGamma/CP5ActorLifecycleOnlyExtended.idr','research-tests/O6-L2R3-Sources/DGamma/L2R3Attached.idr','research/DGamma/CP5AvailabilityAwarePlacement.idr','research-tests/O6-L2R3-Sources/DGamma/L2R3ForcedClosure.idr','research-tests/O6-L2R3-Sources/DGamma/L2R3AttachedGap.idr']
manifest['checkedSourceSHA256']={p:sha(text(p)) for p in manifest['checkedSourcePaths']}
(ROOT/'research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
draft=header+'\n'.join('### '+title+'\n\n```idris\n'+s+'```\n' for title,s in sections)+'\n---\n\n'+text('research-tests/O6-L2R5-CP3-TIER2-CLAUSES.md')+'\n'+footer
(ROOT/'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md').write_text(draft)
print(json.dumps({'draftLines':len(draft.splitlines()),'directSignatureDeclarations':len(rows),'cp3Unchanged':True,'tier1NotCompiled':True,'tier2NotSignable':True}))
