#!/usr/bin/env python3
"""D-only: derive the signed same-bundle Tier 1 patch and exact lane inventory.
No compiler, production/source edit, cache touch, main-worktree access, or lock.
The generated patch is proposed final production text, NOT a CP3 typecheck.
"""
from pathlib import Path
import datetime, difflib, hashlib, json, re, subprocess
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
P='research-tests/O6-L2R15-'
assert Path.cwd()==ROOT
cp3=ROOT/'src/DGamma/CP3.idr'; original=cp3.read_text(); lines=original.splitlines(keepends=True)
blob=subprocess.check_output(['git','hash-object',str(cp3)],text=True).strip()
assert blob=='2c697e532e83989de8591fa6a4378747c6a501c0'
def digest(data):return hashlib.sha256(data).hexdigest()
def dump(suffix,data):(ROOT/(P+suffix)).write_text(json.dumps(data,indent=2)+'\n')
def read(path):return (ROOT/path).read_text()
def block(text,heading):return text.split(heading,1)[1].split('```idris\n',1)[1].split('```',1)[0].rstrip()+'\n'
draft=read('research-tests/O6-L2R5-CP3-DIFF-DRAFT.md')
oldgrammar=block(draft,'### T1.1')
core_reason=oldgrammar.split('||| A contiguous trail',1)[0].rstrip()+'\n\n'
control_path='research-tests/O6-L2R7-Sources/DGamma/L2R7AttachedC.idr'
control=read(control_path)
control_grammar=control[control.index('||| New SAME-BUNDLE'):control.index('||| Sound forward inclusion')]
control_grammar=control_grammar.replace('||| Cross-bundle controls require the OPEN authenticated prefix/generation\n||| history connector. Local control witnesses also check actual source roots.', '||| Cross-bundle authenticated prefix/generation history is an open research\n||| obligation, not a blocker for this SAME-BUNDLE definition. Local control\n||| witnesses also check actual source roots.')
renames={
 'ActorLifecycleOnlyExtended':'ActorLifecycleCore',
 'OrderedForcedRootBundleC':'OrderedForcedRootBundle',
 'ForcedBundleEndC':'ForcedBundleEnd','ForcedBundleInsertC':'ForcedBundleInsert',
 'ForcedBundleRetireC':'ForcedBundleRetire','ForcedBundleRemoveC':'ForcedBundleRemove',
 'ActorLifecycleOnlyAttachedC':'ActorLifecycleOnly',
 'AttachedWithoutRootsC':'ActorWithoutForcedRoots','AttachedWithRootsC':'ActorWithForcedRoots',
 'LocatedOpenEpisodeBlockAttachedC':'LocatedOpenEpisodeBlock','MkLocatedOpenEpisodeBlockAttachedC':'MkLocatedOpenEpisodeBlock',
 'attachedCPreStart':'blockPreStart','attachedCStart':'blockStart','attachedCEnd':'blockEnd',
 'attachedCBefore':'traceBeforeBlock','attachedCOpening':'blockOpening','attachedCBody':'blockBody',
 'attachedCInstalled':'blockBodyInstalled','attachedCActorOnly':'blockActorOnly','attachedCAfter':'traceAfterBlock',
 'attachedCNoEarlier':'noEarlierLifecycle','attachedCNoLater':'noLaterLifecycle',
 'attachedCActiveAtFinal':'blockActiveAtFinal','attachedCDecomposition':'blockDecomposition',
 'BlockBeforeAttachedC':'BlockBefore','MkBlockBeforeAttachedC':'MkBlockBefore',
 'attachedCBetweenBlocks':'betweenBlocks','attachedCBlocksOrdered':'blocksOrderedInGlobal',
 'AttachedBundleOccurrenceC':'AttachedBundleOccurrence','MkAttachedBundleOccurrenceC':'MkAttachedBundleOccurrence',
 'cBundleActor':'bundleActor','cContainingBlock':'containingBlock','cCoreEnd':'coreEnd',
 'cMemberCore':'memberCore','cMemberExtended':'memberExtended','cMemberBundle':'memberBundle',
 'cMemberForced':'memberForced','cMemberSplit':'memberSplit','cBundleOccurrence':'bundleOccurrence',
 'cBundleOffset':'bundleOffset','cOffsetExact':'offsetExact','cMemberOrdinal':'memberOrdinal',
 'cMemberLowerBound':'memberLowerBound','cMemberUpperBound':'memberUpperBound',
 'AttachedNormalFormC':'AttachedNormalForm','MkAttachedNormalFormC':'MkAttachedNormalForm','cRootInBundle':'rootInBundle'}
def rename(text):return re.sub(r'\b('+'|'.join(map(re.escape,sorted(renames,key=len,reverse=True)))+r')\b',lambda m:renames[m[0]],text)
grammar=core_reason+rename(control_grammar).rstrip()+'\n'
located=rename(control[control.index('||| Full located block'):control.index('||| Physical order for complete')]).rstrip()+'\n'
ordered=rename(control[control.index('||| Physical order for complete'):]).rstrip()+'\n'
ordered=ordered.replace('complete attachedC bodies','complete attached bodies')
placement=block(draft,'### T1.3')
placement=placement.replace('||| R178 A8 REPLACEMENT specification, not an adapter to frozen CP3.\n||| Integration needs an OWNER choice of research-tower fork or production\n||| unfreeze. No conversion to the old strict CanonicalInputPlacement exists.', '||| A8 availability-aware canonical placement, owner-signed 2026-09-09.\n||| Root inputs preserve external order and move only through compatible\n||| declaration-free cuts. This does not imply old strict root-first placement.')
least=block(draft,'### T1.4').split('public export\nrecord AttachedBundleOccurrence',1)[0].rstrip()+'\n\n'
gap_path='research-tests/O6-L2R7-Sources/DGamma/L2R7AttachedCGap.idr'
gap=read(gap_path)
member=rename(gap[gap.index('||| Authenticated membership'):gap.index('||| Lifted conditional zero-gap')]).rstrip()+'\n'
support=least+member
relocated=''.join(lines[2092:2120]); assert relocated.startswith('public export\ntransitionCount')
# Coordinates always refer to unchanged CP3, never incrementally shifted text.
replacements=[(1781,1804,relocated+'\n'+grammar),(1821,1846,located+'\n'),(1871,1889,ordered+'\n'),(2093,2120,''),(3152,3195,support+'\n'+placement),(3265,3266,'  inputPlacement : CanonicalInputPlacement name key world error value nameEq keyEq\n    originalFinal supportOrder original canonicalTrace\n')]
updated=list(lines)
for first,last,text in sorted(replacements,reverse=True):updated[first-1:last]=[text]
proposed=''.join(updated)
assert proposed.count('record CanonicalInputPlacement\n')==1
assert proposed.count('data ActorLifecycleOnly :')==1
assert proposed.count('transitionCount : Transitions')==1
assert 'ForcedBundleRetire :' in proposed and 'ForcedBundleRemove :' in proposed
assert 'OrderedForcedRootBundle nameEq selected core [] bundle' in proposed
assert 'allRootInputsFirst :' not in proposed and 'rootGenerationBeforeLifecycle :' not in proposed
assert 'rootGenerationBeforeOwnLifecycle :' in proposed
assert '    originalFinal supportOrder original canonicalTrace\n' in proposed
assert original[original.index('||| Endpoint relation used by canonical deletion.'):original.index('record CanonicalSchedule')] in proposed
patch=''.join(difflib.unified_diff(original.splitlines(keepends=True),proposed.splitlines(keepends=True),fromfile='a/src/DGamma/CP3.idr',tofile='b/src/DGamma/CP3.idr',n=3))
(ROOT/(P+'CP3-TIER1-SIGNED-DIFF.patch')).write_text(patch)
# Import closure over the current lane's tracked files plus owned pending/final L2R15 sources.
paths=set(subprocess.check_output(['git','ls-files','*.idr'],text=True).splitlines())
paths.update(str(p.relative_to(ROOT)) for p in (ROOT/(P+'Sources/DGamma')).glob('*.idr'))
items={}
old_names={'ActorLifecycleOnly','ActorLifecycleEnd','ActorLifecycleStep','ActorYieldedRegistrationStep','CanonicalInputPlacement','MkCanonicalInputPlacement','allRootInputsFirst','rootGenerationBeforeLifecycle','blockActorOnly'}
introduced={'ActorLifecycleCore','AttachedRelease','AttachedReason','OrderedForcedRootBundle','ForcedRootInput','forcedRootLeast','AttachedBundleOccurrence','AttachedNormalForm','rootDeclaredProvisionsFree','rootInputAtSource','AvailabilityTrace','rootCutCompatible','EarliestAvailableRootBirth'}
for path in sorted(paths):
 p=ROOT/path
 if not p.is_file() or not path.startswith(('src/','research/','research-tests/')):continue
 text=p.read_text(); module=re.search(r'^module\s+(\S+)',text,re.M)
 if not module:continue
 code='\n'.join(line for line in text.splitlines() if not line.lstrip().startswith('--') and not line.lstrip().startswith('|||'))
 hits=sorted(n for n in old_names if re.search(r'\b'+re.escape(n)+r'\b',code))
 declarations=set(re.findall(r'^(?:public export\s+|export\s+)?(?:record\s+|data\s+|0\s+)?([A-Za-z][A-Za-z0-9_]*)\s*:',code,re.M))
 declarations.update(re.findall(r'^(?:record|data)\s+([A-Za-z][A-Za-z0-9_]*)',code,re.M))
 items[path]=dict(path=path,module=module[1],imports=re.findall(r'^import\s+(?:public\s+)?(\S+)',text,re.M),sourceSHA256=digest(p.read_bytes()),oldSurfaceNames=hits,productionNameCollisions=sorted(declarations&introduced))
affected={'DGamma.CP3'}
while True:
 new=affected|{r['module'] for r in items.values() if any(i in affected for i in r['imports'])}
 if new==affected:break
 affected=new
research=[r for r in items.values() if r['module'] in affected and r['path'].startswith(('research/','research-tests/'))]
production=[r for r in items.values() if r['module'] in affected and r['path'].startswith('src/')]
repair=[r for r in research if r['oldSurfaceNames'] or r['productionNameCollisions']]
metadata=dict(generatedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),laneHead=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),cp3Blob=blob,cp3SHA256=digest(original.encode()),candidateSHA256=digest(proposed.encode()),patchSHA256=digest(patch.encode()),ownerSigned='2026-09-09',grammar='checked L2R7 attachedC SAME-BUNDLE controls under production names',typecheckedInCP3=False,oldCoordinates=[dict(first=a,last=b) for a,b,t in replacements],renames=renames,scope='Exact current-lane import closure; main R205 must refresh at its own production head. Every listed path requires recheck; repair candidates are lexical old-API uses/new-name collisions, not invented compiler failures.',researchRecheck=research,productionRecheck=production,researchRepairCandidates=[r['path'] for r in repair],researchCount=len(research),productionCount=len(production),standDown='No lane2 compiler after final gate until R205 serialized rebuild finishes; next lane shift re-seeds build/ from rebuilt main.')
dump('CP3-REBUILD-INVENTORY.json',metadata)
overlay=ROOT/(P+'CP3-DIFF-DRAFT-OVERLAY.md');text=overlay.read_text().split('\n## Signed Tier 1 — consolidated copy-ready patch',1)[0].rstrip()
append='''

## Signed Tier 1 — consolidated copy-ready patch

**Tier 1 diff signable and signed by the owner on 2026-09-09; Tier 2 = open research obligations**.

Owner's 21:55 UTC unfreeze and supervisor's explicit grammar choice (B) supersede older “NOT SIGNABLE” / deferred-owner-gate language in L2R5 and L2R10–14. They do not manufacture any Tier 2 proof. This lane changes documentation only. The following is ONE exact final CP3 patch, not alternative fragments or undefined Tier 2 field placeholders. CP3 typechecking and downstream repairs belong to main R205; this patch has NOT been checked in CP3 here.

### Coordinates and reconciliation

All coordinates refer to unchanged `src/DGamma/CP3.idr`, blob `2c697e532e83989de8591fa6a4378747c6a501c0` (still the lane baseline blob):

1. Move **2093–2120**, byte-exact `transitionCount`, `LocatedActionOccurrence`, `locatedActionOrdinal` and separators, immediately before the replacement of **1781–1804**. The patch deletes the old copy; no duplicate or forward-reference cycle.
2. **1781–1804**: replace old actor-only grammar with source-aware `ActorLifecycleCore` plus `AttachedRelease`, release/barrier `AttachedReason`, **same-bundle controls** `OrderedForcedRootBundle` and attached `ActorLifecycleOnly`. This consolidates L2R5 T1.1 with the CHECKED T1.C/L2R7 grammar; the INSERT-only alternative is NOT retained under production names.
3. Replace **1821–1846** and **1871–1889** separately with the complete attachedC located/order records under CP3 names. Keep intervening `NoLifecycleBy`, `prefixToBlockOpening` and `prefixThroughBlock` definitions. `betweenBlocks` starts AFTER the entire core+bundle-with-controls. Gap zero is NOT a definition. O19 keeps exactly `0 safetyBlocksAdjacent : (transitionCount (betweenBlocks safetyBlocksOrdered) = 0)`; its right-opening/no-generated-child/native-replay premises are not removed or weakened.
4. Replace **3152–3195** with generic least forced/barrier closure, full controls-bundle membership/NF specification types and the exact availability-aware helpers plus final `CanonicalInputPlacement`. This is A8 current-cut+terminal-earliest placement, **not** strict all-root-first and **not** undefined L2R5 Tier 2 fields. Own-root lifecycle and unchanged child-generation clauses remain. `RootInputsBeforeLifecycle` stays the strict predicate for explicitly strict domains, but is no longer a canonical-placement field.
5. Replace only **3265–3266** in `CanonicalSchedule` to thread `original`. Leave registration/effect/control/vestigial relations, `SameExternalOrchestration`, `RootOrchestrationStep`, native evaluator/guards and `ConfluenceResult`/`confluenceTheorem` conclusion text unchanged. New canonical field semantics require dependent rechecking; existing proof holes are not certified closed.

Quantities: installedness, actor grammar, no-earlier/no-later and final activity specification fields become **0** exactly as in checked attachedC. Native states/opening/body/decomposition data remain runtime data; no linear runtime API is added. Placement trace/state indices are erased and `original` is explicit. All old actor-only constructors are replaced, with no legacy compatibility alias or false attached→core coercion.

**Adjacent to the grammar:** wrapper history is EMPTY; only an authenticated root insertion grows it. Root Retire/Remove require membership in that SAME bundle plus actual source lookup and Root parent. Cross-bundle authenticated prefix/generation control history is a **research obligation, not a blocker** for this signed same-bundle scope. `EarlierForcedRoot` / `OrderForces` provide local ordered barriers / generic least closure, respectively; they are not a supplied global seed oracle.

```diff
'''+patch+'''```

The standalone identical patch is `research-tests/O6-L2R15-CP3-TIER1-SIGNED-DIFF.patch`; exact hashes, complete rename map and graph inventory are in `research-tests/O6-L2R15-CP3-REBUILD-INVENTORY.json`.

### Checked carry-over versus required re-check

“Carries over” here means the mathematical statement/body has the disclosed structural rename; it does **not** mean a fresh production PASS. Every item must be rechecked after production rehome and import/name disambiguation.

| Checked research theorem/fixture | Production-name carry-over | Re-check/repair required |
|---|---|---|
| `research-tests/O6-L2R7-Sources/DGamma/L2R7AttachedCGap.idr:attachedCZeroGapInNormalForm` (cbc6d783) | Exact same-bundle controls statement under `LocatedOpenEpisodeBlock`, `BlockBefore`, `AttachedBundleOccurrence`, `AttachedNormalForm`; coverage, physical offset and UNIVERSAL interval separation unchanged | Rename types/accessors through inventory map; recheck actual proof. No unconditional selector zero-gap claim. |
| `research-tests/O6-L2R7-Sources/DGamma/L2R7ControlFixture.idr:controlFixture` (28c7cc15) | Same ten native edges; parent [0,8), actor2 [8,10), R/S/Retire3/Remove3 inside complete bundle, physical gap0 | Recheck constructor/projection map plus ControlStates/Execution/Trace dependencies; no new native path invented. |
| `research-tests/O6-L2R7-Sources/DGamma/L2R7Classifier.idr:classifyForcedSound` (190703a3), `classifyForcedComplete` (e353c4cc), `observeForcedClassification` (52a22cb3) | Classifier correspondence to independent least `ForcedRootInput` is unchanged; barrier closure is preserved | Resolve local/re-homed closure names and recheck L2R3ForcedClosure/L2R6Forced/L2R6ForcedScan/L2R7Classifier and fixtures. These are NOT phase or normalizer producers. |
| `research-tests/O6-L2R3-Sources/DGamma/L2R3ForcedClosure.idr:forcedRootLeast` | Generic leastness body is included verbatim in the patch | Recheck at new defining module/direct imports; native seed/assignment linkage stays research. |
| `research/DGamma/CP5AvailabilityAwarePlacement.idr` | Final A8 fields and executable helpers carry over by replacement-name mapping | Recheck/remove duplicate-helper ambiguity and migrate actual callers; no coercion to strict root-first fields. |
| `research/DGamma/CP5ActorLifecycleOnlyExtended.idr:actorLifecycleOnlyIntoExtended` and `research-tests/O6-L2R3-Sources/DGamma/L2R3Attached.idr:oldIntoAttached` | **DO NOT carry over unchanged:** domain name now means attached controls, not old actor-only core | Repair/remove the obsolete forward-domain adapters and migrate consumers honestly; never implement a false reverse attached→core coercion. |
| L2R10–15 release, replay, packet, native-shape and result-constructor proofs | Exact previously checked scopes remain research capital; none changes the signed grammar or adds pending Tier 2 fields | Recheck complete transitive graph below; old native-shape/local/global assumptions remain visible. |

L2R10's restricted lifecycle role, L2R11's native occurrence/packet route, L2R12's fixed phases and actual R191 fold replay, L2R13's native move/suffix frames, L2R14's producer-built fixed iteration/shape square, and L2R15's path decoder/suffix scans/eight native orchestration shapes are reconciled in the status sections above. None is retroactively promoted into missing all-phase, all-kind, global-distance, four-common-lifecycle-payload, NF/selector or normalizer theorems: each is a **research obligation, not a blocker** for Tier 1 unfreeze.

### Exact research re-check / repair inventory

This is the import-reachable closure from `DGamma.CP3` over the current lane's tracked `src/`, `research/`, `research-tests/` plus owned L2R15 sources. It is NOT an inventory of unseen new main-lane commits. R205 must refresh it at its actual production head before serialized rebuilding. All listed paths require recheck. A `*` means lexical old-API/constructor references or definitions colliding with newly production-owned names: mandatory migration review/repair candidate, NOT a claim that a compiler failure has already occurred. The JSON records per-path imports, source hashes, exact hit names and all affected production paths as well.

'''
append+=f'**{len(research)} research paths** ({sum(r["path"].startswith("research/") for r in research)} research + {sum(r["path"].startswith("research-tests/") for r in research)} research-tests); **{len(repair)}** marked repair candidates.\n\n'
repair_paths={r['path'] for r in repair}
append+='\n'.join('- '+('**\\*** ' if r['path'] in repair_paths else '')+'`'+r['path']+'`' for r in research)
append+='''

### R205 serialized rebuild handoff

No shared heavy lock or rebuild-window protocol exists: the historical lock paragraph in L2R5 is superseded. After this lane's final gate, **lane2 runs NO compiler until main R205 finishes its serialized rebuild**. The next lane shift must re-seed `build/` from the rebuilt main tree; these old-definition TTCs must not be reused as post-unfreeze proof evidence. No lane2 post-gate “quick check”. Main retains its own bounded monitored one-compiler/rebuild policy and refreshes the graph/statement map at the exact production head. The lane does not touch the main worktree or start its rebuild.
'''
overlay.write_text(text+append)
assert cp3.read_text()==original
print('D-only signed patch/inventory generated; CP3 unchanged; research paths',len(research),'repair candidates',len(repair),'candidate NOT typechecked')
