#!/usr/bin/env python3
"""Prepare the L2R16 final plan at an idle compiler boundary.
Compiler-free: source freeze, exact-hash inherited import-invalidation audit,
new-module topological targets and scope/status snapshots. Adapted from L2R15.
"""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=Path('/tmp/dgamma-l2r16');P='research-tests/O6-L2R16-'
assert Path.cwd()==ROOT

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
assert not git('diff','--cached','--name-only').strip()
assert not git('diff','--name-only','--','*.idr').strip()
subprocess.run(['python3','-I','research-tests/run-l2r16-recheck.py','--state-only'],cwd=ROOT,check=True)
state=json.loads((ROOT/(P+'RECHECK-STATE.json')).read_text())
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
byid={r['unit']:r for r in records}
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT']
changes={}
for r in source_receipts:changes[r['paths'][0]]=r['timestampUTC']
rows={r['module']:r for r in state['modules']}
invalid=[]
for row in state['modules']:
 if row['status'] not in ['PASSED','REPAIRED']:continue
 receipt=byid[row['lastReceipt']]
 late=[d for d in row['ownDependencies'] if rows[d]['path'] in changes and changes[rows[d]['path']]>receipt['start']]
 if late:invalid.append(dict(module=row['module'],path=row['path'],changedDependencies=late,lastReceipt=row['lastReceipt']))
new=sorted((ROOT/(P+'Sources/DGamma')).glob('*.idr'));assert len(new)==12
new_names={'DGamma.'+p.stem for p in new}
entries=[]
for p in new:
 text=p.read_text();deps=[m for m in re.findall(r'^import\s+(\S+)',text,re.M) if m in new_names]
 entries.append(dict(module='DGamma.'+p.stem,path=str(p.relative_to(ROOT)),sourceSHA256=sha(p),ownDependencies=deps))
ordered=[];done=set()
while len(done)<len(entries):
 choices=[e for e in entries if e['module'] not in done and set(e['ownDependencies'])<=done]
 assert choices
 e=min(choices,key=lambda e:(len(e['ownDependencies']),e['module']));ordered.append(e);done.add(e['module'])
for item in invalid:
 p=ROOT/item['path'];ordered.append(dict(module=item['module'],path=item['path'],sourceSHA256=sha(p),reason='changed dependency after preceding consumer check',ownDependencies=rows[item['module']]['ownDependencies']))
status={
 'T1':'total independent-key component constructor',
 'T2':'total literal native snapshot accessor; no extra-edge claim for fallback indices',
 'T3':'native obligation record TYPE, inhabited separately by T4',
 'T4':'initial well-formedness and twelve actual checked native edges',
 'T5':'two authentic native words',
 'T6':'actual production AvailabilityTrace data for both words',
 'T7':'generic production-to-research constructor bridge preserving native data/index',
 'T8':'executable two-distance/total/target observation',
 'T9':'actual (3,0,3,8)->(2,1,3,7) data agreement',
 'T10':'four concrete ForcedRootPhase inhabitants, not a general producer',
 'T11':'authentic raw insertion ordinal theorem, not assembled uniqueness',
 'T13':'FrontNormal and NeverRetired for both words',
 'T14':'actual classified native square, not AdmittedDistanceMove',
 'T15':'exact native prefix and two suffix reifications',
 'T16':'genuine native remaining-root suffix frames',
 'T17':'complete old catalog phases and earlier-root exclusion via All data',
 'T18':'global-frame instance rejected CONDITIONALLY on UniqueRawNameInsertions only'
}
closed=dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').decode().strip(),retainedModules=len(new),retainedDeclarations=17,statusByUnit=status,failedFullyReverted=['T12'],unattemptedT2Units=list(range(19,27)),currentSources={str(p.relative_to(ROOT)):sha(p) for p in new},allSourceCommitCount=len(source_receipts),inheritedCounts=state['counts'])
(OUT/'source-closed.json').write_text(json.dumps(closed,indent=2)+'\n')
plan=dict(timestampUTC=closed['timestampUTC'],sourceBoundary=closed,targets=ordered,invalidationAudit=invalid,inheritedClosurePolicy='200 inherited targets already received import-ordered fresh checks where unblocked/completable; current hashes and no later changed-dependency commits are audited. Unfinished long/external targets remain explicit, not PASSED. All 12 new modules are rechecked here.',inheritedCounts=state['counts'])
(ROOT/(P+'FINAL-VALIDATION-PLAN.json')).write_text(json.dumps(plan,indent=2)+'\n')
(OUT/'FINAL-INVALIDATION-AUDIT.json').write_text(json.dumps(dict(invalidations=invalid,checkedInherited=len([r for r in state['modules'] if r['status'] in ['PASSED','REPAIRED']]),newTargets=len(new)),indent=2)+'\n')
(OUT/'DIFF-STAT-FROM-PRODUCTION.txt').write_bytes(git('diff','--stat','452420c73c59a6af2d204cafa6e722b3a0fff995','HEAD'))
(OUT/'FINAL-PROTECTED-SCOPE.txt').write_bytes(git('diff','bfe2e8d506f2ca77f2e96086f61ed19cc2bde642','HEAD','--','src/','NOTES.md','README.md','THM73-PLAN.md','research/DGamma/CP5O19*','research/DGamma/CP5O20*','research/DGamma/CP5ConfluenceLocalDiamondSpike.idr','research/DGamma/CP5ConfluenceCanonicalSortSpike.idr','research/DGamma/CP5ConfluenceCrossTraceSpike.idr','research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr','research/DGamma/CP5ConfluenceDeletionChainSpike.idr'))
assert (OUT/'FINAL-PROTECTED-SCOPE.txt').read_bytes()==b''
print(json.dumps(dict(newTargets=len(new),extraInvalidations=len(invalid),inheritedCounts=state['counts'],head=closed['head']),indent=2))
