#!/usr/bin/env python3
"""E3 compiler-free evidence publisher. Does not claim mathematical review.
Requires the completed committed final plan; archives immutable raw snapshots,
then derives origins/ledgers from actual git commit blobs and guard receipts.
Archive boundary excludes its own later artifact-commit receipt (no self-cycle).
"""
from pathlib import Path
import datetime, gzip, hashlib, io, json, re, subprocess, tarfile
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
RAW=Path('/tmp/dgamma-l2r12')
P='research-tests/O6-L2R12-'
assert Path.cwd()==ROOT

def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def declarations(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
def write(suffix,value):(ROOT/(P+suffix)).write_text(json.dumps(value,indent=2)+'\n')
closed=json.loads((RAW/'source-closed.json').read_text())
final=json.loads((RAW/'final-validation-result.json').read_text());assert final['passed']
assert len(final['validations'])==closed['retainedModules']
assert not git('diff','--cached','--name-only').strip()
records=[json.loads(line) for line in (RAW/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(line) for line in (RAW/'commit-receipts.jsonl').read_text().splitlines()]
byid={r['unit']:r for r in records}
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==closed['retainedDeclarations']
boundary=git('rev-parse','HEAD').decode().strip()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
raw={p.name:p.read_bytes() for p in sorted(RAW.iterdir()) if p.is_file()}
archive=ROOT/(P+'RAW-EVIDENCE.tar.gz')
with archive.open('wb') as out:
 with gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w') as tf:
   for name,data in raw.items():
    info=tarfile.TarInfo('raw/'+name);info.size=len(data);info.mode=0o644;info.mtime=0
    tf.addfile(info,io.BytesIO(data))
write('RAW-EVIDENCE-MANIFEST.json',dict(archive=str(archive.relative_to(ROOT)),archiveSHA256=sha(archive.read_bytes()),boundaryHead=boundary,boundaryUTC=now,receiptScope='Includes all source, stop-audit, overlay and pre-validation final-plan commit receipts; no predecessor repair exists. Excludes this archive publication later artifact commit receipt; avoids self-reference.',files={name:dict(sha256=sha(data),bytes=len(data)) for name,data in raw.items()}))
origins=[]
for receipt in source_receipts:
 r=byid[receipt['invocation']];commit=receipt['resultingCommitHash'];path=r['path'];data=git('show',commit+':'+path)
 old=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True)
 names=declarations(data)-declarations(old.stdout if old.returncode==0 else b'');assert len(names)==1
 name=names.pop();current=(ROOT/path).read_text();match=re.search(r'^(?:[01] )?'+re.escape(name)+r'\s*:|^(?:record|data)\s+'+re.escape(name)+r'\b',current,re.M);assert match
 line=current[:match.start()].count('\n')+1
 kind='type' if re.search(r'^(?:record|data)\s+'+re.escape(name)+r'\b',current,re.M) else ('proof' if re.search(r'^0 '+re.escape(name)+r'\s*:',current,re.M) else 'executable')
 status='checked type; inhabitance at exact declared scope' if kind=='type' else ('proved at exact documented scope' if kind=='proof' else 'checked total executable definition')
 origins.append(dict(unit=receipt['unit'],name=name,path=path,line=line,kind=kind,status=status,invocation=receipt['invocation'],commit=commit,checkedSourceSHA256=r['sourceSHA256'],currentSourceSHA256=sha((ROOT/path).read_bytes())))
groups={}
for r in records:
 if not r['unit'].startswith('V'):groups.setdefault(r['unit'].rsplit('-',1)[0],[]).append(r)
stopped=[dict(unit=unit,attempts=[r['unit'] for r in rows],status='STOP3/3; fully reverted; no semantic falsity inferred') for unit,rows in groups.items() if len(rows)==3 and not any(r['passed'] for r in rows)]
write('MICRO-UNIT-LEDGER.json',dict(sourceBoundary=closed,sourceUnits=origins,stopped=stopped,documentationUnits=[dict(unit='E1',status='lane-owned exact partial draft overlay'),dict(unit='E2',status='guard metadata repair, final validation plan and evidence tools'),dict(unit='E3',status='final validations, origins/ledgers/archive/independent mechanical verification')]))
commit_by_id={r['invocation']:r['resultingCommitHash'] for r in source_receipts}
summary=[];overlaps=[]
for r in records:
 row={k:r[k] for k in ['unit','path','start','end','seconds','exit','passed','fresh','interrupted','sourceMutationObserved','sourceSHA256','maxSampleRSSKiB','buildingCount','buildingLines','expectedDiagnostic']}
 row.update(declaredHeavy=False,guardedSourceCommit=commit_by_id.get(r['unit']),rawRecord='raw/'+r['unit']+'.json');summary.append(row)
 for item in r['separateCompilerObservations']:
  overlaps.append(dict(invocation=r['unit'],firstObservedUTC=item.get('firstObservedUTC',r['start']),lastObservedUTC=item.get('lastObservedUTC',r['start'])))
write('COMPILER-LEDGER.json',dict(boundaryHead=boundary,sourceDeclarations=len(origins),invocations=summary,archive=str(archive.relative_to(ROOT)),archiveSHA256=sha(archive.read_bytes()),guardedReceipts=receipts))
write('OVERLAP-LOG.json',dict(timestampObservations=overlaps,foreignCompilersNeverSignalled=True,format='timestamp-only summary; earlier immutable raw records preserve copied-runner process metadata as disclosed in audit'))
counts={kind:sum(r['kind']==kind for r in origins) for kind in ['proof','executable','type']}
lines=['# L2R12 declaration origins and exact scope','',f"Source boundary **{closed['head'][:8]}**; **{len(origins)} checked declarations in {closed['retainedModules']} modules**.",str(counts),'This is bounded PARTIAL connector research, not Theorem73 or a normalizer.','See GRIND-SHIFT-AUDIT and CP3-DIFF-DRAFT-OVERLAY for exact premises/residues.','Each row adds ONE declaration; no predecessor bodies/comments were changed.','','| Unit | File:line / name | Kind/status | Fresh invocation | Guarded commit |','|---|---|---|---|---|']
for r in origins:lines.append('| '+r['unit']+' | `'+Path(r['path']).name+':'+str(r['line'])+'` / `'+r['name']+'` | '+r['kind']+': '+r['status']+' | '+r['invocation']+' | `'+r['commit'][:8]+'` |')
lines+=['','## Origins and boundary','','- A1–A6: new all-key/head/offset agreement; A7 bounded-filter formulation STOP3/3. A8–A14: native phase event decoders; not produceForcedRootPhases.','- B1–B10: executable actual-word set, observations, and NEW kind-restricted structural replay. B11–B15: original-edge role dispatcher and native actor/frame/snapshot transport. B16: ACTUAL R191 inventory, not whole relocated replay.','- C1–C6: exact source/action located occurrence decoder. C7–C13: generic genuine Retire/root local square and classifier/request branch. C14 local fixture STOP3/3 and fully reverted; no concrete application success claimed.','- D: state-family parameter stays abstract in generic core assembly. Original/restored B packets supply native equations; no split8->9 edge normalized or asserted. See audit for final D8 status.','','All retained sources are total and free of new holes/postulates/unsafe escapes. Source snapshots, bounded failed attempts, guard receipts and plan-first final validations are archived. Mechanical verification is NOT independent human mathematical review; the parent owns that review gate.','']
(ROOT/(P+'DECLARATION-ORIGINS.md')).write_text('\n'.join(lines))
print(json.dumps(dict(archiveSHA256=sha(archive.read_bytes()),archiveFiles=len(raw),retained=len(origins),kinds=counts,records=len(records),passed=sum(r['passed'] for r in records),failed=[r['unit'] for r in records if not r['passed']],overlapObservations=len(overlaps)),indent=2))
