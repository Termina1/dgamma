#!/usr/bin/env python3
"""E3 compiler-free evidence publisher. Does not claim mathematical review.
Requires the completed committed final plan; archives immutable raw snapshots,
then derives origins/ledgers from actual git commit blobs and guard receipts.
Archive boundary excludes its own later artifact-commit receipt (no self-cycle).
"""
from pathlib import Path
import datetime, gzip, hashlib, io, json, re, subprocess, tarfile
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
RAW=Path('/tmp/dgamma-l2r10')
P='research-tests/O6-L2R10-'
assert Path.cwd()==ROOT

def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def declarations(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
def write(suffix,value):(ROOT/(P+suffix)).write_text(json.dumps(value,indent=2)+'\n')
final=json.loads((RAW/'final-validation-result.json').read_text());assert final['passed'] and len(final['validations'])==12
assert not git('diff','--cached','--name-only').strip()
records=[json.loads(line) for line in (RAW/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(line) for line in (RAW/'commit-receipts.jsonl').read_text().splitlines()]
byid={r['unit']:r for r in records}
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==42
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
write('RAW-EVIDENCE-MANIFEST.json',dict(archive=str(archive.relative_to(ROOT)),archiveSHA256=sha(archive.read_bytes()),boundaryHead=boundary,boundaryUTC=now,receiptScope='Includes all source, comment, overlay and pre-validation final-plan commit receipts. Excludes this archive publication later artifact commit receipt; avoids self-reference.',files={name:dict(sha256=sha(data),bytes=len(data)) for name,data in raw.items()}))
origins=[]
types={'GeneralAdmittedMoveExistenceUnique':'TYPE ONLY; no inhabitant','RetirementAdvanceEquation':'checked type, inhabited by retirementAdvanceNative','SplitNativeEdge':'checked type, only actual root edge instantiated','SelectedSquareCut':'checked observation type, produced by observeSelectedMoveCut; NOT a move'}
for receipt in source_receipts:
 r=byid[receipt['invocation']];commit=receipt['resultingCommitHash'];path=r['path'];data=git('show',commit+':'+path)
 old=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True)
 names=declarations(data)-declarations(old.stdout if old.returncode==0 else b'');assert len(names)==1
 name=names.pop();current=(ROOT/path).read_text();match=re.search(r'^(?:[01] )?'+re.escape(name)+r'\s*:|^(?:record|data)\s+'+re.escape(name)+r'\b',current,re.M);assert match
 line=current[:match.start()].count('\n')+1
 kind='type' if name in types else ('proof' if re.search(r'^0 '+re.escape(name)+r'\s*:',current,re.M) else 'executable')
 status=types.get(name,'proved at exact documented scope' if kind=='proof' else 'checked total executable definition')
 origins.append(dict(unit=receipt['unit'],name=name,path=path,line=line,kind=kind,status=status,invocation=receipt['invocation'],commit=commit,checkedSourceSHA256=r['sourceSHA256'],currentSourceSHA256=sha((ROOT/path).read_bytes())))
assert len(origins)==42
write('MICRO-UNIT-LEDGER.json',dict(sourceBoundary=json.loads(raw['source-closed.json']),sourceUnits=origins,stopped=[dict(unit='C3',attempts=['C3-1','C3-2','C3-3'],status='STOP3/3 RESOURCE, exact revert; no semantic failure claimed')],unattempted=['C4','C5','C6','C7','C8','C9','C10'],documentationUnits=[dict(unit='E1',status='exact authorized comment repair, V4 PASS'),dict(unit='E2',status='lane-owned partial draft overlay'),dict(unit='E3',status='plan V5–V16 PASS, origins/ledgers/archive/independent mechanical verification')]))
commit_by_id={r['invocation']:r['resultingCommitHash'] for r in source_receipts}
summary=[]
for r in records:
 row={k:r[k] for k in ['unit','path','start','end','seconds','exit','passed','fresh','interrupted','sourceMutationObserved','sourceSHA256','maxSampleRSSKiB','buildingCount','buildingLines','expectedDiagnostic']}
 row.update(declaredHeavy=r.get('declaredHeavy',False),guardedSourceCommit=commit_by_id.get(r['unit']),rawRecord='raw/'+r['unit']+'.json')
 if r.get('declaredHeavy'):row.update(concurrentHeavyOverlapFirst=r['concurrentHeavyOverlapTimestamps'][0],concurrentHeavyOverlapLast=r['concurrentHeavyOverlapTimestamps'][-1],concurrentHeavyOverlapSamples=len(r['concurrentHeavyOverlapTimestamps']))
 summary.append(row)
write('COMPILER-LEDGER.json',dict(boundaryHead=boundary,sourceDeclarations=42,invocations=summary,archive=str(archive.relative_to(ROOT)),archiveSHA256=sha(archive.read_bytes()),guardedReceipts=receipts))
lines=['# L2R10 declaration origins and exact scope','','Source boundary **637c0ca1**; **42 checked declarations in11 modules**.','This is Thm73/O20 connector research, not Theorem73 or a normalizer proof.','12 executable definitions,26 erased proofs,4 type/record definitions; the','unique move-existence TYPE is uninhabited. Each row adds ONE declaration.','','| Unit | File:line / name | Kind and status | Fresh invocation | Guarded commit |','|---|---|---|---|---|']
for r in origins:lines.append('| '+r['unit']+' | `'+Path(r['path']).name+':'+str(r['line'])+'` / `'+r['name']+'` | '+r['kind']+': '+r['status']+' | '+r['invocation']+' | `'+r['commit'][:8]+'` |')
lines+=['','## Source and formulation origins','','- A1/A2: NEW monomorphic ω dictionary/data equations over inherited public','  native trails; not frozen L2R9 OrdinalFixtures. A3–A7: NEW single-key native','  Dec/Bool observations, not the exhausted whole-list statement.','- A8–A14: NEW actual actor-core event word and conservative phase checker;','  inherited catalog/anchor data are observed, not replaced by supplied phases.','- B1/B2: original ForeignBeginPlanView ownerShape adapter plus retirement','  snapshot. B3–B15: explicit native Advance decisions/outcomes, with native','  resolveCommittedValuesRetireRegistry transport. B16 inhabits the original','  retained three-role contract, not narrowed ForeignReplay.single.','- C1/C2: NEW single-equation abstract-state type and actual root4→8. C3','  checkedFromRaw + C2 target validity hit18GiB twice and48GiB on exact third','  bytes. C3 fully reverted; C4–C10 unattempted. No frozen old statement retry.','- D1/D2: owner R173 uniqueness restored; actual located-birth count proof.','  D3–D8: NEW source-aware selected-cut observation, not admitted moves.','  D7 generic observed indices use actual distance/catalog equations.','  D9/D10: observations FROM the new producer on old genuine prefix fixtures,','  never projected old admitted-move fields.','- Recipe scripts follow the predecessor one-declaration-generation pattern','  but are lane-owned, compiler-free and reproduce only their stated helpers.','','## Failed attempts (none retained as unchecked proof)','','- A13-1/A13-2: index\' API/type mismatch (Nat/List, then Nat/Fin); corrected','  to head\'(drop ordinal events), PASS3/3. A failed commit request was rejected','  before staging; guard behavior and fresh-pass requirement are test-covered.','- C3-1/C3-2:18GiB stops. C3-3: authorized exact48GiB cost stop, STOP3/3.','  Earlier lock polling was stopped before compiler launch and consumed no','  attempt; actual C3-3 had no lock/window operation.','- D7-1: coverage failed on calculated search indices; direct imports checked,','  then explicit observed generic distance/items with own equations PASS2/3.','','## Review limits and evidence','','Read CP3-DIFF-DRAFT-OVERLAY for exact Tier-2 residues. The independently','authorized predecessor D4 COMMENT repair is not a proof/body/quantity change.','All other predecessor sources/draft and all src/root documents are unchanged.','The archive contains raw source snapshots, diagnostics, command/RSS records,','guard receipts, lock-policy chronology and final validations. The compiler-free','independent verifier reconstructs these facts without importing runner logic;','its focused tests are not human mathematical review. Parent owns that gate.','']
(ROOT/(P+'DECLARATION-ORIGINS.md')).write_text('\n'.join(lines))
print(json.dumps(dict(published=True,boundaryHead=boundary,records=len(records),origins=len(origins),archiveFiles=len(raw),archiveSHA256=sha(archive.read_bytes())),indent=2))
