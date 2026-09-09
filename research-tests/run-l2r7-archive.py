#!/usr/bin/env python3
"""Archive exact records/provenance; adapted from run-l2r6-archive.py.
Compiler-free, lane2-only. Handles ratified A8 stop and B2's V1 whitespace
receipt explicitly; never treats a matching source hash as PASS authority.
"""
import datetime, hashlib, json, pathlib, re, subprocess, sys, tarfile
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r7');BASE='87e9fb20'
assert pathlib.Path.cwd()==ROOT
assert len(sys.argv)==2
END=sys.argv[1]
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(data): return hashlib.sha256(data).hexdigest()
def declared(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
assert git('branch','--show-current').decode().strip()=='cp5-thm73-lane-a8a10'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in records})==len(records)
individual={}
for p in OUT.glob('*.json'):
 d=json.loads(p.read_text())
 if isinstance(d,dict) and all(k in d for k in ['unit','path','command','start','end','sourceSHA256']):individual[d['unit']]=d
assert set(individual)=={r['unit'] for r in records}
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
source_receipts={r['invocation']:r for r in receipts if r['event']=='GUARDED COMMIT'}
qualifications=json.loads((OUT/'invocation-qualifications.json').read_text())
for r in records:
 assert individual[r['unit']]==r
 assert sha((OUT/(r['unit']+'.source')).read_bytes())==r['sourceSHA256']
 assert (OUT/(r['unit']+'.log')).read_text()==r['transcript']
 assert not r.get('bundleSources')
 assert r['path'].startswith('research-tests/O6-L2R7-Sources/') or (r['unit']=='V0' and r['path']=='research-tests/O6-L2R6-Sources/DGamma/L2R6ForcedScan.idr')
groups={}
for r in records:
 if re.fullmatch(r'[ABCD]\d+-[1-3]',r['unit']):groups.setdefault(r['unit'].rsplit('-',1)[0],[]).append(r)
caps={'A':22,'B':16,'C':12,'D':8,'E':3}
for letter in 'ABCD':assert {u for u in groups if u.startswith(letter)}=={letter+str(n) for n in range(1,caps[letter]+1)}
origins=[];micro=[]
records_types={'AnyHit','SharedKey','ForcedSeedBasis','ForcedClassificationAt','OrderedForcedRootBundleC','ActorLifecycleOnlyAttachedC','LocatedOpenEpisodeBlockAttachedC','BlockBeforeAttachedC','ControlNativeExecution','ForcedRootControlInBundle','ControlFixture','AttachedBundleOccurrenceC','AttachedNormalFormC','ClassifierCorrespondenceFixtures','AnchorTransport','CatalogBirthAt','PlacedCoverageFixtures'}
for unit,attempts in sorted(groups.items(),key=lambda p:(p[0][0],int(p[0][1:]))):
 assert len(attempts)<=3
 assert [int(r['unit'].rsplit('-',1)[1]) for r in attempts]==list(range(1,len(attempts)+1))
 successes=[r for r in attempts if r['passed']];assert len(successes)<=1
 receipt=source_receipts.get(attempts[-1]['unit']);validation=None
 if unit=='B2':
  receipt=source_receipts['V1'];validation=individual['V1'];assert attempts[-1]['passed'] and validation['passed']
  assert (OUT/'B2-1.source').read_bytes().rstrip()+b'\n'==(OUT/'V1.source').read_bytes()
 if not successes:
  assert unit=='A8' and len(attempts)==3
  stop=json.loads((OUT/'A8-stop.json').read_text());assert stop['retained'] is False and 'FULL REVERT' in stop['status']
  assert (ROOT/attempts[-1]['path']).read_bytes()==git('show','3ad23bd0:'+attempts[-1]['path'])
  names=[];status='EXHAUSTED 3/3; ratified FULL REVERT; no restatement';commit=None
 else:
  assert receipt and attempts[-1]['passed']
  checked=validation or attempts[-1];commit=receipt['resultingCommitHash'];path=checked['path']
  before=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True).stdout
  after=git('show',commit+':'+path);names=sorted(declared(after)-declared(before));assert len(names)==1
  assert sha(after)==checked['sourceSHA256']==receipt['sourceHash'];name=names[0]
  lines=(ROOT/path).read_text().splitlines();line=next(i for i,s in enumerate(lines,1) if re.match(r'^(?:[01] |record |data )?'+re.escape(name)+r'\b',s))
  status='TYPE ONLY; general producer OPEN' if name=='GeneralAttachedNormalForm' else ('checked record/family; producer separate' if name in records_types else 'checked total definition/proof; exact scope in audit')
  origins.append(dict(unit=unit,declaration=name,path=path,line=line,check=checked['unit'],proofAttempt=attempts[-1]['unit'],commit=commit,status=status,sourceSHA256=checked['sourceSHA256']))
 micro.append(dict(unit=unit,status=status,declarations=names,path=attempts[-1]['path'],commit=commit,validation=validation['unit'] if validation else None,attempts=[{k:r[k] for k in ['unit','passed','fresh','exit','sourceSHA256','maxSampleRSSKiB','seconds']} for r in attempts]))
assert len(origins)==len(source_receipts)==57
(OUT/'declaration-origins.json').write_text(json.dumps(origins,indent=2)+'\n')
(ROOT/'research-tests/O6-L2R7-MICRO-UNIT-LEDGER.json').write_text(json.dumps(dict(base=BASE,sourceBoundary='435bd364',archiveBoundary=git('rev-parse',END).decode().strip(),caps=caps,attemptedSlots={k:caps[k] for k in 'ABCD'},retainedDeclarations=len(origins),stoppedUnits=['A8'],records=micro),indent=2)+'\n')
text='# L2R7 declaration origins\n\n57 checked retained declarations in17 modules; A8 fully reverted. Every retained declaration has a fresh guarded receipt. B2 uses proof PASS B2-1 plus exact whitespace-only final validation V1. No predecessor Idris source edit.\n\n| Unit | Declaration | File:line | Fresh PASS | Commit | Status |\n|---|---|---|---|---|---|\n'
for o in origins:text+=f"| {o['unit']} | `{o['declaration']}` | `{pathlib.Path(o['path']).stem}:{o['line']}` | {o['check']} | `{o['commit'][:8]}` | {o['status']} |\n"
text+='''\n## Origins and exact scope\n\n- ObservedAny/Classifier: new structural any-fold/ordered-seed proofs; general soundness/completeness plus executable observation of the UNCHANGED L2R6 classifier. Catalog entries, not raw-name lookup, index the correspondence.\n- ReleaseDecode: ONLY SharedKey record retained. A8 observed-Dec/native-case decoder exhausted3/3 and was reverted; no shared-key/release/phase producer.\n- AttachedC: research COPY/EXTENSION of L2R3 grammar, adding SAME-BUNDLE Retire/Remove with Elem and actual source Root lookup. Wrapper EMPTY history. Original proofs untouched. Sound original→C inclusions; full located/order C records preserve all fields.\n- ControlStates/Execution/Trace/Disposition/Fixture: same-origin barrier prefix followed by Retire3/Remove3 then Begin2/Finish2. Native equations, full blocks and both dispositions are constructed simultaneously. Parent [0,8), following [8,10), literal gap0. Cross-bundle controls OPEN.\n- AttachedCGap: research counterparts of L2R3 membership/NF records; NEW conditional zero-gap proof uses inherited numeric interval lemma with count transport. Coverage/NF/separation remain premises.\n- AnchorTransport/Fixture: new physical ordinal-map CONTRACT with actual source/child/parent/shared-key/max witnesses. Actual R-over-Begin2 native instance only. General transport and other-root distance invariance OPEN.\n- CatalogBirth: NEW general trail-inductive generated-catalog decoder, exact ordinal/count transport and generic occurrence bound. No supplied decoder/coverage callback in its public theorem. Proof-erased constructive result, not a runtime decision procedure.\n- PlacedCoverage/CoverageFixtures: NEW general computed catalog equality→actual global bundle occurrence proof, optional observed anchor membership producer, and fresh R/R/S instantiations on both retained originals. No fixture NF reused.\n- NFObligation: NEW exact scoped TYPE ONLY; general producer/all-premises zero-gap OPEN. No holes/postulates/escape hatches.\n- Runners/archive/verifier/tests: copied/adapted L2R6 tooling with exact lane/cap/bootstrap changes, no companion authority, explicit A8 stop and B2 V1 whitespace receipt, accurate header-repair allowlist. Header-only L2R6 P2 exceptions and draft/manifest are the sole predecessor edits.\n'''
(ROOT/'research-tests/O6-L2R7-DECLARATION-ORIGINS.md').write_text(text)
archive=ROOT/'research-tests/O6-L2R7-COMPILER-EVIDENCE.tar.gz';assert not archive.exists(),'Immutable archive already exists'
with tarfile.open(archive,'w:gz') as tar:
 for p in sorted(OUT.iterdir()):
  if p.is_file():tar.add(p,arcname=OUT.name+'/'+p.name)
with tarfile.open(archive,'r:gz') as tar:
 for r in records:
  for suffix in ['.json','.log','.source']:
   filename=r['unit']+suffix;assert tar.extractfile(OUT.name+'/'+filename).read()==(OUT/filename).read_bytes()
ledger=dict(shift='L2R7',base=BASE,sourceBoundary='435bd364',archiveBoundary=git('rev-parse',END).decode().strip(),generatedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),recordCount=len(records),passedCount=sum(r['passed'] for r in records),failedCount=sum(not r['passed'] for r in records),retainedDeclarations=len(origins),unitCaps=caps,commitReceipts=receipts,invocationQualifications=qualifications,monitorQualifications=json.loads((OUT/'monitor-qualifications.json').read_text()),protocolIncidents=json.loads((OUT/'protocol-incidents.json').read_text()),evidenceArchive=archive.name,evidenceArchiveSHA256=sha(archive.read_bytes()),publicationBoundary='All source receipts and final checks are archived. Archive/report publication receipts cannot be recursively inside their own archive; live append-only receipts authenticate later artifact commits.',records=records)
(ROOT/'research-tests/O6-L2R7-COMPILER-LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps({k:ledger[k] for k in ['recordCount','passedCount','failedCount','retainedDeclarations','evidenceArchiveSHA256']}))
