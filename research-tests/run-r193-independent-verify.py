#!/usr/bin/env python3
"""Read-only independent receipt/source/validation audit; no compiler/cache edits."""
import datetime,hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r193')
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(b):return hashlib.sha256(b).hexdigest()
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
byunit={r['unit']:r for r in records};assert len(byunit)==len(records)
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
bycommit={r['resultingCommitHash']:r for r in receipts};assert len(bycommit)==len(receipts)
for r in records:
 assert json.loads((OUT/(r['unit']+'.json')).read_text())==r
 assert (OUT/(r['unit']+'.log')).read_text()==r['transcript']
 assert sha((OUT/(r['unit']+'.source')).read_bytes())==r['sourceSHA256']
 if r['passed']:
  assert r['fresh'] and not r['interrupted']
  if r['expectedDiagnostic']:
   assert r['exit']!=0 and r['expectedDiagnostic'] in r['transcript']
   assert r.get('symbol') and r['symbol'] in r['transcript']
  else:assert r['exit']==0 and 'Error:' not in r['transcript']
for first,second in zip(records,records[1:]):assert first['end']<=second['start']
sourcecommits=git('log','--format=%H','a83706a7..HEAD','--','research/','research-tests/DGamma/').decode().splitlines()
assert len(sourcecommits)==52
for commit in sourcecommits:
 receipt=bycommit[commit];r=byunit[receipt['invocation']]
 assert receipt['event'] in ['GUARDED COMMIT','GUARDED A11 SURFACE COMMIT','GUARDED COMMENT-ONLY COMMIT']
 assert r['passed'] and r['sourceSHA256']==receipt['sourceHash']
 changed=git('diff-tree','--no-commit-id','--name-only','-r',commit,'--','research/','research-tests/DGamma/').decode().splitlines()
 assert changed==[r['path']]
 assert sha(git('show',commit+':'+r['path']))==r['sourceSHA256']
 assert r['end']<=receipt['timestampUTC']
 assert not any(r['end']<other['start']<receipt['timestampUTC'] for other in records)
assert (OUT/'final-validation-plan.json').read_bytes()==(ROOT/'research-tests/O6-R193-FINAL-VALIDATION-PLAN.json').read_bytes()
assert (OUT/'final-source-recheck-plan.json').read_bytes()==(ROOT/'research-tests/O6-R193-FINAL-SOURCE-RECHECK-PLAN.json').read_bytes()
plans=json.loads((OUT/'final-validation-plan.json').read_text())+json.loads((OUT/'final-source-recheck-plan.json').read_text())
qualifications=json.loads((OUT/'validation-qualifications.json').read_text())
assert set(qualifications)=={'V16'} and qualifications['V16']['superseded']
for item in plans:
 r=byunit[item['unit']]
 assert r['passed'] and r['fresh'] and r['sourceSHA256']==item['sourceHash']
 assert r['expectedDiagnostic']==item['expectedDiagnostic'] and r.get('symbol')==item.get('symbol')
 if item['unit']=='V16':
  assert qualifications['V16']['oldSourceHash']==r['sourceSHA256']
  assert byunit['V38']['path']==r['path'] and byunit['V38']['sourceSHA256']==qualifications['V16']['newSourceHash']
 else:assert sha((ROOT/('dgamma.ipkg' if r['path']=='package' else r['path'])).read_bytes())==r['sourceSHA256']
assert byunit['Y1COMMENT']['passed'] and byunit['Y1COMMENT']['sourceSHA256']==byunit['V38']['sourceSHA256']
for key in ['A9','B10','C4']:
 assert [r['unit'] for r in records if re.fullmatch(key+r'-\d+',r['unit'])]==[key+'-1',key+'-2',key+'-3']
 assert all(not byunit[key+'-'+str(n)]['passed'] for n in range(1,4))
qual=json.loads((OUT/'invocation-qualifications.json').read_text())
assert byunit['A10-1']['sourceSHA256']==byunit['A11-1']['sourceSHA256']
assert qual['A11-1']['effectiveUnit']=='A10' and qual['A11-1']['effectiveAttempt']==2
paths=git('diff','--name-only','a83706a7','--','research/','research-tests/DGamma/').decode().splitlines()
newdecls={}
def declarations(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
for path in paths:
 if not path.endswith('.idr'):continue
 old=subprocess.run(['git','show','a83706a7:'+path],cwd=ROOT,capture_output=True).stdout
 added=sorted(declarations((ROOT/path).read_bytes())-declarations(old));newdecls[path]=added
assert sum(map(len,newdecls.values()))==48
assert not git('diff','34b21c9','--','src/','dgamma.ipkg')
assert not git('diff','--cached','--name-only') and not git('diff','--name-only')
assert git('hash-object','src/DGamma/CP3.idr').decode().strip()=='2c697e532e83989de8591fa6a4378747c6a501c0'
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True))
report=dict(status='PASS',head=git('rev-parse','HEAD').decode().strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 invocationCount=len(records),passedCount=sum(r['passed'] for r in records),failedCount=sum(not r['passed'] for r in records),expectedNegativeCount=sum(r['passed'] and bool(r['expectedDiagnostic']) for r in records),
 finalCheckCount=len(plans),supersededHistoricalFinalChecks=['V16'],allFinalCurrentSourcesAuthenticated=True,
 newDeclarationCount=48,newDeclarations=newdecls,sourceCommitCount=len(sourcecommits),allSourceCommitsReceiptAuthenticated=True,
 allInvocationsSerialized=True,allLogsAndSnapshotsAuthenticated=True,maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records),
 allSourceAttemptsBeforeCutoff=all(r['start']<'2026-09-08T21:46:48' for r in records if re.fullmatch(r'[A-FX]\d+-\d+',r['unit'])),
 productionFrozen=True,noUnsafeNewProofs='separate frozen audit enforces prohibition census',noCompiler=True,noStagedFiles=True,cleanTrackedTree=True)
assert report['allSourceAttemptsBeforeCutoff']
(OUT/'independent-verification.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='newDeclarations'},indent=2))
