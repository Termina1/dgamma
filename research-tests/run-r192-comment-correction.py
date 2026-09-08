#!/usr/bin/env python3
"""Owner-approved exactly-three-docstring-line correction, not a proof retry."""
import datetime,hashlib,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path('/tmp/dgamma-r192')
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(b):return hashlib.sha256(b).hexdigest()
manifest_bytes=(ROOT/'research-tests/O6-R192-COMMENT-CORRECTION-MANIFEST.json').read_bytes()
assert sha(manifest_bytes)=='26ac9d9dedbb129786a2b66a3bc650635641b7a7789bd524bf996024e0397878'
assert git('show','HEAD:research-tests/O6-R192-COMMENT-CORRECTION-MANIFEST.json')==manifest_bytes
manifest=json.loads(manifest_bytes);path=manifest['path'];target=ROOT/path
assert git('branch','--show-current').decode().strip()=='cp5-thm73-scoping'
assert not git('diff','34b21c9','--','src/','dgamma.ipkg')
assert git('hash-object','src/DGamma/CP3.idr').decode().strip()=='2c697e532e83989de8591fa6a4378747c6a501c0'
assert not git('diff','--cached','--name-only')
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True))
assert datetime.datetime.now(datetime.timezone.utc)<datetime.datetime(2026,9,8,22,1,48,tzinfo=datetime.timezone.utc)
completed=json.loads((OUT/'final-validation-complete.json').read_text())
assert completed['invocations']==['V'+str(n) for n in range(1,38)]
old=git('show','HEAD:'+path)
assert sha(old)==manifest['oldSourceSHA256']
assert old.decode().count(manifest['oldText'])==1
new=old.decode().replace(manifest['oldText'],manifest['newText']).encode()
assert sha(new)==manifest['newSourceSHA256']
assert old.splitlines()[17:20]!=new.splitlines()[17:20]
for body in [old,new]:
 assert sha('\n'.join(l for l in body.decode().splitlines() if not l.startswith('|||')).encode())==manifest['unchangedNonDocstringBytesSHA256']
if sys.argv[1]=='apply':
 assert target.read_bytes()==old
 assert not git('diff','--name-only')
 target.write_bytes(new)
 print('APPLIED EXACT COMMENT-ONLY CORRECTION',path,sha(old),sha(new))
elif sys.argv[1]=='commit':
 record=json.loads((OUT/'Y1COMMENT.json').read_text())
 assert record['path']==path and record['fresh'] and record['passed'] and record['exit']==0 and not record['interrupted']
 assert record['expectedDiagnostic'] is None and record['sourceSHA256']==sha(new) and target.read_bytes()==new
 assert json.loads((OUT/'ledger.jsonl').read_text().splitlines()[-1])['unit']=='Y1COMMENT'
 assert git('diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg').decode().splitlines()==[path]
 subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
 diff=git('diff','--',path).decode()
 changed=[l for l in diff.splitlines() if l[:1] in ['+','-'] and not l.startswith(('+++','---'))]
 assert len(changed)==6 and all(l[1:].startswith('|||') for l in changed)
 (OUT/'comment-only-source.diff').write_text(diff)
 subprocess.run(['git','add','--',path],cwd=ROOT,check=True)
 subprocess.run(['git','commit','-m','R192: correct candidate-state docstring after reverted C4 trace'],cwd=ROOT,check=True)
 assert not git('diff','--cached','--name-only')
 receipt=dict(event='GUARDED COMMENT-ONLY COMMIT',unit='Y1COMMENT',attempt=None,invocation='Y1COMMENT',path=path,
  oldSourceHash=sha(old),sourceHash=sha(new),resultingCommitHash=git('rev-parse','HEAD').decode().strip(),
  timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
  guardChecksPassed=['exact owner-approved three comment lines','all37 original final checks complete','all non-docstring bytes identical','manifest committed and hash authenticated','fresh PASS with own Building line','exact source SHA256','no intervening compiler','production+CP3 frozen','no pre-staged files','no compiler','git diff --check','git commit success','no post-staged files'])
 with (OUT/'commit-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 qualifications=json.loads((OUT/'validation-qualifications.json').read_text()) if (OUT/'validation-qualifications.json').exists() else {}
 assert 'V16' not in qualifications
 qualifications['V16']=dict(validValidation=True,currentSourceValidation=False,superseded=True,
  supersededBy=['Y1COMMENT','V38'],oldSourceHash=sha(old),newSourceHash=sha(new),
  reason='Valid original-source check; exact owner-approved comment-only correction after37 checks. No declaration/type/body byte changed. Keep record, use V38 for final source.')
 (OUT/'validation-qualifications.json').write_text(json.dumps(qualifications,indent=2)+'\n')
 print('GUARDED COMMENT-ONLY COMMIT',json.dumps(receipt))
else:raise SystemExit('expected apply or commit')
