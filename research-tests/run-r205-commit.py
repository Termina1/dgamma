#!/usr/bin/env python3
"""Guarded commits: PRESTATE, exact owner-signed PRODUCTION, ARTIFACT, LEXICAL.
PRODUCTION is intentionally committed before checking to keep the authorized patch recoverable.
Usage: python3 -I research-tests/run-r205-commit.py KIND MESSAGE PATH...
"""
import sys, pathlib, subprocess, json, re
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
kind,message,*paths=sys.argv[1:]
assert kind in ['PRESTATE','PRODUCTION','ARTIFACT','LEXICAL'] and paths
assert git('branch','--show-current').strip()=='cp5-thm73-scoping'
assert not git('diff','--cached','--name-only').strip()
own,foreign,unknown=compiler_scopes()
assert not own and not unknown, 'Own/unknown compiler active'
if foreign: print('Foreign-lane overlap timestamp',utc(),flush=True)
# Signed unified-diff context lines are exactly one space, not source whitespace.
# Authenticate byte-exact copies instead of altering the signed patch/overlay.
copy_paths=['research-tests/O6-R205-CP3-TIER1-SIGNED-DIFF.patch','research-tests/O6-R205-CP3-TIER1-OVERLAY-COPY.md']
inputs=json.loads((ROOT/'research-tests/O6-R205-INPUTS.json').read_text())
for item in inputs['items'].values():
    if item['copiedTo'] in copy_paths: assert sha((ROOT/item['copiedTo']).read_bytes())==item['sha256']
whitespace_paths=['.']+[':(exclude)'+p for p in copy_paths]
subprocess.run(['git','diff','--check','--',*whitespace_paths],cwd=ROOT,check=True)
assert_frozen()
parent=git('rev-parse','HEAD').strip()
if kind=='PRESTATE':
    assert parent==START
    assert not git('diff',START,'--','src/','research/','research-tests/DGamma/','dgamma.ipkg')
if kind=='PRODUCTION':
    assert paths==['src/DGamma/CP3.idr']
    receipts=OUT/'commit-receipts.jsonl'
    assert not receipts.exists() or not any(json.loads(s)['kind']=='PRODUCTION' for s in receipts.read_text().splitlines())
    patch=ROOT/'research-tests/O6-R205-CP3-TIER1-SIGNED-DIFF.patch'
    assert sha(patch.read_bytes())==PATCH_SHA
    assert git('diff','--name-only','--','src/','dgamma.ipkg').splitlines()==paths
    # Reverse-check and compare the complete resulting bytes to the signed patch candidate.
    subprocess.run(['git','apply','--reverse','--check',str(patch)],cwd=ROOT,check=True)
    expected=json.loads((ROOT/'research-tests/O6-R205-LANE-INVENTORY-COPY.json').read_text())['candidateSHA256']
    assert sha((ROOT/paths[0]).read_bytes())==expected
    assert OWNER in message
elif kind in ['ARTIFACT','PRESTATE']:
    assert all((p.startswith('research-tests/') and not p.endswith('.idr')) or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in paths)
    assert not git('diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg').strip()
elif kind=='LEXICAL':
    assert all(p.startswith(('research/','research-tests/')) and p.endswith('.idr') and p not in PROTECTED_PATHS for p in paths)
    for p in paths:
        repair=json.loads((OUT/('repair-'+pathlib.Path(p).stem+'.json')).read_text())
        assert repair['path']==p and repair['beforeSHA256']==sha(subprocess.check_output(['git','show','HEAD:'+p],cwd=ROOT))
        assert repair['afterSHA256']==sha((ROOT/p).read_bytes())
        record=json.loads((OUT/(repair['passingInvocation']+'.json')).read_text())
        assert record['passed'] and record['path']==p and record['sourceSHA256']==repair['afterSHA256']
        added='\n'.join(x[1:] for x in git('diff','--',p).splitlines() if x.startswith('+') and not x.startswith('+++') and not x[1:].lstrip().startswith(('--','|||')))
        assert not re.search(r'\b(?:with|let|believe_me|assert_total|assert_smaller|partial|postulate|deletionTheoremProof)\b|\?\w+',added)
hashes={}
for path in paths:
    before=subprocess.run(['git','show','HEAD:'+path],cwd=ROOT,capture_output=True)
    hashes[path]=dict(before=sha(before.stdout) if before.returncode==0 else None,after=sha((ROOT/path).read_bytes()))
subprocess.run(['git','add','--',*paths],cwd=ROOT,check=True)
assert set(git('diff','--cached','--name-only').splitlines())==set(paths)
try:
    subprocess.run(['git','diff','--cached','--check','--',*whitespace_paths],cwd=ROOT,check=True)
    subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
except BaseException:
    subprocess.run(['git','restore','--staged','--',*paths],cwd=ROOT,check=True)
    raise
assert not git('diff','--cached','--name-only').strip()
receipt=dict(kind=kind,message=message,ownerDecisionVerbatim=OWNER if kind=='PRODUCTION' else None,beforeCommit=parent,afterCommit=git('rev-parse','HEAD').strip(),timestampUTC=utc(),hashes=hashes,guardSHA256=sha(pathlib.Path(__file__).read_bytes()),noStagedFiles=True,frozenUnchanged=True,whitespaceGuard=True)
OUT.mkdir(exist_ok=True)
with (OUT/'commit-receipts.jsonl').open('a') as f: f.write(json.dumps(receipt,ensure_ascii=False)+'\n')
print(json.dumps(receipt,ensure_ascii=False,indent=2))
