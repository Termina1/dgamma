#!/usr/bin/env python3
"""Guarded exact-source commits; immutable receipts outside git index.
Usage: UNIT MESSAGE [PATH...] (UNIT=ARTIFACT or RETIRE for non-native changes).
"""
import sys, pathlib, subprocess, json, re
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r206_common import *
unit,message,*paths=sys.argv[1:]
assert git('branch','--show-current').strip()=='cp5-thm73-scoping'
assert not git('diff','--cached','--name-only').strip()
assert_frozen()
own,foreign,unknown=compiler_scopes()
assert not own and not unknown, 'Own/unknown compiler active'
if unit not in ['ARTIFACT','RETIRE']:
    record=json.loads((OUT/(unit+'.json')).read_text())
    assert record['passed'] and record['fresh'] and record['exit']==0
    assert records()[-1]['unit']==unit, 'No intervening compiler invocation'
    assert not record['targetMutationDetected'] and not record['unexpectedBuilding']
    assert not paths
    paths=[record['path']]
    assert sha((ROOT/paths[0]).read_bytes())==record['sourceSHA256']
else:
    assert paths
    if unit=='ARTIFACT':
        assert all((p.startswith('research-tests/') and not p.endswith('.idr')) or p in ['README.md','NOTES.md','THM73-PLAN.md'] for p in paths)
    else:
        assert paths==['research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr','research-tests/DGamma/retired/R172O17OpenParentRootReuseCandidate.idr']
        assert not (ROOT/paths[0]).exists()
        assert (ROOT/paths[1]).read_bytes()==subprocess.check_output(['git','show',START+':'+paths[0]],cwd=ROOT)
assert not any(p.startswith('src/') or p=='dgamma.ipkg' or p in PROTECTED_PATHS for p in paths)
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
hashes={}
for p in paths:
    old=subprocess.run(['git','show','HEAD:'+p],cwd=ROOT,capture_output=True)
    hashes[p]=dict(before=sha(old.stdout) if old.returncode==0 else None,after=sha((ROOT/p).read_bytes()) if (ROOT/p).exists() else None)
    if p.endswith('.idr') and unit!='RETIRE':
        diff=git('diff','--',p)
        added='\n'.join(s[1:] for s in diff.splitlines() if s.startswith('+') and not s.startswith('+++') and not s[1:].lstrip().startswith(('--','|||')))
        assert not re.search(r'\b(?:with|let|believe_me|assert_total|assert_smaller|partial|postulate|deletionTheoremProof)\b|\?\w+',added), 'Forbidden added syntax'
parent=git('rev-parse','HEAD').strip()
try:
    subprocess.run(['git','add','--',*paths],cwd=ROOT,check=True)
    assert set(git('diff','--cached','--name-only','--no-renames').splitlines())==set(paths)
    subprocess.run(['git','diff','--cached','--check'],cwd=ROOT,check=True)
    subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
except BaseException:
    subprocess.run(['git','restore','--staged','--',*paths],cwd=ROOT,check=True)
    raise
assert not git('diff','--cached','--name-only').strip()
receipt=dict(unit=unit,message=message,beforeCommit=parent,afterCommit=git('rev-parse','HEAD').strip(),timestampUTC=utc(),hashes=hashes,guardSHA256=sha(pathlib.Path(__file__).read_bytes()),noStagedFiles=True,productionUnchanged=True,frozenUnchanged=True,whitespaceGuard=True,crossLaneOverlapTimestampsUTC=[utc()] if foreign else [])
OUT.mkdir(exist_ok=True)
with (OUT/'commit-receipts.jsonl').open('a') as f: f.write(json.dumps(receipt)+'\n')
print(json.dumps(receipt,indent=2))
