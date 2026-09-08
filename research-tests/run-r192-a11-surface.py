#!/usr/bin/env python3
"""Apply/commit only the exact owner-approved A11 record/consumer declaration.
Usage: python3 -I research-tests/run-r192-a11-surface.py apply|commit UNIT [MESSAGE]
Every step is one existing declaration, not an exception for broad edits.
"""
import datetime, hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r192')
manifest_path = ROOT/'research-tests/O6-R192-A11-SURFACE-MANIFEST.json'
manifest_bytes = manifest_path.read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest() == (OUT/'a11-surface-manifest.sha256').read_text().strip()
manifest = json.loads(manifest_bytes)
action, unit = sys.argv[1:3]
items = [x for x in manifest['items'] if x['unit'] == unit]
assert len(items) == 1
item = items[0]
target = ROOT/item['path']
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git',*args],cwd=ROOT)
assert datetime.datetime.now(datetime.timezone.utc) < datetime.datetime(2026,9,8,21,46,48,tzinfo=datetime.timezone.utc)
assert git('branch','--show-current').decode().strip() == 'cp5-thm73-scoping'
assert not git('diff','--cached','--name-only').strip()
assert not git('diff','34b21c9','--','src/','dgamma.ipkg').strip()
assert git('hash-object','src/DGamma/CP3.idr').decode().strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True))
assert git('show','HEAD:research-tests/O6-R192-A11-SURFACE-MANIFEST.json') == manifest_bytes
old = git('show','HEAD:'+item['path'])
assert sha(old) == item['oldSourceSHA256'], 'HEAD target is not approved old bytes'
new = old.decode()
for replacement in item['replacements']:
    assert new.count(replacement['oldText']) == 1
    new = new.replace(replacement['oldText'],replacement['newText'])
new = new.encode()
assert sha(new) == item['newSourceSHA256']
if action == 'apply':
    assert target.read_bytes() == old
    assert not git('diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg').strip()
    target.write_bytes(new)
    print('APPLIED EXACT A11 DECLARATION',unit,item['path'],sha(new))
elif action == 'commit':
    record = json.loads((OUT/(unit+'.json')).read_text())
    assert record['unit'] == unit and record['path'] == item['path']
    assert record['passed'] and record['fresh'] and not record['interrupted']
    assert record['expectedDiagnostic'] == item['expectedDiagnostic']
    if item['expectedDiagnostic'] is None:
        assert record['exit'] == 0
    else:
        assert record['exit'] != 0 and item['expectedDiagnostic'] in record['transcript'] and item['symbol'] in record['transcript']
        assert record['symbol'] == item['symbol']
    assert target.read_bytes() == new and record['sourceSHA256'] == sha(new)
    assert json.loads((OUT/'ledger.jsonl').read_text().splitlines()[-1])['unit'] == unit
    assert git('diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg').decode().splitlines() == [item['path']]
    subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
    subprocess.run(['git','add','--',item['path']],cwd=ROOT,check=True)
    subprocess.run(['git','commit','-m',sys.argv[3]],cwd=ROOT,check=True)
    assert not git('diff','--cached','--name-only').strip()
    receipt = dict(event='GUARDED A11 SURFACE COMMIT',unit=unit.rsplit('-',1)[0],attempt=unit.rsplit('-',1)[1],invocation=unit,
        path=item['path'],sourceHash=sha(new),oldSourceHash=sha(old),oneExistingDeclaration=item['symbol'],
        resultingCommitHash=git('rev-parse','HEAD').decode().strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        oldFieldSHA256=manifest['oldFieldSHA256'],newFieldSHA256=manifest['newFieldSHA256'],oldRecordSHA256=manifest['oldRecordSHA256'],newRecordSHA256=manifest['newRecordSHA256'],
        guardChecksPassed=['owner-approved exact manifest','one existing declaration','exact HEAD old bytes','exact fresh new bytes','fresh expected PASS','own Building line','no intervening compiler','negative symbol+diagnostic if applicable','production+CP3 frozen','no pre-staged files','no compiler','git diff --check','git commit success','no post-staged files'])
    with (OUT/'commit-receipts.jsonl').open('a') as stream: stream.write(json.dumps(receipt)+'\n')
    print('GUARDED A11 SURFACE COMMIT',json.dumps(receipt))
else:
    raise SystemExit('expected apply or commit')
