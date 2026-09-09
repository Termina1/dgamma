#!/usr/bin/env python3
"""Guarded artifact commit after an independently inspected exact-source PASS.
Accept lane-owned L2R13 non-Idris artifacts ONLY. Only exact parent-authorized P2 documentary repairs.
Usage: python3 -I research-tests/run-l2r13-artifact-commit.py UNIT MESSAGE PATH...
"""
import datetime, hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r13')
BASE = 'b9130fbb'
REPAIRS={}
DOCUMENTARY={'research-tests/O6-L2R12-DECLARATION-ORIGINS.md': {'beforeSHA256': '5653b5a9457f158f54b42fd99c4e699de8c1838048654ad05f940343990ae9fd', 'afterSHA256': '8f83f6526fe0f4926a21b123b851ba1295351debe5863e875742e8af3d1ff805', 'old': 'checked type; inhabitance at exact declared scope', 'new': 'checked TYPE declaration; NOT inhabited', 'authority': 'L2R13 parent steering: L2R12 ACCEPT-WITH-NOTES P2 authorized documentary correction; no source change or dedicated compiler'}, 'research-tests/O6-L2R12-MICRO-UNIT-LEDGER.json': {'beforeSHA256': '78645939508cc7e713f0a11181a38e1ad025489fc805795fc9dff353bf70fee7', 'afterSHA256': 'e559820130fa4ca8e62f5358e184dc02c7fbf4b6683f1ce88071d0727e95bfcd', 'old': 'checked type; inhabitance at exact declared scope', 'new': 'checked TYPE declaration; NOT inhabited', 'authority': 'L2R13 parent steering: L2R12 ACCEPT-WITH-NOTES P2 authorized documentary correction; no source change or dedicated compiler'}, 'research-tests/run-l2r12-publish-evidence.py': {'beforeSHA256': 'b91a34b3b7b10e792508dd17a8e66fbf91abfd2db819cdca34f47ed6096e3d79', 'afterSHA256': 'a056ea95d7609deba5a7d9a0ffaa078f2334f04a6a79dd231e6b0f091651b008', 'old': 'checked type; inhabitance at exact declared scope', 'new': 'checked TYPE declaration; NOT inhabited', 'authority': 'L2R13 parent steering: L2R12 ACCEPT-WITH-NOTES P2 authorized documentary correction; no source change or dedicated compiler'}}

def git(*args):
 return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
 return hashlib.sha256(data).hexdigest()
assert pathlib.Path.cwd() == ROOT
unit, message, *paths = sys.argv[1:]
record = json.loads((OUT/(unit+'.json')).read_text())
assert record['passed'] and record['fresh'] and not record['interrupted'] and not record['sourceMutationObserved']
assert record['exit'] == 0 and not record['expectedDiagnostic']
assert json.loads((OUT/'ledger.jsonl').read_text().splitlines()[-1])['unit'] == unit, 'No intervening compiler invocation'
assert sha((ROOT/record['path']).read_bytes()) == record['sourceSHA256']
assert paths and len(paths) == len(set(paths))
repair_checks = []
for path in paths:
 assert path in REPAIRS or path in DOCUMENTARY or (path.startswith(('research-tests/O6-L2R13-', 'research-tests/run-l2r13-')) and not path.endswith('.idr'))
 assert (ROOT/path).is_file() and (ROOT/path).stat().st_size > 0
 if path in DOCUMENTARY:
  repair=DOCUMENTARY[path];before=git('show','HEAD:'+path)
  assert sha(before)==repair['beforeSHA256']
  assert before.replace(repair['old'].encode(),repair['new'].encode())==(ROOT/path).read_bytes()
  assert sha((ROOT/path).read_bytes())==repair['afterSHA256']
  repair_checks.append(dict(path=path,**repair))
 if path in REPAIRS:
  before = git('show', 'HEAD:'+path)
  repair = REPAIRS[path]
  old, new = repair['old'].encode(), repair['new'].encode()
  assert all(line.startswith(b'|||') for line in old.splitlines()+new.splitlines()), 'Comment-only exact repair'
  assert sha(before) == repair['beforeSHA256']
  assert before.count(old) == 1 and (ROOT/path).read_bytes() == before.replace(old, new)
  assert sha((ROOT/path).read_bytes()) == repair['afterSHA256']
  currentHash=sha((ROOT/path).read_bytes())
  validations=[json.loads(line) for line in (OUT/'ledger.jsonl').read_text().splitlines()]
  assert any(r['unit'].startswith('V') and r['path']==path and r['passed'] and r['fresh'] and r['sourceSHA256']==currentHash for r in validations), 'Comment repair needs exact final source fresh PASS'
  repair_checks.append(dict(path=path, beforeSHA256=sha(before), repairedSHA256=currentHash, authority=repair['authority']))
assert not git('diff', '--cached', '--name-only').strip()
dirty = git('diff', '--name-only').decode().splitlines()
assert set(dirty) <= set(paths), 'Unlisted tracked changes'
assert not any(p.endswith('.idr') and p not in REPAIRS for p in dirty), 'No new-source delta at artifact boundary'
processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)', row) for row in processes.splitlines()), 'Own compiler running; main-lane compilers are separate'
assert git('branch', '--show-current').decode().strip() == 'cp5-thm73-lane-a8a10'
subprocess.run(['git', 'diff', '--check'], cwd=ROOT, check=True)
hashes = {p: sha((ROOT/p).read_bytes()) for p in paths}
subprocess.run(['git', 'add', '--', *paths], cwd=ROOT, check=True)
assert set(git('diff', '--cached', '--name-only').decode().splitlines()) <= set(paths)
subprocess.run(['git', 'commit', '-m', message], cwd=ROOT, check=True)
assert not git('diff', '--cached', '--name-only').strip()
receipt = dict(event='GUARDED ARTIFACT COMMIT', unit=unit, invocation=unit, sourceInvocation=record['unit'], sourceHash=record['sourceSHA256'], resultingCommitHash=git('rev-parse', 'HEAD').decode().strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), paths=paths, artifactHashes=hashes, authorizedCommentRepairs=repair_checks, guardChecksPassed=['fresh PASS', 'exit 0', 'not interrupted', 'no source mutation', 'exact source SHA256', 'no intervening compiler invocation', 'artifact paths or exact authorized comment repairs only', 'no new Idris source delta', 'no pre-staged files', 'no own compiler', 'git diff --check', 'git commit success', 'no post-staged files'])
with (OUT/'commit-receipts.jsonl').open('a') as ledger:
 ledger.write(json.dumps(receipt)+'\n')
print('GUARDED ARTIFACT COMMIT', json.dumps(receipt), flush=True)
