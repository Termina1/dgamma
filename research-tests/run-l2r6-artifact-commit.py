#!/usr/bin/env python3
"""Guarded artifact commit after an independently inspected exact-source PASS.
Accept lane-owned L2R6 non-Idris artifacts, the predecessor CP3 draft/manifest
and docs-only run-l2r5-draft.py, plus the exact authorized Idris comment repair.
Usage: python3 -I research-tests/run-l2r6-artifact-commit.py UNIT MESSAGE PATH...
"""
import datetime, hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r6')
BASE = 'c09c0da2'
REPAIR = json.loads((ROOT/'research-tests/O6-L2R6-COMMENT-REPAIR.json').read_text())
REPAIRS = {REPAIR['path']: (REPAIR['old'].encode(), REPAIR['new'].encode())}

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
 assert path in {'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md','research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json','research-tests/run-l2r5-draft.py'} or path in REPAIRS or (path.startswith(('research-tests/O6-L2R6-', 'research-tests/run-l2r6-')) and not path.endswith('.idr'))
 assert (ROOT/path).is_file() and (ROOT/path).stat().st_size > 0
 if path in REPAIRS:
  before = git('show', 'HEAD:'+path)
  old, new = REPAIRS[path]
  assert before.count(old) == 1 and (ROOT/path).read_bytes() == before.replace(old, new)
  currentHash=sha((ROOT/path).read_bytes())
  validations=[json.loads(line) for line in (OUT/'ledger.jsonl').read_text().splitlines()]
  assert any(r['unit'].startswith('V') and r['path']==path and r['passed'] and r['fresh'] and r['sourceSHA256']==currentHash for r in validations), 'Comment repair needs exact final source fresh PASS'
  repair_checks.append(dict(path=path, beforeSHA256=sha(before), repairedSHA256=currentHash, authority=REPAIR['authority']))
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
