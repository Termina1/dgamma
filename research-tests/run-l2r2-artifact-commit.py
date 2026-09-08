#!/usr/bin/env python3
"""Guarded artifact commit after an independently inspected exact-source PASS.
Only L2R2 artifacts, plus TWO exact supervisor-authorized predecessor comment
repairs, are accepted. The latter are authenticated against the shift base;
Idris declarations and Python executable code in predecessors must not change.
Usage: python3 -I research-tests/run-l2r2-artifact-commit.py UNIT MESSAGE PATH...
"""
import datetime, hashlib, json, pathlib, re, subprocess, sys
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r2')
BASE = '986342303cce59c27c157867cfeb124d3147a9f0'
REPAIRS = {
 'research-tests/run-l2r1-check.py': (
  b'Uses absolute compiler arguments, never touches sources or deletes build data.',
  b'Uses absolute compiler arguments; never changes source contents or deletes build data; performs the approved target-only mtime touch.'),
 'research-tests/DGamma/L2R1RootHoist.idr': (
  b'||| Explicit small source/original-cut/alternate-cut states. Root2 has empty\n||| provisions, so this is the ADMISSIBLE fixture, not the blocked R174 collision.\n||| No recursively nested evaluator builds these state indices.',
  b'||| Candidate admissible-root states (trace/square NOT proved in L2R1).\n||| Root2 has empty provisions, unlike the blocked R174 collision.\n||| No recursively nested evaluator builds these state indices.')
}
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
 assert path in REPAIRS or (path.startswith(('research-tests/O6-L2R2-', 'research-tests/run-l2r2-')) and not path.endswith('.idr'))
 assert (ROOT/path).is_file() and (ROOT/path).stat().st_size > 0
 if path in REPAIRS:
  before = git('show', BASE+':'+path)
  old, new = REPAIRS[path]
  assert before.count(old) == 1 and (ROOT/path).read_bytes() == before.replace(old, new)
  repair_checks.append(dict(path=path, baseSHA256=sha(before), repairedSHA256=sha((ROOT/path).read_bytes()), authority='Explicit supervisor docs-only repair ruling; exact byte replacement'))
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
