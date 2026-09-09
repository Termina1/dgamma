#!/usr/bin/env python3
"""Compiler-free, separately executable L2R5 evidence/receipt/scope verifier.
Reconstructs evidence from lane2 files and git objects, not audit prose. It is
NOT an independent human proof review. No compiler, cache modification or main
worktree access occurs. Writes only /tmp/dgamma-l2r5/independent-verification.json.
"""
import ast, datetime, hashlib, json, pathlib, re, subprocess, tarfile
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r5')
BASE = '769d332d'
OWNED = 'research-tests/O6-L2R5-Sources/'
def git(*args):
 return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
 return hashlib.sha256(data).hexdigest()
def declarations(data):
 text = data.decode()
 return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:', text, re.M) + re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)', text, re.M))
def code(data):
 return '\n'.join(line for line in data.decode().splitlines() if not line.lstrip().startswith(('|||', '--')))
def building(record, path):
 return re.search(r'^\d+/\d+: Building DGamma\.' + re.escape(pathlib.Path(path).stem) + r' \(' + re.escape(str(ROOT/path)) + r'\)$', record['transcript'], re.M)
assert pathlib.Path.cwd() == ROOT
assert git('branch', '--show-current').decode().strip() == 'cp5-thm73-lane-a8a10'
subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, 'HEAD'], cwd=ROOT, check=True)
records = [json.loads(line) for line in (OUT/'ledger.jsonl').read_text().splitlines()]
byunit = {r['unit']: r for r in records}
assert len(byunit) == len(records)
receipts = [json.loads(line) for line in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
bycommit = {r['resultingCommitHash']: r for r in receipts}
assert len(bycommit) == len(receipts)
for r in records:
 assert json.loads((OUT/(r['unit']+'.json')).read_text()) == r
 assert (OUT/(r['unit']+'.log')).read_text() == r['transcript']
 assert sha((OUT/(r['unit']+'.source')).read_bytes()) == r['sourceSHA256']
 assert r['path'].startswith(OWNED) or (r['unit']=='V0' and r['path']=='research-tests/O6-L2R4-Sources/DGamma/L2R4AnchorMeasure.idr')
 assert r['command'][-2:] == ['--check', str(ROOT/r['path'])]
 assert all('/Work/dgamma/' not in part for part in r['command'])
 assert r['targetMtimeTouch']['path'] == str(ROOT/r['path'])
 assert r['targetMtimeTouch']['newMtimeNs'] >= r['targetMtimeTouch']['oldMtimeNs']
 assert r['fresh'] == bool(building(r, r['path']))
 if r['passed']:
  assert r['fresh'] and not r['interrupted'] and not r['sourceMutationObserved']
  assert r['exit'] == 0 and not r['expectedDiagnostic'] and 'Error:' not in r['transcript']
 if r['maxSampleRSSKiB'] >= 19*1024*1024:
  assert r['heavyLockAcquired'], 'Heavy invocation lacked the shared launch lock'
 if r['sourceMutationObserved']:
  assert r['interrupted'] and not r['passed']
 assert not r.get('bundleSources'), 'No L2R5 bundle authority'
for first, second in zip(records, records[1:]):
 assert first['end'] <= second['start'], 'Overlapping lane-owned compiler invocations'
incidents = json.loads((OUT/'protocol-incidents.json').read_text())
assert incidents == [], 'New incident requires explicit independent-review qualification'
sourcecommits = git('log', '--format=%H', BASE+'..HEAD', '--', OWNED).decode().splitlines()
for commit in sourcecommits:
 receipt = bycommit[commit]
 r = byunit[receipt['invocation']]
 assert receipt['event'] == 'GUARDED COMMIT' and r['passed']
 assert r['sourceSHA256'] == receipt['sourceHash']
 changed = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).decode().splitlines()
 expected = [r['path']] + [x['path'] for x in r.get('bundleSources', [])]
 assert set(changed) == set(expected)
 new = git('show', commit+':'+r['path'])
 old = subprocess.run(['git', 'show', commit+'^:'+r['path']], cwd=ROOT, capture_output=True).stdout
 assert sha(new) == r['sourceSHA256'] and len(declarations(new)-declarations(old)) == 1
 for extra in r.get('bundleSources', []):
  assert sha(git('show', commit+':'+extra['path'])) == extra['sourceSHA256']
 assert r['end'] <= receipt['timestampUTC']
 assert not any(r['end'] < other['start'] < receipt['timestampUTC'] for other in records), 'Commit followed another compiler invocation'
allcommits = git('log', '--format=%H', BASE+'..HEAD').decode().splitlines()
assert set(allcommits) == set(bycommit), 'Every shift commit must have exactly one guarded receipt'
for commit in allcommits:
 receipt = bycommit[commit]
 if receipt['event'] != 'GUARDED ARTIFACT COMMIT':
  continue
 r=byunit[receipt['invocation']]
 assert r['passed'] and r['fresh'] and r['sourceSHA256']==receipt['sourceHash']
 assert sha(git('show',commit+':'+r['path']))==r['sourceSHA256']
 assert r['end']<=receipt['timestampUTC']
 assert not any(r['end']<other['start']<receipt['timestampUTC'] for other in records)
 changed = git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).decode().splitlines()
 assert set(changed) <= set(receipt['paths'])
 for path in changed:
  assert sha(git('show', commit+':'+path)) == receipt['artifactHashes'][path]
planGroups = [('final-validation-plan.json','research-tests/O6-L2R5-FINAL-VALIDATION-PLAN.json')]
plans = []
seen_paths = set()
for localPlan, planpath in planGroups:
 assert (OUT/localPlan).read_bytes() == (ROOT/planpath).read_bytes()
 group = json.loads((OUT/localPlan).read_text())
 assert len({p['path'] for p in group}) == len(group) == len({p['unit'] for p in group})
 plancommits = git('log', '--format=%H', BASE+'..HEAD', '--', planpath).decode().splitlines()
 assert len(plancommits) == 1 and git('show', plancommits[0]+':'+planpath) == (ROOT/planpath).read_bytes(), 'Immutable plan changed after publication'
 assert bycommit[plancommits[0]]['timestampUTC'] <= byunit[group[0]['unit']]['start']
 for item in group:
  assert set(item.get('dependsOn', [])) <= seen_paths, 'Plan is not leaf-before-dependent'
  seen_paths.add(item['path'])
  r = byunit[item['unit']]
  assert r['passed'] and r['fresh'] and not r['interrupted'] and not r['sourceMutationObserved']
  assert r['path'] == item['path'] and r['sourceSHA256'] == item['sourceHash']
  assert sha((ROOT/r['path']).read_bytes()) == r['sourceSHA256']
 plans += group
# No predecessor source or runner repair is authorized in L2R5.
repairs = {}
paths = git('diff', '--name-only', BASE).decode().splitlines()
allowed = ('research-tests/O6-L2R5-', 'research-tests/run-l2r5-')
assert all(p in repairs or p.startswith(allowed) for p in paths)
newdecls = {}
for path in paths:
 if not path.endswith('.idr') or path in repairs:
  continue
 assert path.startswith(OWNED)
 old = subprocess.run(['git', 'show', BASE+':'+path], cwd=ROOT, capture_output=True).stdout
 current = (ROOT/path).read_bytes()
 assert old == b'', 'Only new lane-owned Idris modules permitted'
 assert not re.search(r'\b(believe_me|assert_total|postulate|assert_smaller|partial|with|let)\b|\?[A-Za-z_]', code(current))
 assert '%default total' in current.decode()
 newdecls[path] = sorted(declarations(current))
 assert any(p['path'] == path for p in plans), 'Missing current-source final fresh check'
assert sum(map(len, newdecls.values())) == len(sourcecommits) == 33
for letter, cap, retained in [('A',20,20), ('B',16,5), ('C',10,10)]:
 attempts = {}
 for r in records:
  match = re.fullmatch(letter+r'(\d+)-(\d+)', r['unit'])
  if match:
   assert 1 <= int(match[1]) <= cap and 1 <= int(match[2]) <= 3
   attempts.setdefault(int(match[1]), []).append(r)
 assert set(attempts) == set(range(1, retained+1))
 for group in attempts.values():
  assert [int(r['unit'].rsplit('-', 1)[1]) for r in group] == list(range(1, len(group)+1))
  if group[0]['unit'].rsplit('-',1)[0] in {'A11','B5'}:
   assert len(group) == 3 and not any(r['passed'] for r in group)
   stopped={'A11':'twoHeadLookupRightObserved','B5':'providerHeadObservation'}[group[0]['unit'].rsplit('-',1)[0]]
   assert not (ROOT/group[-1]['path']).exists() or stopped not in declarations((ROOT/group[-1]['path']).read_bytes()), 'Stopped declaration not reverted'
  else:
   assert len(group) <= 3 and group[-1]['passed'] and sum(r['passed'] for r in group) == 1
publication = ''
manifest = json.loads((ROOT/('research-tests/O6-L2R5'+publication+'-COMPILER-LEDGER.json')).read_text())
archive = ROOT/('research-tests/O6-L2R5'+publication+'-COMPILER-EVIDENCE.tar.gz')
assert manifest['recordCount'] == len(records) and manifest['passedCount'] == sum(r['passed'] for r in records)
assert manifest['evidenceArchiveSHA256'] == sha(archive.read_bytes())
assert set(sourcecommits) <= {r['resultingCommitHash'] for r in manifest['commitReceipts']}
assert manifest['monitorQualifications'] == json.loads((OUT/'monitor-qualifications.json').read_text())
with tarfile.open(archive, 'r:gz') as tar:
 for r in records:
  for suffix in ['.json', '.log', '.source']:
   filename = r['unit']+suffix
   assert tar.extractfile(OUT.name+'/'+filename).read() == (OUT/filename).read_bytes()
  for extra in r.get('bundleSources', []):
   assert tar.extractfile(OUT.name+'/'+extra['sourceFile']).read() == (OUT/extra['sourceFile']).read_bytes()
 for localPlan, _ in planGroups:
  assert tar.extractfile(OUT.name+'/'+localPlan).read() == (OUT/localPlan).read_bytes()
rehome=json.loads((ROOT/'research-tests/O6-L2R5-CP3-REHOME-MANIFEST.json').read_text())
assert rehome['cp3Blob']==git('rev-parse','HEAD:src/DGamma/CP3.idr').decode().strip()
for p,h in rehome['checkedSourceSHA256'].items(): assert sha((ROOT/p).read_bytes())==h
moved='\n'.join((ROOT/'src/DGamma/CP3.idr').read_text().splitlines()[2092:2120])+'\n'
assert sha(moved.encode())==rehome['movedCombinedSHA256']
draft=(ROOT/'research-tests/O6-L2R5-CP3-DIFF-DRAFT.md').read_text()
for section in rehome['tier1Sections']:
 fragment=draft.split('### '+section['title']+'\n\n```idris\n',1)[1].split('```',1)[0]
 assert sha(fragment.encode())==section['sha256']
assert 'NOT YET SIGNABLE' in draft and 'UNCHECKED' in draft
assert not git('diff', BASE, '--', 'src/', 'research/', 'dgamma.ipkg', 'README.md', 'NOTES.md', 'THM73-PLAN.md')
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only'), 'Commit artifacts before independent verification'
assert not git('ls-files', '--others', '--exclude-standard'), 'Untracked deliverable remains'
processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)', row) for row in processes.splitlines()), 'Own compiler running'
lockowner = json.loads(pathlib.Path('/tmp/dgamma-heavy.lock/owner').read_text()) if pathlib.Path('/tmp/dgamma-heavy.lock/owner').exists() else None
assert not lockowner or lockowner.get('lane') != 'lane2', 'Own heavy lock remains'
shift = json.loads((OUT/'shift.json').read_text())
assert all(r['start'] < shift['attemptCutoff'] for r in records if re.fullmatch(r'[ABC]\d+-\d+', r['unit']))
assert all(byunit[p['unit']]['end'] < shift['validationCutoff'] for p in plans)
report = dict(status='PASS', immutablePlanPublishedBeforeValidation=True, finalPlanLeafBeforeDependent=True, head=git('rev-parse', 'HEAD').decode().strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), invocationCount=len(records), passedCount=sum(r['passed'] for r in records), failedCount=sum(not r['passed'] for r in records), interruptedCount=sum(r['interrupted'] for r in records), finalCheckCount=len(plans), newDeclarationCount=sum(map(len, newdecls.values())), newDeclarations=newdecls, sourceCommitCount=len(sourcecommits), allShiftCommitsReceiptAuthenticated=True, noUnapprovedBundles=True, noPredecessorEdits=True, allInvocationsSerialized=True, allRecordedSnapshotsAndLogsAuthenticated=True, protocolIncidents=incidents, allFinalCurrentSourcesAuthenticated=True, committedArchiveAndManifestAuthenticated=True, evidenceArchiveSHA256=sha(archive.read_bytes()), productionAndFrozenResearchUntouched=True, maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records), RSSQualification='250ms sampled RSS, not continuous peak; chez classified from the first L2R5 invocation', noUnsafeNewProofs=True, noOwnCompiler=True, noOwnHeavyLock=True, observedNonOwnedHeavyLock=lockowner, noStagedFiles=True, cleanTrackedTree=True, noUntrackedDeliverables=True, manualProofReviewStillRequired=True, humanProofReviewGateRequired=True)
(OUT/'independent-verification.json').write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps({k: v for k, v in report.items() if k != 'newDeclarations'}, indent=2))
