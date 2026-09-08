#!/usr/bin/env python3
"""Compiler-free independent audit of R189 exact records/commit-time receipts.
Usage: python3 -I research-tests/run-r189-verify-evidence.py --expected-a N --expected-b N --expected-mechanical N --expected-bodies N --expected-validations N
Never compiles, stages, edits sources, or deletes caches. The closing archive's
own artifact receipt necessarily lives outside itself and is reported at gate.
Expected counts are explicit review inputs, not inferred from missing records.
"""
import argparse
import collections
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import tarfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser()
parser.add_argument('--expected-a', type=int, required=True)
parser.add_argument('--expected-b', type=int, required=True)
parser.add_argument('--expected-mechanical', type=int, required=True)
parser.add_argument('--expected-bodies', type=int, required=True)
parser.add_argument('--expected-validations', type=int, required=True)
args = parser.parse_args()
assert 0 <= args.expected_a <= 16 and 0 <= args.expected_b <= 9
assert 0 <= args.expected_mechanical <= 52 and 0 <= args.expected_bodies <= 1

def sha(data):
    return hashlib.sha256(data).hexdigest()
def git(*parts):
    return subprocess.check_output(['git', *parts], cwd=ROOT)
def utc(text):
    return datetime.datetime.fromisoformat(text)
def declarations(data):
    text = data.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:', text, re.M) +
               re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)', text, re.M))

ledger = json.loads((ROOT/'research-tests/O6-R189-COMPILER-LEDGER.json').read_text())
assert ledger['shift'] == 'R189'
assert ledger['startCommit'] == git('rev-parse','8e133ed5').decode().strip()
archive = ROOT/'research-tests'/ledger['evidenceArchive']
assert sha(archive.read_bytes()) == ledger['evidenceArchiveSHA256']
records = ledger['records']
assert len(records) == ledger['recordCount']
assert len({r['invocation'] for r in records}) == len(records)
qualified = ledger['invocationQualifications']
assert qualified == {}, 'No R189 invocation relabeling is authorized'
raw, sources, normalized = {}, {}, {}
archiveRoot = 'dgamma-r189/'
with tarfile.open(archive, 'r:gz') as tar:
    dual_roles = ledger.get('finalValidationDualRoles', {})
    if dual_roles:
        assert dual_roles == json.loads(tar.extractfile(archiveRoot+'final-validation-dual-roles.json').read())
    archived_ledger = [json.loads(line) for line in tar.extractfile(archiveRoot+'ledger.jsonl').read().decode().splitlines()]
    assert len(archived_ledger) == len(records)
    if qualified:
        assert qualified == json.loads(tar.extractfile(archiveRoot+'invocation-qualifications.json').read())
    archived_receipts = [json.loads(line) for line in tar.extractfile(archiveRoot+'commit-receipts.jsonl').read().decode().splitlines()]
    assert archived_receipts == ledger['commitReceipts']
    for r in records:
        invocation = r['invocation']
        exact = json.loads(tar.extractfile(archiveRoot+r['record']).read())
        source = tar.extractfile(archiveRoot+r['source']).read()
        log = tar.extractfile(archiveRoot+r['log']).read().decode()
        assert source and sha(source) == r['sourceHash'] == exact['sourceSHA256'], invocation
        assert log == exact['transcript'], invocation
        assert exact in archived_ledger, invocation
        expected_line = r'^\d+/\d+: Building DGamma\.' + re.escape(pathlib.Path(exact['path']).stem) + r' \(' + re.escape(exact['path']) + r'\)$'
        fresh = exact['path'] == 'package' or bool(re.search(expected_line, log, re.M))
        assert exact['fresh'] == fresh, invocation
        diagnostic = exact['expectedDiagnostic']
        passed = fresh and not exact['interrupted'] and (
            exact['exit'] != 0 and diagnostic in log and (not exact.get('symbol') or exact['symbol'] in log)
            if diagnostic else exact['exit'] == 0 and 'Error:' not in log)
        assert exact['passed'] == passed, invocation
        assert exact['unit'] == invocation and exact['path'] == r['target']
        for field in ['passed', 'fresh', 'interrupted', 'exit', 'command', 'expectedDiagnostic']:
            assert r[field] == exact[field], (invocation, field)
        match = re.fullmatch(r'([A-Z]+\d+)-(\d+)', invocation)
        q = qualified.get(invocation, {})
        assert r['effectiveUnit'] == q.get('effectiveUnit', match[1] if match else invocation)
        assert r['effectiveAttempt'] == q.get('effectiveAttempt', int(match[2]) if match else None)
        path = 'dgamma.ipkg' if r['target'] == 'package' else r['target']
        for commit in r['matchingSourceCommits']:
            assert sha(git('show', commit+':'+path)) == r['sourceHash']
        raw[invocation], sources[invocation], normalized[invocation] = exact, source, r
assert ledger['passedCount'] == sum(r['passed'] for r in records)
assert ledger['failedCount'] == sum(not r['passed'] for r in records)
assert ledger['invalidValidationCount'] == 0 and not ledger['validationQualifications']
assert ledger['qualifiedPassedCount'] == ledger['passedCount']
ordered = sorted(raw.values(), key=lambda r: r['start'])
for first, second in zip(ordered, ordered[1:]):
    assert utc(first['end']) <= utc(second['start']), (first['unit'], second['unit'])
assert not any(r['interrupted'] for r in raw.values())
assert max(r['maxSampleRSSKiB'] for r in raw.values()) <= 48*1024*1024
receipts = ledger['commitReceipts']
source_receipts = [r for r in receipts if r['event'] == 'GUARDED COMMIT']
expected_units = {'A'+str(i) for i in range(1,args.expected_a+1)} | {'B'+str(i) for i in range(2,args.expected_b+2)}
assert len(source_receipts) == len(expected_units)
assert {r['unit'] for r in source_receipts} == expected_units
proof_runs = [r for r in raw.values() if re.fullmatch(r'[AB]\d+-\d+', r['unit'])]
grouped = collections.defaultdict(list)
for r in proof_runs:
    n = normalized[r['unit']]
    grouped[n['effectiveUnit']].append(n['effectiveAttempt'])
    assert utc(r['start']) < datetime.datetime(2026, 9, 8, 15, 9, 50, tzinfo=datetime.timezone.utc)
    assert b'%default total' in sources[r['unit']] and b'%unbound_implicits off' in sources[r['unit']]
    prior = [q for q in source_receipts if raw[q['invocation']]['path'] == r['path'] and utc(q['timestampUTC']) <= utc(r['start'])]
    commit = max(prior, key=lambda q: q['timestampUTC'])['resultingCommitHash'] if prior else ledger['startCommit']
    old = subprocess.run(['git', 'show', commit+':'+r['path']], cwd=ROOT, capture_output=True)
    added = declarations(sources[r['unit']]) - declarations(old.stdout if old.returncode == 0 else b'')
    assert len(added) == 1, (r['unit'], added)
assert set(grouped) == expected_units
assert all(sorted(attempts) == list(range(1, max(attempts)+1)) and max(attempts) <= 3 for attempts in grouped.values())
result_declarations = []
for receipt in source_receipts:
    invocation = receipt['invocation']
    r = raw[invocation]
    assert r['passed'] and r['fresh'] and r['exit'] == 0 and not r['interrupted'] and r['expectedDiagnostic'] is None
    assert invocation == receipt['unit']+'-'+receipt['attempt']
    assert receipt['unit'] == normalized[invocation]['effectiveUnit']
    assert receipt['sourceHash'] == r['sourceSHA256']
    commit = receipt['resultingCommitHash']
    assert sha(git('show', commit+':'+r['path'])) == r['sourceSHA256']
    assert git('diff-tree', '--no-commit-id', '--name-only', '-r', commit).decode().splitlines() == [r['path']]
    assert utc(r['end']) <= utc(receipt['timestampUTC'])
    assert not any(utc(r['end']) <= utc(other['start']) < utc(receipt['timestampUTC']) for other in raw.values() if other['unit'] != invocation), invocation
    assert 'exact source SHA256' in receipt['guardChecksPassed'] and 'no post-staged files' in receipt['guardChecksPassed']
    old = subprocess.run(['git', 'show', commit+'^:'+r['path']], cwd=ROOT, capture_output=True)
    added = declarations(sources[invocation]) - declarations(old.stdout if old.returncode == 0 else b'')
    assert len(added) == 1, (invocation, added)
    result_declarations.append(dict(unit=receipt['unit'], effectiveAttempt=normalized[invocation]['effectiveAttempt'], declaration=next(iter(added)), commit=commit))
artifacts = [r for r in receipts if r['event'] == 'GUARDED ARTIFACT COMMIT']
for receipt in artifacts:
    assert all(key in receipt for key in ['unit', 'attempt', 'sourceInvocation', 'paths'])
    r = raw[receipt['sourceInvocation']]
    assert r['passed'] and r['fresh'] and r['exit'] == 0 and not r['interrupted'] and r['expectedDiagnostic'] is None
    assert receipt['sourceHash'] == r['sourceSHA256']
    changed = git('diff-tree', '--no-commit-id', '--name-only', '-r', receipt['resultingCommitHash']).decode().splitlines()
    assert set(changed).issubset(receipt['paths']) and all(p.startswith('research-tests/') and not p.endswith('.idr') for p in changed)

# Independently authenticate every mechanical multi-file move. The byte ranges
# are parsed from the immutable start, NOT trusted from the move runner.
CROSS='research/DGamma/CP5ConfluenceCrossTraceSpike.idr'
SURFACE='research/DGamma/CP5O19SurfaceSpike.idr'
original=git('show',ledger['startCommit']+':'+CROSS)
positions=list(re.finditer(rb'(?m)^(?:\|\|\|[^\n]*\n)*(?:(?:public export|export|private)\n)?(?=(?:record|data) |(?:[01] )?\w+[ \t]*:)(?:[01] )?(?:(?:record|data) )?([A-Za-z_]\w*)',original))
spans={m[1].decode():(m.start(),positions[i+1].start() if i+1<len(positions) else len(original)) for i,m in enumerate(positions)}
names=[m[1].decode() for m in positions[:28] if m[1] != b'CertifiedActorPermutation']
assert len(names)==27 and names[0]=='AdjacentActorOrderSwap' and names[-1]=='blockSwapOccurrenceCorrespondence'
names+=['CertifiedActorPermutation','OperationalActorPermutation','MappedCanonicalSupportOrders','canonicalActorBlockDecomposition','CertifiedOperationalCanonicalPermutation']
chunks={name:original[slice(*spans[name])] for name in names}
header=original[:positions[0].start()].replace(b'module DGamma.CP5ConfluenceCrossTraceSpike',b'module DGamma.CP5O19SurfaceSpike')
mechanical=[r for r in receipts if r['event']=='GUARDED MECHANICAL COMMIT']
assert len(mechanical)==args.expected_mechanical
mechanical_units=set()
with tarfile.open(archive,'r:gz') as tar:
    for receipt in mechanical:
        unit=receipt['invocation']; r=raw[unit]; commit=receipt['resultingCommitHash']
        assert r['passed'] and r['fresh'] and r['exit']==0 and not r['interrupted'] and r['expectedDiagnostic'] is None
        assert unit==receipt['unit']+'-'+receipt['attempt']
        assert r['sourceSHA256']==receipt['sourceHash']
        assert utc(r['end'])<=utc(receipt['timestampUTC'])
        assert not any(utc(r['end'])<=utc(o['start'])<utc(receipt['timestampUTC']) for o in raw.values() if o['unit']!=unit)
        metadata=json.loads(tar.extractfile(archiveRoot+unit+'.mechanical.json').read())
        assert metadata==receipt['mechanical']
        assert git('rev-parse',commit+'^').decode().strip()==metadata['priorCommit']
        changed=git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines()
        assert set(changed)==set(receipt['sourceHashes'])
        for path,digest in receipt['sourceHashes'].items():
            source=tar.extractfile(archiveRoot+unit+'.'+pathlib.Path(path).name+'.source').read()
            assert sha(source)==digest==sha(git('show',commit+':'+path))
        if receipt['unit'].startswith('M'):
            index=int(receipt['unit'][1:]); name=names[index-1]
            expected_cross=original
            for prior in names[:index]: expected_cross=expected_cross.replace(chunks[prior],b'',1)
            expected_cross=expected_cross.replace(b'\n\nimport DGamma.Core',b'\n\nimport public DGamma.CP5O19SurfaceSpike\nimport DGamma.Core',1)
            assert git('show',commit+':'+CROSS)==expected_cross
            expected_lower=header+b''.join(chunks[n] for n in (names[:index] if index<=27 else names[:26]+names[27:index]+[names[26]]))
            if index>27: expected_lower=expected_lower[:-1]
            assert git('show',commit+':'+SURFACE)==expected_lower
            assert metadata['declaration']==name and metadata['declarationSHA256']==sha(chunks[name])
            assert re.search(r'^\d+/\d+: Building DGamma\.CP5O19SurfaceSpike \(research/DGamma/CP5O19SurfaceSpike.idr\)$',r['transcript'],re.M)
        elif receipt['unit'].startswith('I'):
            assert receipt['unit'].startswith('I') and len(changed)==1
            path=changed[0]; old=git('show',commit+'^:'+path)
            assert old.count(b'import DGamma.CP5ConfluenceCrossTraceSpike\n')==1
            assert git('show',commit+':'+path)==old.replace(b'import DGamma.CP5ConfluenceCrossTraceSpike\n',b'import DGamma.CP5O19SurfaceSpike\n',1)
        else:
            assert receipt['unit']=='W1' and changed==[SURFACE]
            old=git('show',commit+'^:'+SURFACE)
            assert old.endswith(b'\n\n') and git('show',commit+':'+SURFACE)==old[:-1]
            assert metadata['kind']=='approved final separator normalization'
        mechanical_units.add(receipt['unit'])
assert len(mechanical_units)==args.expected_mechanical
assert {r['unit'].rsplit('-',1)[0] for r in raw.values() if re.fullmatch(r'[MIW]\d+-\d+',r['unit'])}==mechanical_units
bodies=[r for r in receipts if r['event']=='GUARDED BODY COMMIT']
assert len(bodies)==args.expected_bodies
for receipt in bodies:
    r=raw[receipt['invocation']]; commit=receipt['resultingCommitHash']
    assert r['passed'] and r['fresh'] and r['exit']==0 and not r['interrupted']
    assert r['sourceSHA256']==receipt['sourceHash']==sha(git('show',commit+':'+CROSS))
    assert git('diff-tree','--no-commit-id','--name-only','-r',commit).decode().splitlines()==[CROSS]
    assert utc(r['end'])<=utc(receipt['timestampUTC'])
    assert not any(utc(r['end'])<=utc(o['start'])<utc(receipt['timestampUTC']) for o in raw.values() if o['unit']!=r['unit'])
    old=git('show',commit+'^:'+CROSS); new=git('show',commit+':'+CROSS)
    symbol=b'operationalAdjacentBlockSwapSpike'
    statement=lambda s:s[s.index(b'0 '+symbol+b' :'):s.index(b'\n'+symbol+b' ',s.index(b'0 '+symbol+b' :'))]
    assert statement(old)==statement(new)
    assert b'?operationalAdjacentBlockSwapSpike_rhs' in old and b'?operationalAdjacentBlockSwapSpike_rhs' not in new
    new_without_import=new.replace(b'import DGamma.CP5O19OperationalAssemblySpike\n',b'',1)
    start=new_without_import.index(b'\n'+symbol+b' ',new_without_import.index(b'0 '+symbol+b' :'))+1
    end=new_without_import.index(b'\n\n',start)
    assert new_without_import[:start]+b'operationalAdjacentBlockSwapSpike = ?operationalAdjacentBlockSwapSpike_rhs'+new_without_import[end:]==old
body_runs=[r for r in raw.values() if re.fullmatch(r'O19-\d+',r['unit'])]
assert len(body_runs)<=3 and (bool(body_runs)==bool(args.expected_bodies))
assert len(source_receipts)+len(artifacts)+len(mechanical)+len(bodies)==len(receipts)
for r in raw.values():
    assert utc(r['start'])<datetime.datetime(2026,9,8,15,9,50,tzinfo=datetime.timezone.utc),r['unit']

validations = [r for r in records if re.fullmatch(r'V\d+', r['invocation'])]
assert len(validations) == args.expected_validations
assert all(r['passed'] and r['fresh'] for r in validations)
for unit, role in dual_roles.items():
    assert raw[unit]['passed'] and raw[unit]['fresh'] and raw[unit]['exit'] == 0 and not raw[unit]['interrupted']
    assert role['target'] == raw[unit]['path'] and role['sourceHash'] == raw[unit]['sourceSHA256']
    assert sha(git('show', ledger['endCommit']+':'+role['target'])) == role['sourceHash']
assert not git('diff', '--cached', '--name-only').strip()
assert not git('diff', '34b21c9', '--', 'src/', 'dgamma.ipkg').strip()
assert not git('diff', ledger['startCommit'], '--', 'research/DGamma/CP5ConfluenceLocalDiamondSpike.idr').strip()
assert git('hash-object', 'src/DGamma/CP3.idr').decode().strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
modules = re.findall(r'DGamma\.[A-Za-z0-9_.]+', (ROOT/'dgamma.ipkg').read_text())
assert len(modules) == 207 and all((ROOT/'build/ttc/2025081600'/(m.replace('.', '/')+'.ttc')).is_file() for m in modules)
report = dict(shift='R189', checkedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), endCommit=ledger['endCommit'],
    records=len(records), passed=ledger['passedCount'], rejected=ledger['failedCount'], proofInvocations=len(proof_runs),
    sourceReceipts=len(source_receipts), artifactReceipts=len(artifacts), mechanicalReceipts=len(mechanical), bodyReceipts=len(bodies), bodyInvocations=len(body_runs), validValidations=len(validations), finalValidationDualRoles=dual_roles, finalValidationRoles=len(validations)+len(dual_roles),
    expectedNegativeValidations=sum(r['expectedDiagnostic'] is not None for r in validations),
    invalidValidationCount=0, serialized=True, interrupted=0, maximumRSSKiB=max(r['maxSampleRSSKiB'] for r in raw.values()),
    oneNewDeclarationPerProofInvocation=True, oneNewDeclarationPerSourceCommit=True, effectiveAttemptCapsPassed=True,
    invocationQualifications=qualified, sourceDeclarations=result_declarations, archiveSHA256=ledger['evidenceArchiveSHA256'],
    seeds='207/207', productionDiff='empty', LocalDiamondDiff='empty', noStagedFiles=True,
    finalArtifactReceiptQualification='Archive cannot contain its own commit-time receipt; final live receipt is reported separately at gate.')
print(json.dumps(report, indent=2))
