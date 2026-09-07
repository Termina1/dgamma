#!/usr/bin/env python3
"""Read-only final R178 audit. Writes JSON outside the repository; no compilation."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
START = '6d6ab285ba0c173101d49e3aa7c8492122635b9e'
PARTS = ['CanonicalSort', 'CrossTrace', 'LocalDiamond', 'DeletionChain', 'RenamingComposition']
PATHS = {p: 'research/DGamma/CP5Confluence'+p+'Spike.idr' for p in PARTS}

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

def source(path):
    return (ROOT/path).read_text()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def declaration(text, name):
    start = text.index('0 '+name+' :')
    body = text.index('\n'+name+' =', start)
    return text[start:body], text[body+1:].split('\n\n', 1)[0]

def without_a9(text):
    return re.sub(r'  \(0 leftRightGeneratedMatched : GeneratedOrchestrationMatched .*?\(generatedGenerationBijection sameInputs\)\) ->\n', '', text, flags=re.S)

assert git('branch', '--show-current').strip() == 'cp5-thm73-scoping'
assert not git('diff', '34b21c9', '--', 'src/', 'dgamma.ipkg')
assert git('hash-object', 'src/DGamma/CP3.idr').strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
assert not git('diff', '--cached', '--name-only') and not git('diff', '--name-only')
assert not git('diff', '--check', START)
untracked = git('ls-files', '--others', '--exclude-standard').splitlines()
assert all(p.startswith('paper/') or p == 'review-o6-body-adversarial.md' for p in untracked)
processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', processes)
for part in ['CanonicalSort', 'LocalDiamond']:
    assert not git('diff', START, '--', PATHS[part]), part
local = (ROOT/PATHS['LocalDiamond']).read_bytes()
start = local.index(b'0 adjacentSwapSuffixSpike :')
full_sha, statement_sha = sha(local[start:start+1470]), sha(local[start:start+1154])
assert full_sha == '2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf'
assert statement_sha == '3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf'
protected = {}
for part, name in [('CanonicalSort', 'sortClosingFreeTraceSpike'),
                   ('CrossTrace', 'operationalAdjacentBlockSwapSpike'),
                   ('CrossTrace', 'selectOperationalCanonicalPermutationSpike'),
                   ('CrossTrace', 'canonicalSchedulesConvergeSpike'),
                   ('RenamingComposition', 'replayedCanonicalToOriginalEndpointSpike')]:
    old_type, old_body = declaration(git('show', START+':'+PATHS[part]), name)
    new_type, new_body = declaration(source(PATHS[part]), name)
    assert old_body == new_body, name
    assert old_type == without_a9(new_type), name
    protected[name] = dict(bodyUnchanged=True, signatureChange='explicit A9 only' if old_type != new_type else 'none', bodySHA256=sha(new_body.encode()))
old_deletion = git('show', START+':'+PATHS['DeletionChain'])
new_deletion = source(PATHS['DeletionChain'])
visibility = '||| R178 coverage API: existing discipline/provenance lemma only.\n||| This does not call the frozen deletion theorem or prove O21 withdrawals.\nexport\n'
assert new_deletion.replace(visibility, '', 1) == old_deletion
review = sha((ROOT/'review-o6-body-adversarial.md').read_bytes())
assert review == '61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8'
holes = {p: re.findall(r'\?\w+', source(PATHS[p])) for p in PARTS}
assert [len(holes[p]) for p in PARTS] == [1, 3, 0, 0, 1]
changed_idris = [p for p in git('diff', '--name-only', START, '--', 'research/', 'research-tests/DGamma/').splitlines() if p.endswith('.idr')]
assert all('%default total' in source(p) for p in changed_idris)
zero_holes = {p: re.findall(r'\?\w+', source(p)) for p in changed_idris if p not in PATHS.values()}
assert not any(zero_holes.values())
added = [line[1:] for line in git('diff', START, '--', 'research/', 'research-tests/DGamma/').splitlines() if line.startswith('+') and not line.startswith('+++')]
code = '\n'.join(line for line in added if not line.lstrip().startswith(('--', '|||')))
patterns = [r'\bbelieve_me\b', r'\bassert_total\b', r'^\s*partial\b', r'\?\w+', r'\blet\b', r'\bwith\b', r'\bdeletionTheoremProof\b', r'\bpostulate\b', r'\b[A-Za-z_]\w*@\s*[\(\[]']
prohibited = {pattern: re.findall(pattern, code, re.M) for pattern in patterns}
assert not any(prohibited.values()), prohibited
modules = re.findall(r'DGamma\.[A-Za-z0-9_.]+', source('dgamma.ipkg'))
assert len(modules) == 207
seed_root = ROOT/'build/ttc/2025081600'
assert all((seed_root/(module.replace('.', '/')+'.ttc')).exists() for module in modules)
local_ttc = seed_root/'DGamma/CP5ConfluenceLocalDiamondSpike.ttc'
assert local_ttc.stat().st_size == 125368223
local_time = datetime.datetime.fromtimestamp(local_ttc.stat().st_mtime, datetime.timezone.utc).isoformat()
assert local_time.startswith('2026-09-07T01:56:14.')
assert 'r178R174RootBirth' not in source('research-tests/DGamma/R174O17ProvisionCollisionCandidate.idr')
phases = [json.loads(line) for line in pathlib.Path('/tmp/dgamma-r178/final-phases.jsonl').read_text().splitlines()]
assert [p['phase'] for p in phases] == ['package', 'boundaries', 'legacy-seeded']
assert all(p['passed'] for p in phases)
boundaries = [json.loads(line) for line in pathlib.Path('/tmp/dgamma-r178/final-suite-ledger.jsonl').read_text().splitlines()]
final_boundaries = [r for r in boundaries if r.get('boundaryRun') == 'R178-final']
assert len(final_boundaries) == 40 and all(r['fresh'] and r['passed'] for r in final_boundaries)
report = dict(timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(), verifiedImplementationAndAuditHead=git('rev-parse', 'HEAD').strip(),
    startHead=START, branch='cp5-thm73-scoping', idrisVersion=subprocess.check_output(['idris2','--version'], text=True).strip(),
    holes=holes, holeCounts=[len(holes[p]) for p in PARTS], noNewHoles=zero_holes,
    productionDiffVs34b21c9='empty', CP3Blob='2c697e532e83989de8591fa6a4378747c6a501c0',
    LocalDiamondDiffVsStart='empty', CanonicalSortDiffVsStart='empty', protectedDeclarations=protected,
    DeletionChainOnlyChange='two comments + export of existing provenance lemma; original type/body identical',
    adjacentFullSHA256=full_sha, adjacentStatementSHA256=statement_sha, reviewSHA256=review,
    productionTTCSeeds='207/207', LocalDiamondTTC=dict(bytes=local_ttc.stat().st_size, mtimeUTC=local_time, deleted=False),
    changedIdrisFiles=changed_idris, sourceSHA256={p:sha((ROOT/p).read_bytes()) for p in changed_idris},
    prohibitedAdditions=prohibited, allChangedIdrisDefaultTotal=True, noCompiler=True, cleanTrackedTree=True,
    allowedUntrackedOnly=True, tree=git('status','--short').strip(), validationPhases=phases,
    freshFinalBoundaries=dict(positives=30, diagnosticNegatives=10, allPassed=True), aggregateR11SuiteRun='seeded, passed; not cold/fresh',
    O18Closed=True, O18BodyCommit='108846b', implicationsCommittedBeforeBody=['ff65617','dd0df9f'],
    A8='checked standalone replacement and proved scalar R174 shape; owner migration decision open',
    A9='explicit authentic ordered matching, supervisor decision under delegation, owner override pending',
    parkedC9='2/3 no-verdict cost interruptions; fully reverted/restoration checked; no packet claim',
    twoCapitalGapPreserved=True, fullPaperProofClaimed=False)
output = pathlib.Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/dgamma-r178/frozen-final.json')
assert str(output).startswith('/tmp/')
output.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
