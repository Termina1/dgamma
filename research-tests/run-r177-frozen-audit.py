#!/usr/bin/env python3
"""Read-only R177 census/frozen check. No proof compilation. Writes requested /tmp JSON."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
START = '86659a16b07be8225bf2269df2c155bae01491b6'
PARTS = ['CanonicalSort', 'CrossTrace', 'DeletionChain', 'LocalDiamond', 'RenamingComposition']
PATHS = {part: 'research/DGamma/CP5Confluence' + part + 'Spike.idr' for part in PARTS}
EXTRA = ['CP5CurrentGenerationBirthSpike', 'CP5ImmutableBirthMetadataSpike',
         'CP5MatchedBirthMetadataSpike', 'CP5RegistrationParentBirthSpike',
         'CP5ConfluenceWorkMeasureSpike', 'CP5UniqueRawNameCanonicalCapital',
         'CP5RawClosingRankSpike', 'CP5ConfluenceRankObservationSpike']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)

def source(path):
    return (ROOT / path).read_text()

def sha(data):
    return hashlib.sha256(data).hexdigest()

def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()

assert git('branch', '--show-current').strip() == 'cp5-thm73-scoping'
assert not git('diff', '34b21c9', '--', 'src/', 'dgamma.ipkg')
assert git('hash-object', 'src/DGamma/CP3.idr').strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only')
assert not git('diff', '--check', START)
untracked = git('ls-files', '--others', '--exclude-standard').splitlines()
assert all(path.startswith('paper/') or path == 'review-o6-body-adversarial.md' for path in untracked)
processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', processes)
for part in ['CrossTrace', 'DeletionChain', 'LocalDiamond']:
    assert not git('diff', START, '--', PATHS[part]), part
local = (ROOT / PATHS['LocalDiamond']).read_bytes()
start = local.index(b'0 adjacentSwapSuffixSpike :')
assert sha(local[start:start + 1470]) == '2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf'
assert sha(local[start:start + 1154]) == '3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf'
protected = {}
for part, declaration in [('CanonicalSort', 'sortClosingFreeTraceSpike'),
                          ('RenamingComposition', 'replayedCanonicalToOriginalEndpointSpike')]:
    pattern = r'0 ' + declaration + r' :.*?' + declaration + r'\s*=\s*\?' + declaration + r'_rhs'
    old = re.search(pattern, git('show', START + ':' + PATHS[part]), re.S).group(0)
    new = re.search(pattern, source(PATHS[part]), re.S).group(0)
    assert old == new
    protected[declaration] = dict(unchanged=True, sha256=sha(new.encode()))
review = sha((ROOT / 'review-o6-body-adversarial.md').read_bytes())
assert review == '61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8'
holes = {part: re.findall(r'\?\w+', source(PATHS[part])) for part in PARTS}
assert [len(holes[part]) for part in PARTS] == [1, 4, 0, 0, 1]
zero = {'research/DGamma/' + module + '.idr': re.findall(r'\?\w+', source('research/DGamma/' + module + '.idr')) for module in EXTRA}
assert not any(zero.values())
modules = re.findall(r'DGamma\.[A-Za-z0-9_.]+', source('dgamma.ipkg'))
assert len(modules) == 207
seed_root = ROOT / 'build/ttc/2025081600'
assert all((seed_root / (module.replace('.', '/') + '.ttc')).exists() for module in modules)
local_ttc = seed_root / 'DGamma/CP5ConfluenceLocalDiamondSpike.ttc'
assert local_ttc.exists() and local_ttc.stat().st_size == 125368223
assert datetime.datetime.fromtimestamp(local_ttc.stat().st_mtime, datetime.timezone.utc).isoformat().startswith('2026-09-07T01:56:14.')
assert not (ROOT / 'research-tests/DGamma/R177RetirementTransportProbe.idr').exists()
assert not (ROOT / 'research-tests/DGamma/R177ExactCurrentDomainProbe.idr').exists()
assert not (ROOT / 'research-tests/DGamma/R177AuthenticatedCurrentBirthProbe.idr').exists()
changed_idris = [path for path in git('diff', '--name-only', START, '--', 'research/', 'research-tests/DGamma/').splitlines() if path.endswith('.idr')]
assert all('%default total' in source(path) for path in changed_idris)
diff = git('diff', START, '--', 'research/', 'research-tests/DGamma/')
added = [line[1:] for line in diff.splitlines() if line.startswith('+') and not line.startswith('+++')]
code = '\n'.join(line for line in added if not line.lstrip().startswith(('--', '|||')))
patterns = [r'\bbelieve_me\b', r'\bassert_total\b', r'^\s*partial\b', r'\?\w+', r'\blet\b',
            r'\bwith\b', r'\bdeletionTheoremProof\b', r'\bpostulate\b', r'\b[A-Za-z_]\w*@\s*[\(\[]']
prohibited = {pattern: re.findall(pattern, code, re.M) for pattern in patterns}
assert not any(prohibited.values()), prohibited
report = dict(timestamp=now(), verifiedImplementationAndAuditHead=git('rev-parse', 'HEAD').strip(),
    startHead=START, branch=git('branch', '--show-current').strip(),
    idrisVersion=subprocess.check_output(['idris2', '--version'], text=True).strip(),
    holes=holes, holeCounts=[len(holes[part]) for part in PARTS], zeroHoleResearchModules=zero,
    productionDiffVs34b21c9='empty', CP3Blob='2c697e532e83989de8591fa6a4378747c6a501c0',
    LocalDiamondDiffVsR177Start='empty', LocalDiamondSourceSHA256=sha(local),
    CrossTraceDiffVsR177Start='empty', DeletionChainDiffVsR177Start='empty', protectedDeclarations=protected,
    adjacentFullBytes=1470, adjacentFullSHA256=sha(local[start:start + 1470]),
    adjacentStatementBytes=1154, adjacentStatementSHA256=sha(local[start:start + 1154]),
    reviewSHA256=review, productionTTCSeeds='207/207',
    LocalDiamondTTC=dict(bytes=local_ttc.stat().st_size, mtimeUTC=datetime.datetime.fromtimestamp(local_ttc.stat().st_mtime, datetime.timezone.utc).isoformat(), deleted=False),
    changedIdrisFiles=changed_idris, sourceSHA256={path:sha((ROOT/path).read_bytes()) for path in changed_idris},
    changedFiles=git('diff', '--name-only', START).splitlines(), prohibitedAdditions=prohibited,
    allChangedIdrisDefaultTotal=True, noCompiler=True, noStagedFiles=True, noTrackedChanges=True,
    allowedUntrackedOnly=True, tree=git('status', '--short').strip(), probesRemoved=True,
    O18BodyUnchanged=True, O18ClosureClaimed=False, expectedFiveHoleGateFired=False,
    O17Frontier='actual pair location and orientation applicability; root placement owner-paused',
    O18Frontier='all-supported retained-event/root coverage; retired flags and cross-endpoint support truth under A9',
    A9Finding='P1 checked non-root classification and P2-4 executable quiet unequal-support pair; both IndependentCanonicalSchedule capitals unconstructed',
    A9PendingOwnerOverride='research-side GeneratedOrchestrationMatched modulo accepted generation bijection, threaded like uniqueness; production frozen; NOT implemented',
    aggregateR11SuiteRun=False, fullPaperProofClaimed=False)
output = pathlib.Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/dgamma-r177/frozen-final.json')
assert str(output).startswith('/tmp/'), 'Read-only audit output must be outside the repository'
output.write_text(json.dumps(report, indent=2)+'\n')
print(json.dumps(report, indent=2))
