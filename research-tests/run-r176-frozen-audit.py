#!/usr/bin/env python3
"""Read-only R176 frozen-boundary/census check; writes JSON only to requested /tmp output.
No compiler check is launched; --version is informational. Run after committing audits.
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
START = '9eaee0a'
PARTS = ['CanonicalSort', 'CrossTrace', 'DeletionChain', 'LocalDiamond', 'RenamingComposition']
PATHS = {part: 'research/DGamma/CP5Confluence' + part + 'Spike.idr' for part in PARTS}
NEW = ['research/DGamma/CP5UniqueRawNameCanonicalCapital.idr',
       'research/DGamma/CP5ConfluenceRankObservationSpike.idr']
OTHERS = ['research/DGamma/CP5ConfluenceWorkMeasureSpike.idr',
          'research/DGamma/CP5RawClosingRankSpike.idr']


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def source(path):
    return (ROOT / path).read_text()


assert git('branch', '--show-current').strip() == 'cp5-thm73-scoping'
assert not git('diff', '34b21c9', '--', 'src/', 'dgamma.ipkg')
assert git('hash-object', 'src/DGamma/CP3.idr').strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only')
assert not git('diff', '--check', START)
untracked = git('ls-files', '--others', '--exclude-standard').splitlines()
assert all(path.startswith('paper/') or path == 'review-o6-body-adversarial.md' for path in untracked)
processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
assert not re.search(r'^\s*\d+\s+\d+\s+\S*chez --program \S*/idris2_app/idris2\.so(?:\s|$)', processes, re.M)

local = (ROOT / PATHS['LocalDiamond']).read_bytes()
start = local.index(b'0 adjacentSwapSuffixSpike :')
assert sha(local[start:start + 1470]) == '2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf'
assert sha(local[start:start + 1154]) == '3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf'
old_local = git('show', START + ':' + PATHS['LocalDiamond'])
without_import = local.decode().replace('import DGamma.CP5ConfluenceRankObservationSpike\n', '', 1)
assert without_import.startswith(old_local)
addition = without_import[len(old_local):]
assert addition.count('\n0 ') == 1 and '\nexport\n0 sealedSuffixActionFoldSame :' in addition
assert 'public export' not in addition
assert git('diff', '--numstat', START, '--', PATHS['LocalDiamond']).split()[:2] == ['27', '0']

pattern = r'0 sortClosingFreeTraceSpike :.*?sortClosingFreeTraceSpike = \?sortClosingFreeTraceSpike_rhs'
old_o17 = re.search(pattern, git('show', START + ':' + PATHS['CanonicalSort']), re.S).group(0)
new_o17 = re.search(pattern, source(PATHS['CanonicalSort']), re.S).group(0)
assert old_o17 == new_o17
for part, import_line in [('CanonicalSort', 'import DGamma.CP5ConfluenceRankObservationSpike\n'),
                          ('DeletionChain', 'import DGamma.CP5UniqueRawNameInsertions\n')]:
    assert source(PATHS[part]).replace(import_line, '', 1).startswith(git('show', START + ':' + PATHS[part]))
assert 'canonicalWorkRankStepProgress' not in source(PATHS['CanonicalSort'])
review = sha((ROOT / 'review-o6-body-adversarial.md').read_bytes())
assert review == '61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8'

holes = {part: re.findall(r'\?\w+', source(PATHS[part])) for part in PARTS}
assert [len(holes[part]) for part in PARTS] == [1, 4, 0, 0, 1]
zero_holes = {path: re.findall(r'\?\w+', source(path)) for path in NEW + OTHERS}
assert not any(zero_holes.values())
modules = re.findall(r'DGamma\.[A-Za-z0-9_.]+', source('dgamma.ipkg'))
assert len(modules) == 207
seed_root = ROOT / 'build/ttc/2025081600'
assert all((seed_root / (module.replace('.', '/') + '.ttc')).exists() for module in modules)
local_ttc = seed_root / 'DGamma/CP5ConfluenceLocalDiamondSpike.ttc'
assert local_ttc.exists()
assert local_ttc.stat().st_size == 125368223
assert datetime.datetime.fromtimestamp(local_ttc.stat().st_mtime, datetime.timezone.utc).isoformat().startswith('2026-09-07T01:56:14.')

changed_idris = [path for path in git('diff', '--name-only', START, '--', 'research/', 'research-tests/DGamma/').splitlines() if path.endswith('.idr')]
assert all('%default total' in source(path) for path in changed_idris)
diff = git('diff', START, '--', 'research/', 'research-tests/DGamma/')
added = [line[1:] for line in diff.splitlines() if line.startswith('+') and not line.startswith('+++')]
code = '\n'.join(line for line in added if not line.lstrip().startswith(('--', '|||')))
patterns = [r'\bbelieve_me\b', r'\bassert_total\b', r'^\s*partial\b', r'\?\w+', r'\blet\b',
            r'\bwith\b', r'\bdeletionTheoremProof\b', r'\bpostulate\b', r'\b[A-Za-z_]\w*@\s*[\(\[]']
prohibited = {pattern: re.findall(pattern, code, re.M) for pattern in patterns}
assert not any(prohibited.values()), prohibited
assert 'rawClosingMaximumUnderUniqueInsertions' in source('THM73-PLAN.md')

report = dict(
    timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    verifiedImplementationAndAuditHead=git('rev-parse', 'HEAD').strip(), startHead=START,
    branch=git('branch', '--show-current').strip(),
    idrisVersion=subprocess.check_output(['idris2', '--version'], text=True).strip(),
    holes=holes, holeCounts=[len(holes[part]) for part in PARTS], zeroHoleResearchModules=zero_holes,
    productionDiffVs34b21c9='empty', CP3Blob='2c697e532e83989de8591fa6a4378747c6a501c0',
    LocalDiamondDiffVsStart='one import plus export 0 sealedSuffixActionFoldSame; 27 added / 0 removed',
    LocalDiamondProcessDeviation='New declaration added without required prior R167/R168 gate; independently verified and retroactively authorized by supervisor at C11 stop. Future prior-gate rule unchanged.',
    LocalDiamondSourceSHA256=sha(local), LocalDiamondOldBodyIntact=True,
    LocalDiamondTTC=dict(present=True, bytes=local_ttc.stat().st_size,
                        mtimeUTC=datetime.datetime.fromtimestamp(local_ttc.stat().st_mtime, datetime.timezone.utc).isoformat(),
                        deleted=False, refreshedOnlyAtC2=True),
    adjacentFullBytes=1470, adjacentFullSHA256=sha(local[start:start + 1470]),
    adjacentStatementBytes=1154, adjacentStatementSHA256=sha(local[start:start + 1154]),
    O17DeclarationUnchanged=True, O17DeclarationSHA256=sha(new_o17.encode()),
    reviewSHA256=review, productionTTCSeeds='207/207', noCompiler=True,
    noStagedFiles=True, noTrackedChanges=True, allowedUntrackedOnly=True,
    tree=git('status', '--short').strip(), prohibitedAdditions=prohibited,
    changedIdrisFiles=changed_idris, changedFiles=git('diff', '--name-only', START).splitlines(),
    allChangedIdrisDefaultTotal=True, C11Removed=True, C12Attempts=0,
    unitA='complete; exactly six original-unique surfaces; structural transports and boundary fixtures',
    unitB='complete; rawClosingMaximumUnderUniqueInsertions; no frozen deletion call',
    unitC='partial; C1-C10 checked; C11 3/3 stop ratified; actual strict worklist decrease remains open',
    aggregateR11SuiteRun=False, independentReviewClaimed=False)
output = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else '/tmp/dgamma-r176/frozen.json')
assert str(output).startswith('/tmp/'), 'Audit output must remain outside the source tree until copied/committed'
output.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
