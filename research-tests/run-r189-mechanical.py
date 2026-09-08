#!/usr/bin/env python3
"""ONE ratified byte-identical declaration move/import switch per fresh check.
Launch detached with python3 -I; owns edit -> serial guarded check -> guarded
commit in one exception-stopping process. No proof text is ever repaired here.
Usage: run-r189-mechanical.py M1-1 (through M27-1), or I1-1 (through I16-1).
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r189')
START = '8e133ed5'
CROSS = 'research/DGamma/CP5ConfluenceCrossTraceSpike.idr'
SURFACE = 'research/DGamma/CP5O19SurfaceSpike.idr'
NAMES = ['AdjacentActorOrderSwap', 'ActorBlockDecomposition', 'NoGeneratedChild',
 'generatedChildAtHeadContradictsSafety', 'AdjacentActorSwapSafety', 'actorBlockTrace',
 'actorBlockTransitionCount', 'successorEqualityInjective', 'addLeftInjective',
 'SelectedBlockCoordinateInjectivity', 'selectedBlockCoordinateInjectivity',
 'NodeCrossesSourceBlockPosition', 'transitionPrefixLength', 'adjacentLeftNodeOccurrence',
 'adjacentRightNodeOccurrence', 'leftNodeSourceBlockLabel', 'rightNodeSourceBlockLabel',
 'DerivationCrossesBlockPositions', 'BlockCrossingOriginPlan', 'foldBlockCrossingOriginPlan',
 'WholeBlockSwapDerivation', 'blockCrossingLabels', 'wholeSelectedCoordinateAliasImpossible',
 'wholeBlockFiniteDerivation', 'OperationalAdjacentBlockSwap', 'blockSwapReplayCorrespondence',
 'blockSwapOccurrenceCorrespondence']
HELPERS = ['BodyMetadata', 'OrdinalPlan', 'CartesianSitePlan', 'PairObservation',
 'MixedActivationRow', 'MixedRowDispatcher', 'CartesianWordRow', 'CartesianColumns',
 'OriginalBlockClass', 'PaperBranchCompleteness', 'ActualCartesian', 'WholeBlock',
 'SameChainAssembly', 'ReachedBlocks', 'ReachedDecomposition', 'OperationalAssembly']
LOWER_IMPORT = b'import public DGamma.CP5O19SurfaceSpike\n'
OLD_IMPORT = b'import DGamma.CP5ConfluenceCrossTraceSpike\n'
NEW_IMPORT = b'import DGamma.CP5O19SurfaceSpike\n'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def no_compiler():
    assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)), 'Reconcile compiler/orphan first'
def chunks():
    original = git('show', START+':'+CROSS)
    positions = list(re.finditer(rb'(?m)^(?:\|\|\|[^\n]*\n)*public export\n(?:[01] )?(?:(?:record|data) )?([A-Za-z_]\w*)\s*(?=[:\n (])', original))
    spans = {m[1].decode():(m.start(), positions[i+1].start() if i+1 < len(positions) else len(original)) for i,m in enumerate(positions)}
    selected = {name:original[slice(*spans[name])] for name in NAMES}
    header = original[:positions[0].start()].replace(b'module DGamma.CP5ConfluenceCrossTraceSpike', b'module DGamma.CP5O19SurfaceSpike')
    return original, spans, selected, header

def expected_move(count):
    original, spans, selected, header = chunks()
    cross = original
    for name in NAMES[:count]:
        assert cross.count(selected[name]) == 1
        cross = cross.replace(selected[name], b'', 1)
    if count:
        cross = cross.replace(b'\n\nimport DGamma.Core', b'\n\n'+LOWER_IMPORT+b'import DGamma.Core', 1)
    return cross, header+b''.join(selected[n] for n in NAMES[:count])

unit = sys.argv[1]
match = re.fullmatch(r'([MI])(\d+)-(\d+)', unit)
assert match and match[3] == '1', 'Mechanical rejection requires a gate, no automatic retry/repair'
kind, number = match[1], int(match[2])
assert datetime.datetime.now(datetime.timezone.utc) < datetime.datetime(2026,9,8,15,9,50,tzinfo=datetime.timezone.utc)
assert git('branch','--show-current').decode().strip() == 'cp5-thm73-scoping'
assert not git('diff','--name-only').strip() and not git('diff','--cached','--name-only').strip()
assert all(p.startswith('paper/') or p == 'review-o6-body-adversarial.md' for p in git('ls-files','--others','--exclude-standard').decode().splitlines())
no_compiler()
head = git('rev-parse','HEAD').decode().strip()
original, spans, selected, header = chunks()
if kind == 'M':
    assert 1 <= number <= len(NAMES)
    before_cross, before_surface = expected_move(number-1)
    assert (ROOT/CROSS).read_bytes() == before_cross
    assert (ROOT/SURFACE).read_bytes() == before_surface if number>1 else not (ROOT/SURFACE).exists()
    after_cross, after_surface = expected_move(number)
    expected = {CROSS:after_cross, SURFACE:after_surface}
    target = CROSS
    name = NAMES[number-1]
    metadata = dict(kind='declaration move',declaration=name,byteCount=len(selected[name]),declarationSHA256=sha(selected[name]),oldLines=[original[:spans[name][0]].count(b'\n')+1, original[:spans[name][1]].count(b'\n')],newStartLine=after_surface[:after_surface.index(selected[name])].count(b'\n')+1)
else:
    assert 1 <= number <= len(HELPERS)
    assert (ROOT/CROSS).read_bytes() == expected_move(len(NAMES))[0]
    assert (ROOT/SURFACE).read_bytes() == expected_move(len(NAMES))[1]
    target = 'research/DGamma/CP5O19'+HELPERS[number-1]+'Spike.idr'
    old = (ROOT/target).read_bytes()
    assert old.count(OLD_IMPORT) == 1 and NEW_IMPORT not in old
    expected = {target:old.replace(OLD_IMPORT, NEW_IMPORT, 1)}
    metadata = dict(kind='helper import switch',helper=target,oldSHA256=sha(old))
assert not (OUT/(unit+'.mechanical.json')).exists()
for path,data in expected.items():
    (ROOT/path).write_bytes(data)
    (OUT/(unit+'.'+pathlib.Path(path).name+'.source')).write_bytes(data)
metadata.update(unit=unit,priorCommit=head,target=target,sourceHashes={p:sha(b) for p,b in expected.items()},preparedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat())
(OUT/(unit+'.mechanical.json')).write_text(json.dumps(metadata,indent=2)+'\n')
print('PREPARED',json.dumps(metadata),flush=True)
with (OUT/(unit+'.check-monitor')).open('w') as monitor:
    checked = subprocess.run(['python3','-I',str(ROOT/'research-tests/run-r189-check.py'),unit,target],cwd=ROOT,stdout=monitor,stderr=subprocess.STDOUT)
record = json.loads((OUT/(unit+'.json')).read_text())
assert checked.returncode == 0 and record['passed'] and record['fresh'] and record['exit'] == 0 and not record['interrupted'], 'STOP: failed byte-identical move; gate before any repair except missing imports'
assert record['expectedDiagnostic'] is None
assert record['sourceSHA256'] == sha(expected[target])
if kind == 'M':
    assert re.search(r'^\d+/\d+: Building DGamma\.CP5O19SurfaceSpike \('+re.escape(SURFACE)+r'\)$',record['transcript'],re.M), 'Lower surface must freshly build too'
assert json.loads((OUT/'ledger.jsonl').read_text().splitlines()[-1])['unit'] == unit
assert git('rev-parse','HEAD').decode().strip() == head
assert not git('diff','--cached','--name-only').strip()
assert set(git('diff','--name-only').decode().splitlines()).issubset(expected)
for path,data in expected.items():
    assert (ROOT/path).read_bytes() == data
assert not git('diff','34b21c9','--','src/','dgamma.ipkg').strip()
assert not git('diff',START,'--','research/DGamma/CP5ConfluenceLocalDiamondSpike.idr').strip()
no_compiler()
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',*expected],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m','refactor(o19): '+(NAMES[number-1]+' byte-identical type rehome' if kind=='M' else HELPERS[number-1]+' lower-surface import')+' (R189 '+unit+')'],cwd=ROOT,check=True)
assert not git('diff','--cached','--name-only').strip()
receipt = dict(event='GUARDED MECHANICAL COMMIT',unit=kind+str(number),attempt=match[3],invocation=unit,sourceHash=record['sourceSHA256'],sourceHashes=metadata['sourceHashes'],resultingCommitHash=git('rev-parse','HEAD').decode().strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),mechanical=metadata,guardChecksPassed=['fresh PASS','exit 0','not interrupted','no expected diagnostic','exact source SHA256','all moved source hashes','one byte-identical declaration move or one exact helper import switch','no intervening compiler invocation','no pre-staged files','no compiler','production freeze','LocalDiamond unchanged','git diff --check','git commit success','no post-staged files'])
with (OUT/'commit-receipts.jsonl').open('a') as ledger:
    ledger.write(json.dumps(receipt)+'\n')
print('GUARDED MECHANICAL COMMIT',json.dumps(receipt),flush=True)
