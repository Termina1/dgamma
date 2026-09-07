#!/usr/bin/env python3
"""Seeded, serialized R176 boundary regression checks; NEVER deletes TTCs.
Run detached (python3 -I ...) and monitor the log: R8 may exceed 150 seconds.
Every target is touched to force source checking; only timestamps are changed.
"""
import json
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
POSITIVE = [
    'research/DGamma/CP5ConfluenceCanonicalSortSpike.idr',
    'research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr',
    'research/DGamma/CP5ConfluenceCrossTraceSpike.idr',
    'research/DGamma/CP5UniqueRawNameCanonicalCapital.idr',
    'research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr',
    'research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr',
    'research-tests/DGamma/R174O17ProvisionCollisionUnique.idr',
    'research-tests/DGamma/R8FullPipeline.idr',
    'research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr',
    'research-tests/DGamma/R4ScannerProducerConsumers.idr',
]
NEGATIVE = [
    ('R176BareCapitalFreshnessNegative', 'bareCapitalCannotSupplyFreshness', 'Mismatch between: TraceIndependent'),
    ('R176WrongOriginalTraceUniqueNegative', 'wrongOriginalTraceFreshness', 'Mismatch between: otherTrace and leftTrace.'),
    ('R176UnsealedOriginUniqueNegative', 'unsealedOriginCannotTransportUnique', 'Mismatch between: ActionRegistrationReplayCorrespondence'),
    ('R176ReductionUniqueDirectionNegative', 'reductionUniqueCannotRunBackward', 'reduction .reducedFinal and originalFinal'),
    ('R6OldPollutionNegative', 'oldPollutionReachesO20', 'Mismatch between: CertifiedActorPermutation'),
    ('R6MixedScheduleNegative', 'mixedLeftSchedule', 'Mismatch between: leftCapital and otherLeft.'),
    ('R8WrongTraceBridgeNegative', 'wrongTraceBridge', 'operationalTargetFinal and otherFinal'),
    ('R8WrongOccurrenceBridgeNegative', 'detachBridgeOccurrenceRelation', 'first and second'),
    ('R11BridgeWrongGenerationNegative', 'arbitraryRightBirthCannotSatisfyBridgeGeneration', 'generatedGenerationBijection sameInputs'),
]


def check(path, symbol=None, diagnostic=None):
    processes = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
    if re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', processes, re.M):
        raise RuntimeError('Existing compiler: reconcile orphan before another check')
    (ROOT / path).touch()
    command = ['idris2', '--source-dir', 'src', '--source-dir', 'research']
    if path.startswith('research-tests/'):
        command += ['--source-dir', 'research-tests']
    command += ['--check', path]
    print('START ' + ' '.join(command), flush=True)
    started = time.time()
    result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, flush=True)
    fresh = ('Building DGamma.' + pathlib.Path(path).stem) in result.stdout
    if diagnostic:
        passed = fresh and result.returncode != 0 and symbol in result.stdout and diagnostic in result.stdout
    else:
        passed = fresh and result.returncode == 0 and not re.search(r'^Error:', result.stdout, re.M)
    record = dict(path=path, command=' '.join(command), exit=result.returncode,
                  seconds=time.time() - started, fresh=fresh, expectedDiagnostic=diagnostic, passed=passed)
    print('RESULT ' + json.dumps(record), flush=True)
    if not passed:
        raise SystemExit('Boundary regression failed; no subsequent checks launched')


if __name__ == '__main__':
    for path in POSITIVE:
        check(path)
    for module, symbol, diagnostic in NEGATIVE:
        check('research-tests/DGamma/' + module + '.idr', symbol, diagnostic)
    print('PASS: 10 positive fresh checks; 9 exact diagnostic-negative fresh checks', flush=True)
