#!/usr/bin/env python3
"""Seeded, serialized R178 boundary regression checks; NEVER deletes TTCs.
Run detached (python3 -I ...) and monitor the log: R8 may exceed 150 seconds.
Every target is touched to force source checking; only timestamps are changed.
"""
import datetime
import hashlib
import json
import os
import signal
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
POSITIVE = [
    'research/DGamma/CP5ConfluenceWorkMeasureSpike.idr',
    'research/DGamma/CP5ConfluenceDeletionChainSpike.idr',
    'research/DGamma/CP5ConfluenceCanonicalSortSpike.idr',
    'research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr',
    'research/DGamma/CP5ConfluenceCrossTraceSpike.idr',
    'research/DGamma/CP5UniqueRawNameCanonicalCapital.idr',
    'research/DGamma/CP5GeneratedOrchestrationMatched.idr',
    'research/DGamma/CP5CurrentGenerationBirthSpike.idr',
    'research/DGamma/CP5SupportedBirthCoverageSpike.idr',
    'research/DGamma/CP5RetirementHistorySpike.idr',
    'research/DGamma/CP5RootBirthCoverageSpike.idr',
    'research/DGamma/CP5RetiredFlagEvaluationSpike.idr',
    'research/DGamma/CP5GeneratedRetirementTransportSpike.idr',
    'research/DGamma/CP5RootOrchestrationTransportSpike.idr',
    'research/DGamma/CP5AcceptedRetirementTransportSpike.idr',
    'research/DGamma/CP5SupportEdgeInductionSpike.idr',
    'research/DGamma/CP5AllSupportedMetadataSpike.idr',
    'research/DGamma/CP5SupportClauseTransportSpike.idr',
    'research/DGamma/CP5AcceptedSupportTruthSpike.idr',
    'research/DGamma/CP5AvailabilityAwarePlacement.idr',
    'research/DGamma/CP5MatchedBirthMetadataSpike.idr',
    'research-tests/DGamma/R178GeneratedOrchestrationFixtures.idr',
    'research-tests/DGamma/R176CanonicalPermutationUniquePositive.idr',
    'research-tests/DGamma/R173UniqueRawNameInsertionsFixtures.idr',
    'research-tests/DGamma/R174O17ProvisionCollisionUnique.idr',
    'research-tests/DGamma/R174O17ProvisionCollisionCandidate.idr',
    'research-tests/DGamma/R174O17SortedProvisionGuard.idr',
    'research-tests/DGamma/R8FullPipeline.idr',
    'research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr',
    'research-tests/DGamma/R4ScannerProducerConsumers.idr',
]
NEGATIVE = [
    ('R178WrongGenerationMatchingNegative', 'wrongGenerationMatching', 'otherRenaming and sameInputs .generatedGenerationBijection'),
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
    start_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    log_path = pathlib.Path('/tmp/dgamma-r178') / ('final-suite-' + pathlib.Path(path).stem + '.log')
    maximum_rss = 0
    with log_path.open('w') as output:
        process = subprocess.Popen(command, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT, start_new_session=True)
        def stop(signum, frame):
            os.killpg(process.pid, signal.SIGTERM)
            process.wait()
            raise SystemExit(128 + signum)
        signal.signal(signal.SIGTERM, stop)
        signal.signal(signal.SIGINT, stop)
        while process.poll() is None:
            time.sleep(1)
            for row in subprocess.check_output(['ps', '-axo', 'pid,ppid,rss,command'], text=True).splitlines():
                fields = row.strip().split(None, 3)
                if len(fields) == 4 and fields[0].isdigit() and '/idris2_app/idris2' in fields[3]:
                    maximum_rss = max(maximum_rss, int(fields[2]))
                    if maximum_rss > 80 * 1024 * 1024:
                        stop(signal.SIGTERM, None)
    result = subprocess.CompletedProcess(command, process.returncode, log_path.read_text())
    print(result.stdout, flush=True)
    fresh = ('Building DGamma.' + pathlib.Path(path).stem) in result.stdout
    if diagnostic:
        passed = fresh and result.returncode != 0 and symbol in result.stdout and diagnostic in result.stdout
    else:
        passed = fresh and result.returncode == 0 and not re.search(r'^Error:', result.stdout, re.M)
    record = dict(path=path, command=' '.join(command), exit=result.returncode,
                  sourceSHA256=hashlib.sha256((ROOT/path).read_bytes()).hexdigest(), boundaryRun='R178-final',
                  seconds=time.time() - started, start=start_utc, end=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  maxSampleRSSKiB=maximum_rss, fresh=fresh, expectedDiagnostic=diagnostic, passed=passed)
    with pathlib.Path('/tmp/dgamma-r178/final-suite-ledger.jsonl').open('a') as ledger:
        ledger.write(json.dumps(record) + '\n')
    print('RESULT ' + json.dumps(record), flush=True)
    if not passed:
        raise SystemExit('Boundary regression failed; no subsequent checks launched')


if __name__ == '__main__':
    for path in POSITIVE:
        check(path)
    for module, symbol, diagnostic in NEGATIVE:
        check('research-tests/DGamma/' + module + '.idr', symbol, diagnostic)
    print(f'PASS: {len(POSITIVE)} positive fresh checks; {len(NEGATIVE)} exact diagnostic-negative fresh checks', flush=True)
