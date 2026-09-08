#!/usr/bin/env python3
"""R185 final SERIALIZED seeded validation. Launch detached, preserve all TTCs.
Includes 5 frozen spikes, current prerequisite producers, real fixtures and
2 exact diagnostic negatives; never runs the broad legacy R11 suite.
"""
import datetime
import json
import pathlib
import subprocess
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r185')
checks = [
 ['V01', 'research/DGamma/CP5ConfluenceLocalDiamondSpike.idr'],
 ['V02', 'research/DGamma/CP5ConfluenceDeletionChainSpike.idr'],
 ['V03', 'research/DGamma/CP5ConfluenceCanonicalSortSpike.idr'],
 ['V04', 'research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr'],
 ['V05', 'research/DGamma/CP5ConfluenceCrossTraceSpike.idr'],
 ['V06', 'research/DGamma/CP5O19ActualCommutedDomainSpike.idr'],
 ['V07', 'research/DGamma/CP5O19InsertObservationSpike.idr'],
 ['V08', 'research/DGamma/CP5O19ResolvedOpeningRowSpike.idr'],
 ['V09', 'research/DGamma/CP5O19ActivationInsertionRowSpike.idr'],
 ['V10', 'research/DGamma/CP5O19InsertionInsertionRowSpike.idr'],
 ['V11', 'research/DGamma/CP5O19CartesianInsertionSpike.idr'],
 ['V12', 'research/DGamma/CP5O19AdvanceObservationSpike.idr'],
 ['V13', 'research/DGamma/CP5O19ActivationResolutionSpike.idr'],
 ['V14', 'research/DGamma/CP5O20SafeBlockSelectionSpike.idr'],
 ['V15', 'research/DGamma/CP5O20BeginObservationSpike.idr'],
 ['V16', 'research/DGamma/CP5O20CanonicalPairSelectionSpike.idr'],
 ['V17', 'research/DGamma/CP5O19SourceShapeSpike.idr'],
 ['V18', 'research-tests/DGamma/R185O19ObservedInsertionRowPositive.idr'],
 ['V19', 'research-tests/DGamma/R185O19ActivationInsertionRowPositive.idr'],
 ['V20', 'research-tests/DGamma/R185O19InsertionGuardsPositive.idr'],
 ['V21', 'research-tests/DGamma/R182O19RevisedSafetyPositive.idr'],
 ['V22', 'research-tests/DGamma/R182O19RevisedSafetyNegative.idr'],
 ['V23', 'research-tests/DGamma/R182O19AdjacencyNegative.idr'],
 ['V24', 'research-tests/DGamma/R183O19GenericBeginRowPositive.idr'],
 ['V25', 'research-tests/DGamma/R182O19AllFourCrossingsPositive.idr'],
 ['V26', 'research-tests/DGamma/R7OperationalThreadingPositive.idr'],
 ['V27', 'research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr'],
 ['V28', 'research-tests/DGamma/R6SafetyDetachmentNegative.idr', 'firstPremises and secondPremises', 'detachSafetyFromCurrentState'],
 ['V29', 'research-tests/DGamma/R8ZeroDerivationOperationalStepNegative.idr', 'FiniteAdjacentSwapDerivation', 'zeroDerivationOperationalStepStillAccepted'],
 ['V30', 'research-tests/DGamma/R8FullPipeline.idr'],
 ['V31', 'package'],
]
(OUT/'final-regressions.py').write_bytes(pathlib.Path(__file__).read_bytes())
results = []
for spec in checks:
    if datetime.datetime.now(datetime.timezone.utc) >= datetime.datetime(2026, 9, 8, 3, 11, tzinfo=datetime.timezone.utc):
        raise SystemExit('NO NEW ATTEMPTS after 03:11 UTC; next was '+spec[0])
    result = subprocess.run(['python3', '-I', 'research-tests/run-r185-check.py']+spec, cwd=ROOT)
    results.append(json.loads((OUT/(spec[0]+'.json')).read_text()))
    (OUT/'final-regressions.json').write_text(json.dumps(results, indent=2)+'\n')
    if result.returncode:
        raise SystemExit('STOP at '+spec[0])
print('ALL 31 R185 FINAL REGRESSIONS PASSED', flush=True)
