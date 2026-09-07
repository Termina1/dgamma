#!/usr/bin/env python3
"""Reproduce R184's 21 SERIALIZED seeded checks; no broad R11 or cache removal.
Launch detached with python3 -I. Each target uses the unchanged 48GiB guard.
"""
import json, pathlib, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1]
checks=[
 ['V01','research/DGamma/CP5O19ActualCommutedDomainSpike.idr'],
 ['V02','research/DGamma/CP5O19InsertObservationSpike.idr'],
 ['V03','research/DGamma/CP5O20SafeBlockSelectionSpike.idr'],
 ['V04','research/DGamma/CP5O20BeginObservationSpike.idr'],
 ['V05','research/DGamma/CP5O20CanonicalPairSelectionSpike.idr'],
 ['V06','research-tests/DGamma/R182O19RevisedSafetyPositive.idr'],
 ['V07','research-tests/DGamma/R182O19RevisedSafetyNegative.idr'],
 ['V08','research-tests/DGamma/R182O19AdjacencyNegative.idr'],
 ['V09','research-tests/DGamma/R183O19GenericBeginRowPositive.idr'],
 ['V10','research-tests/DGamma/R182O19AllFourCrossingsPositive.idr'],
 ['V11','research-tests/DGamma/R7OperationalThreadingPositive.idr'],
 ['V12','research-tests/DGamma/R16ConfluenceTheoremAssemblyPositive.idr'],
 ['V13','research-tests/DGamma/R6SafetyDetachmentNegative.idr','firstPremises and secondPremises','detachSafetyFromCurrentState'],
 ['V14','research-tests/DGamma/R8ZeroDerivationOperationalStepNegative.idr','FiniteAdjacentSwapDerivation','zeroDerivationOperationalStepStillAccepted'],
 ['V15','research-tests/DGamma/R8FullPipeline.idr'],
 ['V16','research/DGamma/CP5ConfluenceCanonicalSortSpike.idr'],
 ['V17','research/DGamma/CP5ConfluenceCrossTraceSpike.idr'],
 ['V18','research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr'],
 ['V19','research/DGamma/CP5ConfluenceDeletionChainSpike.idr'],
 ['V20','research/DGamma/CP5ConfluenceLocalDiamondSpike.idr'],
 ['V21','package']]
results=[]
for spec in checks:
 r=subprocess.run(['python3','-I','research-tests/run-r184-check.py']+spec,cwd=ROOT)
 results.append(json.loads(pathlib.Path('/tmp/dgamma-r184',spec[0]+'.json').read_text()))
 pathlib.Path('/tmp/dgamma-r184/regression-results.json').write_text(json.dumps(results,indent=2)+'\n')
 if r.returncode: raise SystemExit('STOP at '+spec[0])
print('ALL 21 REGRESSIONS PASSED',flush=True)
