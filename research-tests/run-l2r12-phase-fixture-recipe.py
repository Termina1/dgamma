#!/usr/bin/env python3
"""Compiler-free L2R12 fixture source emitter. Writes exactly one requested
new declaration; never checks, commits, touches dependencies or runs a shell.
A9 emits public actual fragment data, later stages append native certificates.
"""
from pathlib import Path
import sys
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
target=ROOT/'research-tests/O6-L2R12-Sources/DGamma/L2R12PhaseNativeFixtures.idr'
assert Path.cwd()==ROOT
stage=sys.argv[1]
small=[('smallState '+str(i),'smallState '+str(i+1),a,t,'('+p+' smallNativeExecution)') for i,a,t,p in [(0,'LBegin 0','LBeginTag','smallBegin0'),(1,'LAdvance 0','LFinishTag','smallFinish0'),(2,'ORetire 1','ORetireTag','smallRetire1'),(3,'ORemove 1','ORemoveTag','smallRemove1'),(4,'OInsert 3 Root (smallComponent True)','OInsertTag','smallInsert3'),(5,'LBegin 2','LBeginTag','smallBegin2'),(6,'LAdvance 2','LFinishTag','smallFinish2')]]
barrier=small[:5]+[('barrierState '+str(i),'barrierState '+str(i+1),a,t,'('+p+' barrierNativeExecution)') for i,a,t,p in [(5,'OInsert 4 Root (smallComponent False)','OInsertTag','insertS'),(6,'LBegin 2','LBeginTag','beginFollowing'),(7,'LAdvance 2','LFinishTag','finishFollowing')]]
def edge(e):
 b,a,x,t,p=e
 return f'(Fired {{before = {b}}} {{afterState = {a}}} (fst fixtureDictionaries) (snd fixtureDictionaries) ({x}) {t} {p})'
def trace(es):
 if not es:return 'NoTransitions'
 return '(MoreTransitions '+edge(es[0])+' '+trace(es[1:])+')'
def trail(es,end):
 if not es:return '(AvailabilityEnd ('+end+'))'
 return '(AvailabilityStep ('+es[0][0]+') '+edge(es[0])+' '+trace(es[1:])+' '+trail(es[1:],end)+')'
imports='''module DGamma.L2R12PhaseNativeFixtures

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6Phase
import DGamma.L2R7CatalogBirth
import DGamma.L2R9OrdinalTrails
import DGamma.L2R10OrdinalData
import DGamma.L2R10PhaseScan
import DGamma.L2R11PhaseDecode
import DGamma.L2R8CoreContract
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

'''
if stage=='A9':
 assert not target.exists()
 body='''||| Authentic Finish0/Retire1/Remove1 fragment and its source-aware trail.
||| Data only: no phase, ownership or interval property is assumed.
public export
phaseFixtureCore : (core : Transitions (smallState 1) (smallState 4) **
  AvailabilityTrace Nat Bool Unit String (\\key => Unit) core)
phaseFixtureCore = ('''+trace(small[1:4])+' ** '+trail(small[1:4],'smallState 4')+')\n'
 target.write_text(imports+body)
elif stage=='A10':
 body='''\n||| The actual lifecycle head of the public three-edge native fragment.
export
0 phaseFixtureLife : LocatedActionOccurrence (LAdvance 0) (fst phaseFixtureCore)
phaseFixtureLife = MkLocatedActionOccurrence (smallState 1) (smallState 2)
  NoTransitions '''+edge(small[1])+' '+trace(small[2:4])+' Refl Refl\n'
 with target.open('a') as f:f.write(body)
elif stage in ['A11','A12','A13']:
 name={'A11':'singleForcedPhaseDecoded','A12':'barrierRootPhaseDecoded','A13':'barrierSuccessorPhaseDecoded'}[stage]
 es=small if stage=='A11' else barrier
 entry='MkRootCatalogEntry '+('5 4 (smallComponent False)' if stage=='A13' else '4 3 (smallComponent True)')
 native='fst ordinalFixtureTrails' if stage=='A11' else 'snd ordinalFixtureTrails'
 le='(LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))'
 body=f'''\n||| Concrete ForcedRootPhase FROM native fragment, release and phase owner
||| decoder. Every seed/anchor/count fact computes on explicit fixture data.
||| This is a fixed certificate, not the general acceptance-to-phase producer.
export
0 {name} : ForcedRootPhase Nat Bool Unit String (\\key => Unit)
  (fst fixtureDictionaries) (snd fixtureDictionaries) ({native}) ({entry})
{name} = MkForcedRootPhase
  (MkRootCatalogEntry 4 3 (smallComponent True)) Here {le} Refl
  0 (smallState 1) (smallState 4)
  {trace(small[:1])} (fst phaseFixtureCore) {trace(es[4:])}
  (phaseEventsExtended (fst fixtureDictionaries) 0 (snd phaseFixtureCore)
    [Refl, Refl, Refl]) Refl
  smallRelease (LAdvance 0) phaseFixtureLife True Refl Refl
  (phaseLifeOwnerDecoded (fst fixtureDictionaries) 0 (smallState 1) (LAdvance 0) Refl Refl)
  (LTESucc LTEZero) Refl Refl {le}
'''
 with target.open('a') as f:f.write(body)
else:raise SystemExit('Unsupported one-declaration stage')
print(stage,target)
