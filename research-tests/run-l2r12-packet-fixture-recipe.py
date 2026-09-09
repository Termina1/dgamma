#!/usr/bin/env python3
"""Compiler-free D7/D8 emitter. D7 instantiates arbitrary-family PacketPassage
with the retained native packets; D8 discharges the separate endpoint premise
from contiguityEndpoints and returns the existing full fixture contract.
Never runs a compiler, git, native split Remove, or dependency touch.
"""
from pathlib import Path
import sys
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2'); assert Path.cwd()==ROOT
p=ROOT/'research-tests/O6-L2R12-Sources/DGamma/L2R12PacketFixture.idr'
stage=sys.argv[1]
def edge(b,a,x,t,proof):return f'(Fired {{before = {b}}} {{afterState = {a}}} (fst fixtureDictionaries) (snd fixtureDictionaries) ({x}) {t} ({proof}))'
small=[('smallState '+str(i),'smallState '+str(i+1),a,t,proof+' smallNativeExecution') for i,a,t,proof in [(0,'LBegin 0','LBeginTag','smallBegin0'),(1,'LAdvance 0','LFinishTag','smallFinish0'),(2,'ORetire 1','ORetireTag','smallRetire1'),(3,'ORemove 1','ORemoveTag','smallRemove1')]]
old=[('contiguityState 5','contiguityState 6','OInsert 3 Root (smallComponent True)','OInsertTag','fst contiguityOriginalLast'),('contiguityState 6','contiguityState 7','OInsert 4 Root (smallComponent False)','OInsertTag','snd contiguityOriginalLast')]
new=[('contiguityState 16','contiguityState 17','OInsert 4 Root (smallComponent False)','OInsertTag','restoredEdge16 contiguityRestoredLast')]
def tr(es):return 'NoTransitions' if not es else '(MoreTransitions '+edge(*es[0])+' '+tr(es[1:])+')'
def trail(es,end):return '(AvailabilityEnd ('+end+'))' if not es else '(AvailabilityStep ('+es[0][0]+') '+edge(*es[0])+' '+tr(es[1:])+' '+trail(es[1:],end)+')'
header='''module DGamma.L2R12PacketFixture

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R5Extensional
import DGamma.L2R6Iteration
import DGamma.L2R8ContiguityStates
import DGamma.L2R8NativeWords
import DGamma.L2R8CoreContract
import DGamma.L2R9ContiguityPackets
import DGamma.L2R9RestoredPackets
import DGamma.L2R9ContiguityEndpoints
import DGamma.L2R9CoreRestoration
import DGamma.L2R10OrdinalData
import DGamma.L2R11OpaqueCore
import DGamma.L2R11CorePackets
import DGamma.L2R12PacketContiguity
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core

%default total
%unbound_implicits off

'''
if stage=='D7':
 assert not p.exists()
 body=f'''||| Actual old/new passage packets instantiate the ARBITRARY-family input.
||| Existing native edge packets supply every checked equation. No split
||| path and no whole endpoint relation is smuggled into this input record.
public export
fixturePacketPassage : PacketPassage contiguityState (\\ordinal => contiguityState (11 + ordinal))
  (smallState 0) (contiguityState 7) (contiguityState 17)
fixturePacketPassage = MkPacketPassage originalCorePacket restoredCorePacket
  {tr(small)}
  {trail(small,'smallState 4')}
  3 (smallComponent True) (restoredEdge10 contiguityRestoredFirst)
  {tr(old)}
  {trail(old,'contiguityState 7')}
  {tr(new)}
  {trail(new,'contiguityState 17')}
  [OInsert 4 Root (smallComponent False)] Refl Refl
  (smallSourceValid smallNativeExecution)
  (\\same => SIsNotZ {{x = 0}} (cong pred (cong pred same)))
'''
 p.write_text(header+body)
elif stage=='D8':
 result='(coreContiguityFromPackets contiguityState (\\ordinal => contiguityState (11 + ordinal)) fixturePacketPassage (snapshotIntoExtensional (fst fixtureDictionaries) (contiguityState 7) (contiguityState 17) (snd contiguityEndpoints)))'
 body='''\n||| Fixed full CoreRestorationFixture FROM the NEW arbitrary-family consumer.
||| Its explicit endpoint premise is DISCHARGED by checked contiguityEndpoints;
||| the other facts come from packet assembly. No native split edge is used.
export
0 coreRestorationViaGeneralPackets : CoreRestorationFixture
coreRestorationViaGeneralPackets = MkCoreRestorationFixture\n'''
 for field in ['packetOriginalRun','packetRestoredRun','packetOriginalTrail','packetRestoredTrail','packetOriginalCore','packetRestoredCore','packetOriginValid','packetRootForeign','packetOriginalSuffix','packetRestoredWord','packetCoreWord','packetCorePosition','packetWholeEndpoints']:
  body+='  ('+field+' '+result+')\n'
 with p.open('a') as f:f.write(body)
else:raise SystemExit('D7 or D8 required')
print(stage,p)
