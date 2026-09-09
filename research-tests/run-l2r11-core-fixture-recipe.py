#!/usr/bin/env python3
"""L2R11 D8 compiler-free single-declaration recipe, following L2R10 recipes.
Builds ONLY the original/restored B-packet contract-level core fixture.
No split-state edge, compiler launch, git operation, lock/window access or
native evaluator normalization. Absolute lane2 paths; stdout is source text.
"""
from pathlib import Path
ROOT = Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
assert Path.cwd() == ROOT
NE='(fst fixtureDictionaries)'; KE='(snd fixtureDictionaries)'
def step(before, after, action, tag, proof):
    return f'(Fired {{before = {before}}} {{afterState = {after}}} {NE} {KE} ({action}) {tag} ({proof}))'
def trace(steps):
    result='NoTransitions'
    for item in reversed(steps):result=f'(MoreTransitions {item} {result})'
    return result
def trail(states, steps):
    result=f'(AvailabilityEnd ({states[-1]}))'
    for i in reversed(range(len(steps))):result=f'(AvailabilityStep ({states[i]}) {steps[i]} {trace(steps[i+1:])} {result})'
    return result
states=[f'smallState {i}' for i in range(5)]
steps=[step(states[i],states[i+1],action,tag,proof+' smallNativeExecution') for i,(action,tag,proof) in enumerate([
 ('LBegin 0','LBeginTag','smallBegin0'),('LAdvance 0','LFinishTag','smallFinish0'),('ORetire 1','ORetireTag','smallRetire1'),('ORemove 1','ORemoveTag','smallRemove1')])]
pre=trace(steps); pretrail=trail(states,steps)
olds=[step('contiguityState 5','contiguityState 6','OInsert 3 Root (smallComponent True)','OInsertTag','fst contiguityOriginalLast'),step('contiguityState 6','contiguityState 7','OInsert 4 Root (smallComponent False)','OInsertTag','snd contiguityOriginalLast')]
oldtail=trace(olds); oldtailtrail=trail([f'contiguityState {i}' for i in [5,6,7]],olds)
root=[step('contiguityState 0','contiguityState 11','OInsert 3 Root (smallComponent True)','OInsertTag','restoredEdge10 contiguityRestoredFirst')]
roottrace=trace(root);roottrail=trail(['contiguityState 0','contiguityState 11'],root)
newpre=f'(appendTransitions {pre} {roottrace})';newpretrail=f'(appendAvailability {pretrail} {roottrail})'
newtailsteps=[step('contiguityState 16','contiguityState 17','OInsert 4 Root (smallComponent False)','OInsertTag','restoredEdge16 contiguityRestoredLast')]
newtail=trace(newtailsteps);newtailtrail=trail(['contiguityState 16','contiguityState 17'],newtailsteps)
oldcore='(assembledTrace originalCoreNative)';oldcoretrail='(assembledTrail originalCoreNative)'
newcore='(assembledTrace restoredCoreNative)';newcoretrail='(assembledTrail restoredCoreNative)'
oldrun=f'(appendTransitions {pre} (appendTransitions {oldcore} {oldtail}))';newrun=f'(appendTransitions {newpre} (appendTransitions {newcore} {newtail}))'
oldtrail=f'(appendAvailability {pretrail} (appendAvailability {oldcoretrail} {oldtailtrail}))';newtrail=f'(appendAvailability {newpretrail} (appendAvailability {newcoretrail} {newtailtrail}))'
oldlocated=f'(MkLocatedExtendedCore (contiguityState 0) (contiguityState 5) {pre} {oldcore} {oldtail} {pretrail} {oldcoretrail} {oldtailtrail} (assembledActorOnly originalCoreNative) Refl)'
newlocated=f'(MkLocatedExtendedCore (contiguityState 11) (contiguityState 16) {newpre} {newcore} {newtail} {newpretrail} {newcoretrail} {newtailtrail} (assembledActorOnly restoredCoreNative) Refl)'
print('''||| Concrete ORIGINAL/RESTORED contract-level B-packet instance. Native
||| core traces and grammar come FROM opaque assembly. No intermediate
||| split path/edge is claimed; incompatible core endpoint states are never
||| equated. This realizes one fixed contract instance, not the universal
||| GeneralCoreContiguityRestored function for arbitrary inputs.
export
0 coreRestorationFromPackets : CoreRestorationFixture
coreRestorationFromPackets = MkCoreRestorationFixture''')
for part in [oldrun,newrun,oldtrail,newtrail,oldlocated,newlocated,'(smallSourceValid smallNativeExecution)','(\\same => absurd (injective (injective same)))','Refl','Refl','(trans (assembledWord restoredCoreNative) (sym (assembledWord originalCoreNative)))','Refl',f'(snapshotIntoExtensional {NE} (contiguityState 7) (contiguityState 17) (snd contiguityEndpoints))']:
    print('  '+part)
