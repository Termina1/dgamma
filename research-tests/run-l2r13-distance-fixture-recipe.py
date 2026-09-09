#!/usr/bin/env python3
"""L2R13 B12 one-declaration fixture recipe, absolute lane-owned source only.
Constructs prefixes from native edges, NEVER projects prior hand-built moves.
No compiler or commit operations.
"""
from pathlib import Path
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
p=ROOT/'research-tests/O6-L2R13-Sources/DGamma/L2R13DistanceFixtures.idr'
assert Path.cwd()==ROOT
ne='(fst fixtureDictionaries)';ke='(snd fixtureDictionaries)'
def edge(a,b,act,tag,proof):
 return f'(Fired {{before = smallState {a}}} {{afterState = smallState {b}}} {ne} {ke} ({act}) {tag} ({proof}))'
e1=edge(0,1,'LBegin 0','LBeginTag','smallBegin0 smallNativeExecution');e2=edge(1,2,'LAdvance 0','LFinishTag','smallFinish0 smallNativeExecution');e3=edge(2,3,'ORetire 1','ORetireTag','smallRetire1 smallNativeExecution');e4=edge(3,4,'ORemove 1','ORemoveTag','smallRemove1 smallNativeExecution');e5=edge(4,5,'OInsert 3 Root (smallComponent True)','OInsertTag','smallInsert3 smallNativeExecution')
pre='(MoreTransitions '+e1+' (MoreTransitions '+e2+' (MoreTransitions '+e3+' (MoreTransitions '+e4+' NoTransitions))))'
pres='(MoreTransitions '+e1+' (MoreTransitions '+e2+' (MoreTransitions '+e3+' (MoreTransitions '+e4+' (MoreTransitions '+e5+' NoTransitions)))))'
tr='(appendAvailability (nativePairTrail '+ne+' '+ke+' (smallState 0) (smallState 1) (smallState 2) (LBegin 0) (LAdvance 0) LBeginTag LFinishTag (smallBegin0 smallNativeExecution) (smallFinish0 smallNativeExecution)) (nativePairTrail '+ne+' '+ke+' (smallState 2) (smallState 3) (smallState 4) (ORetire 1) (ORemove 1) ORetireTag ORemoveTag (smallRetire1 smallNativeExecution) (smallRemove1 smallNativeExecution)))'
trs='(appendAvailability '+tr+' (AvailabilityStep (smallState 4) '+e5+' NoTransitions (AvailabilityEnd (smallState 5))))'
bound4='(LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))';bound5='(LTESucc '+bound4+')'
s=f'''
||| D8 single 1->0 and the bundle's terminal 1->0 move FROM the general
||| terminal-square producer. Native prefixes, forcing and scan frames compute;
||| no singleAdmitted/secondBundleAdmitted field of iterationFixtures is used.
public export
0 terminalFixtureMoves :
  (AdmittedDistanceMove Nat Bool Unit String (\\key => Unit) {ne} {ke}
    (singleBeforeTrail iterationFixtures) (singleAfterTrail iterationFixtures),
   AdmittedDistanceMove Nat Bool Unit String (\\key => Unit) {ne} {ke}
    (bundleMiddleTrail iterationFixtures) (bundleAfterTrail iterationFixtures))
terminalFixtureMoves =
  (terminalSquareAdmittedMove {ne} {ke} 3 (smallComponent True)
    (smallState 4) (smallState 8) (smallState 9) (LBegin 2) LBeginTag {pre} {tr}
    (smallEarlyBegin2 smallNativeExecution) (smallLateInsert3 smallNativeExecution)
    (fst distanceFixtureSquares) (KeyForces Here Refl) 4 0 {bound4} Refl Refl,
   terminalSquareAdmittedMove {ne} {ke} 4 (smallComponent False)
    (smallState 5) (smallState 6) (bundlePhaseState 6) (LBegin 2) LBeginTag {pres} {trs}
    (smallBegin2 smallNativeExecution) (sAfterRBegin bundlePhaseNative)
    (snd distanceFixtureSquares)
    (OrderForces (KeyForces Here Refl) (There Here) {bound5}) 5 0 {bound5} Refl Refl)
'''
assert '0 terminalFixtureMoves :' not in p.read_text()
p.write_text(p.read_text()+s)
