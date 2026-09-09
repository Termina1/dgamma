#!/usr/bin/env python3
"""Compiler-free D6 single-declaration emitter for the supervisor-authorized
arbitrary-state packet consumer. Endpoint equivalence remains EXPLICIT INPUT.
No compiler, git, dependency touch, or source mutation during checks.
"""
from pathlib import Path
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
assert Path.cwd()==ROOT
p=ROOT/'research-tests/O6-L2R12-Sources/DGamma/L2R12PacketContiguity.idr'
assert 'coreContiguityFromPackets :' not in p.read_text()
old='(assembleCoreNative oldStates (passageOldPacket passage))'
new='(assembleCoreNative newStates (passageNewPacket passage))'
before='(passagePrefix passage)';bt='(passagePrefixTrail passage)'
after='(passageOldSuffix passage)';at='(passageOldSuffixTrail passage)'
newafter='(passageNewSuffix passage)';nt='(passageNewSuffixTrail passage)'
root='(OInsert (passageRoot passage) Root (passageComponent passage))'
edge=f'(Fired {{before = oldStates 0}} {{afterState = newStates 0}} (fst fixtureDictionaries) (snd fixtureDictionaries) {root} OInsertTag (passageEarlyRoot passage))'
roottrace=f'(MoreTransitions {edge} NoTransitions)'
roottrail=f'(AvailabilityStep (oldStates 0) {edge} NoTransitions (AvailabilityEnd (newStates 0)))'
nb=f'(appendTransitions {before} {roottrace})';nbt=f'(appendAvailability {bt} {roottrail})'
ot=f'(assembledTrail {old})';newt=f'(assembledTrail {new})'
oldrun=f'(appendTransitions {before} (appendTransitions (assembledTrace {old}) {after}))'
newrun=f'(appendTransitions {nb} (appendTransitions (assembledTrace {new}) {newafter}))'
oldtrail=f'(appendAvailability {bt} (appendAvailability {ot} {at}))'
newtrail=f'(appendAvailability {nbt} (appendAvailability {newt} {nt}))'
coreEq=f'(fst (packetCoreWords oldStates newStates (passageOldPacket passage) (passageNewPacket passage)))'
wordproof=f'''(trans (nativeWordAppend {nbt} (appendAvailability {newt} {nt}))
    (trans (cong2 (++) (nativeWordAppend {bt} {roottrail})
      (trans (nativeWordAppend {newt} {nt})
        (cong2 (++) {coreEq} (passageNewAfterWord passage))))
      (sym (appendAssociative (nativeActionWord {bt}) [{root}]
        (nativeActionWord {ot} ++ passageSuffixWord passage)))))'''
body=f'''\n||| CONDITIONAL general packet route, per explicit supervisor ruling(A).
||| Original/restored state families and all surrounding traces are arbitrary.
||| Core grammar, location, ACTION-WORD equality, count5 and +1 placement are
||| PRODUCED. Whole endpoints are deliberately a SEPARATE EXPLICIT PREMISE;
||| deriving that premise from native passage squares is the L2R13 residue.
export
0 coreContiguityFromPackets :
  (oldStates, newStates : Nat -> SystemState Nat Bool (\\key => Unit) Unit String) ->
  {{initial, oldFinal, newFinal : SystemState Nat Bool (\\key => Unit) Unit String}} ->
  (passage : PacketPassage oldStates newStates initial oldFinal newFinal) ->
  (0 endpoints : RegistryExtensional Nat Bool Unit String (\\key => Unit)
    (fst fixtureDictionaries) oldFinal newFinal) ->
  PacketContiguityResult initial oldFinal newFinal
    (passageRoot passage) (passageComponent passage) (passageSuffixWord passage)
coreContiguityFromPackets oldStates newStates passage endpoints = MkPacketContiguityResult
  {oldrun}
  {newrun}
  {oldtrail}
  {newtrail}
  (locatePacketCore oldStates (passageOldPacket passage) {before} {after} {bt} {at})
  (locatePacketCore newStates (passageNewPacket passage) {nb} {newafter} {nbt} {nt})
  (passageSourceValid passage) (passageForeign passage) (passageOldAfterWord passage)
  {wordproof}
  {coreEq}
  (assembledCount {old}) (assembledCount {new})
  (packetPrefixShift {before} {edge}) endpoints
'''
with p.open('a') as f:f.write(body)
print(p)
