#!/usr/bin/env python3
"""Pure string recipes for the one-origin control fixture (no compiler/git IO).
Imported by bounded source-writing steps; explicit native state/edge identity.
"""
EDGES = [
 ('LBegin 0','LBeginTag','smallBegin0 smallNativeExecution'),
 ('LAdvance 0','LFinishTag','smallFinish0 smallNativeExecution'),
 ('ORetire 1','ORetireTag','smallRetire1 smallNativeExecution'),
 ('ORemove 1','ORemoveTag','smallRemove1 smallNativeExecution'),
 ('OInsert 3 Root (smallComponent True)','OInsertTag','smallInsert3 smallNativeExecution'),
 ('OInsert 4 Root (smallComponent False)','OInsertTag','insertS barrierNativeExecution'),
 ('ORetire 3','ORetireTag','retireR controlNativeExecution'),
 ('ORemove 3','ORemoveTag','removeR controlNativeExecution'),
 ('LBegin 2','LBeginTag','beginControlFollowing controlNativeExecution'),
 ('LAdvance 2','LFinishTag','finishControlFollowing controlNativeExecution')]

def step(i):
 a,t,p=EDGES[i]
 return f'(Fired {{before = controlState {i}}} {{afterState = controlState {i+1}}} %search %search ({a}) {t} ({p}))'
def trace(start,end):
 s='NoTransitions'
 for i in reversed(range(start,end)):s=f'(MoreTransitions {step(i)} {s})'
 return s
def trail(start,end):
 s=f'(AvailabilityEnd (controlState {end}))'
 for i in reversed(range(start,end)):s=f'(AvailabilityStep (controlState {i}) {step(i)} _ {s})'
 return s
def installed(start,end):
 s='(InstalledEnd Refl)'
 for i in reversed(range(start,end)):
  a,t,p=EDGES[i]
  s=f'(InstalledStep {{first = controlState {i}}} {{middle = controlState {i+1}}} {{finalState = controlState {end}}} ({a}) {t} ({p}) {trace(i+1,end)} Refl {s})'
 return s
def no_life(start,end):
 s='NoLifecycleByEnd'
 for i in reversed(range(start,end)):
  s=f'(NoLifecycleByStep {step(i)} {trace(i+1,end)} (\\life, same => case same of Refl impossible) {s})'
 return s
def extended():
 return f'(ExtendedLifecycleStep {step(1)} {trace(2,4)} Refl Refl (ExtendedChildRetireStep {step(2)} {trace(3,4)} 1 (freshFiber (smallComponent True) (ChildOf 0)) Refl Refl Refl (ExtendedChildRemoveStep {step(3)} NoTransitions 1 (retireFiber (freshFiber (smallComponent True) (ChildOf 0))) Refl Refl Refl ExtendedLifecycleEnd)))'
def bundle():
 s=f'(ForcedBundleRemoveC 3 (retireFiber (freshFiber (smallComponent True) Root)) {step(7)} NoTransitions (There Here) (removeRootFound controlNativeExecution) Refl Refl ForcedBundleEndC)'
 s=f'(ForcedBundleRetireC 3 (freshFiber (smallComponent True) Root) {step(6)} {trace(7,8)} (There Here) (retireRootFound controlNativeExecution) Refl Refl {s})'
 s=f'(ForcedBundleInsertC 4 (smallComponent False) {step(5)} {trace(6,8)} Refl (EarlierForcedRoot Here) {s})'
 return f'(ForcedBundleInsertC 3 (smallComponent True) {step(4)} {trace(5,8)} Refl (KeyReleased smallRelease) {s})'
def occurrence(i,start,end):
 return f'(MkLocatedActionOccurrence (controlState {i}) (controlState {i+1}) {trace(start,i)} {step(i)} {trace(i+1,end)} Refl Refl)'

def imports(module):
 return f'''module DGamma.{module}

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
import DGamma.L2R7AttachedC
import DGamma.L2R7ControlStates
import DGamma.L2R7ControlExecution
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

'''
