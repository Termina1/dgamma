#!/usr/bin/env python3
"""Gated single O19 body attempt AFTER committed, freshly validated A/B/C.
Launch detached with Python -I. Failure restores exact committed source and
stops for supervisor; no automated proof/body repair or retry.
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path('/tmp/dgamma-r189')
CROSS='research/DGamma/CP5ConfluenceCrossTraceSpike.idr'
START='8e133ed5'
unit=sys.argv[1]
assert unit=='O19-1', 'Only the initial gated body attempt is authorized'
def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(data):
    return hashlib.sha256(data).hexdigest()
def no_compiler():
    assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True))
def signature(data):
    start=data.index(b'0 operationalAdjacentBlockSwapSpike :')
    return data[start:data.index(b'\noperationalAdjacentBlockSwapSpike ',start)]
assert datetime.datetime.now(datetime.timezone.utc)<datetime.datetime(2026,9,8,15,9,50,tzinfo=datetime.timezone.utc)
assert git('branch','--show-current').decode().strip()=='cp5-thm73-scoping'
assert not git('diff','--name-only').strip() and not git('diff','--cached','--name-only').strip()
assert all(p.startswith('paper/') or p=='review-o6-body-adversarial.md' for p in git('ls-files','--others','--exclude-standard').decode().splitlines())
no_compiler()
assert not (OUT/(unit+'.json')).exists() and not (OUT/(unit+'.body.json')).exists()
receipts=[json.loads(line) for line in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
mechanical=[r for r in receipts if r['event']=='GUARDED MECHANICAL COMMIT']
assert len(mechanical)==52
assert {r['unit'] for r in mechanical}=={'M'+str(i) for i in range(1,33)}|{'I'+str(i) for i in range(1,20)}|{'W1'}
proofs=[r for r in receipts if r['event']=='GUARDED COMMIT']
assert {r['unit'] for r in proofs}=={'A'+str(i) for i in range(1,10)}|{'B'+str(i) for i in range(2,8)}
assert not [r for r in receipts if r['event']=='GUARDED BODY COMMIT']
plan=json.loads((OUT/'prebody-validation-plan.json').read_text())
complete=json.loads((OUT/'prebody-validation-complete.json').read_text())
assert len(plan)==62 and complete['serial'] and complete['invocations']==[item['unit'] for item in plan]
for item in plan:
    record=json.loads((OUT/(item['unit']+'.json')).read_text())
    assert record['passed'] and record['fresh'] and not record['interrupted']
    assert record['path']==item['path'] and record['expectedDiagnostic']==item['expectedDiagnostic']
    path='dgamma.ipkg' if item['path']=='package' else item['path']
    assert sha((ROOT/path).read_bytes())==record['sourceSHA256']
assert json.loads((OUT/'C-transitive-cycle-audit.json').read_text())['CrossTraceImportEdges']==[]
with (OUT/'O19-before-body-frozen.monitor').open('w') as log:
    subprocess.run(['python3','-I',str(ROOT/'research-tests/run-r189-frozen-audit.py'),str(OUT/'O19-before-body-frozen.json')],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
frozen=json.loads((OUT/'O19-before-body-frozen.json').read_text())
assert frozen['split']==[1,3,0,0,1] and not frozen['O19Closed']
head=git('rev-parse','HEAD').decode().strip()
old=(ROOT/CROSS).read_bytes()
assert signature(old)==signature(git('show',START+':'+CROSS))
hole=b'operationalAdjacentBlockSwapSpike = ?operationalAdjacentBlockSwapSpike_rhs'
body=b'operationalAdjacentBlockSwapSpike nameEq keyEq protocol orderSwap sourceTrace sourceBlocks sourcePremises sourceUnique applicableSafety =\n  o19ActualOperationalBlockSwap nameEq keyEq protocol orderSwap sourceTrace sourceBlocks sourcePremises applicableSafety sourceUnique'
anchor=b'import public DGamma.CP5O19SurfaceSpike\n'
extra=b'import DGamma.CP5O19OperationalAssemblySpike\n'
assert old.count(hole)==1 and old.count(anchor)==1 and extra not in old
new=old.replace(anchor,anchor+extra,1).replace(hole,body,1)
assert signature(new)==signature(old)
assert not re.search(rb'\b(?:with|prefix|let|believe_me|assert_total|partial|postulate)\b|\?\w+',body)
metadata=dict(unit=unit,priorCommit=head,target=CROSS,oldSHA256=sha(old),sourceSHA256=sha(new),signatureSHA256=sha(signature(old)),prerequisiteValidations=[p['unit'] for p in plan],mechanicalCommits=len(mechanical),bodyChangeOnly=True,preparedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat())
(OUT/(unit+'.body.json')).write_text(json.dumps(metadata,indent=2)+'\n')
(OUT/(unit+'.before.source')).write_bytes(old)
(ROOT/CROSS).write_bytes(new)
with (OUT/(unit+'.check-monitor')).open('w') as log:
    checked=subprocess.run(['python3','-I',str(ROOT/'research-tests/run-r189-check.py'),unit,CROSS],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
record=json.loads((OUT/(unit+'.json')).read_text())
if not (checked.returncode==0 and record['passed'] and record['fresh'] and record['exit']==0 and not record['interrupted'] and record['expectedDiagnostic'] is None):
    no_compiler()
    assert (ROOT/CROSS).read_bytes()==new
    (ROOT/CROSS).write_bytes(old)
    (OUT/(unit+'.rollback.json')).write_text(json.dumps(dict(event='BODY FAILURE STOP/FULL REVERT',restoredCommit=head,rejectedSHA256=sha(new),restoredSHA256=sha(old),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
    raise SystemExit('STOP/GATE: rejected body retained in snapshots, committed source fully restored')
assert record['sourceSHA256']==sha(new)
assert json.loads((OUT/'ledger.jsonl').read_text().splitlines()[-1])['unit']==unit
assert git('rev-parse','HEAD').decode().strip()==head
assert not git('diff','--cached','--name-only').strip()
assert git('diff','--name-only').decode().splitlines()==[CROSS]
assert (ROOT/CROSS).read_bytes()==new
assert not git('diff','34b21c9','--','src/','dgamma.ipkg').strip()
assert not git('diff',START,'--','research/DGamma/CP5ConfluenceLocalDiamondSpike.idr').strip()
assert not git('diff','--check').strip()
no_compiler()
subprocess.run(['git','add','--',CROSS],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m','proof(o19): assemble exact actual operational block swap after A/B/C gates (R189 O19-1)'],cwd=ROOT,check=True)
assert not git('diff','--cached','--name-only').strip()
receipt=dict(event='GUARDED BODY COMMIT',unit='O19',attempt='1',invocation=unit,sourceHash=record['sourceSHA256'],resultingCommitHash=git('rev-parse','HEAD').decode().strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),guardChecksPassed=['committed A/B/C','62 fresh prebody validations','52 guarded mechanical commits','exact protected statement SHA256','fresh PASS','exit 0','not interrupted','no expected diagnostic','exact source SHA256','exact one-body/import delta','no intervening compiler invocation','no pre-staged files','no compiler','production/LocalDiamond freeze','git diff --check','git commit success','no post-staged files'])
with (OUT/'commit-receipts.jsonl').open('a') as log:
    log.write(json.dumps(receipt)+'\n')
print('GUARDED BODY COMMIT',json.dumps(receipt),flush=True)
