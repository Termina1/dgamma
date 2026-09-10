#!/usr/bin/env python3
"""Compiler-free adversarial evidence/policy checks with authenticated test reports.
maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water).
"""
import hashlib, json, pathlib, re, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parents[1]; ART=ROOT/'research-tests'; OUT=pathlib.Path('/tmp/dgamma-r204')
sha=lambda b:hashlib.sha256(b).hexdigest()
for label,script,count in [('contract-tests','test_r204_evidence_contract.py',27),('policy-contract-tests','test_r204_policy_contract.py',10)]:
    result=subprocess.run([sys.executable,'-I',str(ART/script)],cwd=ROOT,capture_output=True)
    log=result.stdout+result.stderr; (OUT/(label+'.log')).write_bytes(log)
    assert result.returncode==0 and re.search(rb'Ran '+str(count).encode()+rb' tests',log) and log.rstrip().endswith(b'OK')
    report=dict(status='PASS',tests=count,command=[sys.executable,'-I',str(ART/script)],logSHA256=sha(log),testSourceSHA256=sha((ART/script).read_bytes()),contractSourceSHA256=sha((ART/'r204_evidence_contract.py').read_bytes()))
    (OUT/(label+'.json')).write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps(report))
