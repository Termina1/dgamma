#!/usr/bin/env python3
"""Persist exact R178 check evidence, interval ledger and declaration inventory."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import tarfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
TMP = pathlib.Path('/tmp/dgamma-r178')
START = '6d6ab285ba0c173101d49e3aa7c8492122635b9e'
OUT = ROOT/'research-tests'

def git(*args):
    return subprocess.check_output(['git',*args],cwd=ROOT,text=True)

def rows(path):
    return [json.loads(line) for line in path.read_text().splitlines()]

def moment(value):
    return datetime.datetime.fromisoformat(value)

primary = rows(TMP/'ledger.jsonl')
boundaries = rows(TMP/'final-suite-ledger.jsonl')
phases = rows(TMP/'final-phases.jsonl')
for row in primary:
    row['transcript'] = (TMP/(row['unit']+'.log')).read_text()
    data = (TMP/(row['unit']+'.source')).read_bytes()
    assert hashlib.sha256(data).hexdigest() == row['sourceSHA256'], row['unit']
    row.setdefault('seconds',(moment(row['end'])-moment(row['start'])).total_seconds())
with tarfile.open(OUT/'r178-evidence/Unit-A-boundaries.tar.gz') as old:
    for row in boundaries:
        filename = 'final-suite-'+pathlib.Path(row['path']).stem+'.log'
        row['transcript'] = ((TMP/filename).read_text() if row.get('boundaryRun')=='R178-final'
                             else old.extractfile(filename).read().decode())
intervals = sorted([dict(label=r.get('unit',r['path']),start=r['start'],end=r['end']) for r in primary+boundaries],key=lambda r:r['start'])
for previous,current in zip(intervals,intervals[1:]):
    assert moment(previous['end']) <= moment(current['start']), (previous,current)
legacy = next(p for p in phases if p['phase']=='legacy-seeded')
assert moment(intervals[-1]['end']) <= moment(legacy['start'])
legacy_source = (OUT/'run-r11-suite.sh').read_text()
legacy_counts = {key:len([line for line in re.search(key+r'=\(\n(.*?)\n\)',legacy_source,re.S).group(1).splitlines() if line.strip() and not line.lstrip().startswith('#')])
                 for key in ['SPIKES','POSITIVE','NEGATIVE_SPECS']}
report = dict(timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),
    primaryChecks=primary,boundaryChecks=boundaries,finalPhases=phases,
    primarySummary=dict(total=len(primary),ordinaryPass=sum(r['passed'] and not r.get('expectedDiagnostic') for r in primary),
      expectedDiagnosticPass=sum(r['passed'] and bool(r.get('expectedDiagnostic')) for r in primary),
      failures=sum(not r['passed'] and not r.get('interrupted') for r in primary),
      costInterruptions=sum(bool(r.get('interrupted')) for r in primary)),
    boundarySummary=dict(unitA=sum(not r.get('boundaryRun') for r in boundaries),final=sum(r.get('boundaryRun')=='R178-final' for r in boundaries),allPassed=all(r['passed'] for r in boundaries)),
    compilerIntervalsVerifiedNonOverlapping=True,intervals=intervals,
    maximumInstrumentedRSSKiB=max(r.get('maxSampleRSSKiB',0) for r in primary+boundaries),
    legacyCounts=legacy_counts,legacyPassed=legacy['passed'],legacyFreshClaim=False,
    legacyTranscript=(TMP/'F-legacy-seeded.log').read_text(),
    commits=git('log','--reverse','--format=%H %s',START+'..HEAD').splitlines())
(OUT/'O6-R178-COMPILER-LEDGER.json').write_text(json.dumps(report,indent=2)+'\n')
text=['# R178 compiler transcript presentation','',
      'Raw exact source snapshots/logs/wrapper JSON are in O6-R178-COMPILER-EVIDENCE.tar.gz; the committed JSON also preserves exact transcripts. Rendered Markdown lines are right-trimmed.',
      'Unit A pre-final boundary logs are separately preserved in r178-evidence/Unit-A-boundaries.tar.gz.',
      'The legacy suite is seeded, not a cold/fresh rebuild. Two C9 cost stops have NO compiler verdict.','']
for row in primary:
    text += ['## '+row['unit'], '',f"{row['start']} → {row['end']}; passed={row['passed']}; interrupted={row.get('interrupted',False)}; SHA256={row['sourceSHA256']}", '', '```text',row.get('transcript','').rstrip(),'```','']
for row in boundaries:
    text += ['## '+row.get('boundaryRun','Unit-A')+' '+row['path'],'','```text',row['transcript'].rstrip(),'```','']
text += ['## Legacy seeded suite','','```text',report['legacyTranscript'].rstrip(),'```','']
(OUT/'O6-R178-COMPILER-TRANSCRIPTS.md').write_text('\n'.join(line.rstrip() for line in '\n'.join(text).splitlines())+'\n')

def declarations(text):
    found={}
    for number,line in enumerate(text.splitlines(),1):
        match=re.match(r'(?:(?:0|1) )?([A-Za-z_]\w*)\s*:',line) or re.match(r'(?:record|data)\s+([A-Za-z_]\w*)',line)
        if match:found[match.group(1)]=number
    return found

inventory=['# R178 declaration / clause correspondence','','Every listed declaration is in a fresh-checked module. This inventory does not upgrade a specification or helper into a theorem. See module comments and the branch map below.','',
'| Units | Semantic capital | Status |','|---|---|---|',
'| A1–A22 | Authentic A9 relation, structural negative, nonempty identity fixture | checked/proved; A16 normalization stop ratified |',
'| A23–A32 | Explicit accepted-bijection A9 signature/caller threading and negatives | checked; no O19 body |',
'| B1–B37 | Exact accepted retained-or-closing coverage; supported closing exclusion | proved |',
'| B38–B45 | Actual root birth/static coverage both directions | proved |',
'| B46–B62 | Actual lifecycle flag preservation and retired-endpoint retirement history | proved |',
'| B63–B73 | Prefix-current A9 birth authentication and bilateral actual retirement transport | proved |',
'| B74–B88 | Exact external-root action transport and accepted support-relative retirement | proved |',
'| B89–B97 | Actual support-edge rank induction; complete static image coherence | proved |',
'| B98–B119 | Actual provider/parent clause facts and total cross-state support induction | proved |',
'| B120–B124 | Producer-owned packages, BOTH support-truth implications, then O18 | proved; O18 closes one hole |',
'| C1–C6 | Executable interval-compatible root placement replacement specification | checked; frozen integration OPEN |',
'| C7–C8 | Fixture-only observation/annotation helpers | checked |',
'| C9 | Concrete located-root packet | PARKED 2/3; absent from source |',
'| C10–C11 | Authenticated R174 scalar interval-shape equality | proved in three authorized checks |','',
'## Exact declaration inventory','']
changes=git('diff','--name-status',START,'--','research/','research-tests/DGamma/').splitlines()
for change in changes:
    status,path=change.split('\t',1)
    if not path.endswith('.idr'):continue
    current=(ROOT/path).read_text()
    old='' if status=='A' else git('show',START+':'+path)
    before=declarations(old)
    added={name:line for name,line in declarations(current).items() if name not in before}
    inventory += ['### '+path,'']
    if added:
        inventory += [f'- `{path}:{line}:{name}` — checked declaration (see source contract).' for name,line in added.items()]
    else:
        inventory += ['- Existing surface only: explicit A9 threading, O18 body, or narrowly authorized visibility change; see audit/protected-surface report.']
    inventory += ['']
(OUT/'O6-R178-CLAUSE-MAP.md').write_text('\n'.join(inventory))
with tarfile.open(OUT/'O6-R178-COMPILER-EVIDENCE.tar.gz','w:gz') as archive:
    for path in sorted(TMP.iterdir()):
        if path.is_file():archive.add(path,arcname=path.name)
print(json.dumps({key:report[key] for key in ['primarySummary','boundarySummary','compilerIntervalsVerifiedNonOverlapping','maximumInstrumentedRSSKiB','legacyCounts','legacyPassed']},indent=2))
