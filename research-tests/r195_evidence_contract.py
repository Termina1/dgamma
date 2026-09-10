"""Pure R195 evidence contracts; no compiler, subprocess or filesystem writes."""
import re

def owned_target(path):
    # Owner clarification: inherited main-baseline modules are valid targets,
    # even if their subject also belongs to lane2. Never enter another tree.
    return path == 'package' or (path.startswith(('research/DGamma/', 'research-tests/DGamma/'))
        and '..' not in path.split('/'))

def source_code(source):
    return '\n'.join(line for line in source.decode().splitlines()
                     if line.strip() and not line.lstrip().startswith(('--', '|||')))

def validate_record(record, source, log, root):
    import hashlib
    assert hashlib.sha256(source).hexdigest() == record['sourceSHA256']
    assert log == record['transcript']
    assert owned_target(record['path']), 'Target outside main research roots'
    assert 'rssSamples' in record and 'targetMutationDetected' in record
    assert record['maxSampleRSSKiB'] == max([s['rssKiB'] for s in record['rssSamples']] or [0])
    if record['passed']:
        assert record['fresh'] and not record['interrupted'] and not record['targetMutationDetected']
        if record['path'] != 'package':
            paths = '(?:' + re.escape(record['path']) + '|' + re.escape(str(root / record['path'])) + ')'
            assert re.search(r'^\d+/\d+: Building [^\n]+ \(' + paths + r'\)$', log, re.M)
        if record['expectedDiagnostic']:
            assert record['exit'] != 0 and record['expectedDiagnostic'] in log
            assert record.get('symbol') and record['symbol'] in log
        else:
            assert record['exit'] == 0 and 'Error:' not in log

def validate_attempts(records, snapshots):
    attempts = {}
    for record in records:
        match = re.fullmatch(r'([A-Z]+\d+)-(\d+)', record['unit'])
        if match:
            attempts.setdefault(match[1], []).append(record)
    for unit, runs in attempts.items():
        numbers = [int(r['unit'].rsplit('-', 1)[1]) for r in runs]
        assert numbers == list(range(1, len(runs) + 1)) and len(runs) <= 3, unit
        assert not any(r['passed'] for r in runs[:-1]), 'No retry after a passed proof unit'
    for lane, cap in [('A', 26), ('B', 16)]:
        selected = sorted(int(unit[1:]) for unit in attempts if re.fullmatch(lane + r'\d+', unit))
        assert selected == list(range(1, len(selected) + 1)) and len(selected) <= cap
    return attempts
