"""Pure current-source disposition policy; a rejected attempt cannot revive a seed."""

def classify_module(*, exact, record, epoch, blocked, in_closure,
                    baseline_status, seed_authenticated):
    if blocked:
        return 'blocked by untrusted/retired import', False
    fresh = bool(exact and record['fresh'] and not record['unexpectedBuilding'])
    if exact and (not record['passed'] or not fresh):
        return ('fresh own-target FAILED' if fresh else
                'rejected native invocation / cache-resource gate'), False
    if exact and record['passed'] and record['end'] >= epoch:
        return ('fresh PASS' if record['exit'] == 0 else
                'fresh expected-negative PASS'), record['exit'] == 0
    if not in_closure and seed_authenticated:
        return 'R205 authenticated seed (not R206 fresh)', True
    if baseline_status == 'legacy, not re-checked (standing classification)':
        return 'legacy not applicable (not executed)', False
    if baseline_status.startswith('FAILED — pre-existing'):
        return 'pre-existing R137 failure (record only)', False
    if baseline_status == 'passed expected-negative contract' and not in_closure:
        return 'R205 expected-negative (not R206 fresh)', False
    return 'unchecked / invalidated', False
