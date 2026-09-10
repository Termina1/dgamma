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
        return 'R206 authenticated seed (not R207 fresh)', True
    if baseline_status in ['legacy, not re-checked (standing classification)', 'legacy not applicable (not executed)']:
        return 'legacy not applicable (not executed)', False
    if baseline_status.startswith('FAILED — pre-existing') or baseline_status == 'pre-existing R137 failure (record only)':
        return 'pre-existing R137 failure (record only)', False
    if baseline_status in ['passed expected-negative contract', 'R205 expected-negative (not R206 fresh)', 'fresh expected-negative PASS'] and not in_closure:
        return 'R206 expected-negative (not R207 fresh)', False
    if baseline_status == 'fresh own-target FAILED' and not in_closure:
        return 'R206 untrusted failure (record only)', False
    return 'unchecked / invalidated', False


def needs_dependency_refresh(record, epoch, snapshot, dependency_hashes):
    """A passed root is not exempt from source/epoch dependency invalidation."""
    return (record['end'] < epoch or
            any(snapshot.get(path) != digest for path, digest in dependency_hashes.items()))
