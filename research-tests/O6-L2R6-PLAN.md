# L2R6 bounded shift plan

Exact clean baseline c09c0da2; branch cp5-thm73-lane-a8a10.

{
  "start": "2026-09-09T04:11:16.546583+00:00",
  "deadline": "2026-09-09T08:11:16.546583+00:00",
  "attemptCutoff": "2026-09-09T07:31:16.546583+00:00",
  "validationCutoff": "2026-09-09T07:46:16.546583+00:00",
  "gateTime": "2026-09-09T07:56:16.546583+00:00",
  "base": "c09c0da2",
  "caps": {
    "A": 14,
    "B": 14,
    "C": 10,
    "D": 12,
    "E": 3
  }
}

Ordered caps A14 B14 C10 D12 E3. One new declaration per own-target fresh check; at most three attempts per micro-unit. Any 3/3: full revert, audit and supervisor gate; two at same seam stop that unit. No inherited-source companion authority. No lock/window operations, main-worktree access, production edits or full rebuild. Bootstrap V0 touches only unchanged L2R5RootCatalog target; subsequent validations only new L2R6 sources. 18 GiB sampled guard keeps all checks below 19 GiB (stricter than 48 GiB overall ceiling).
