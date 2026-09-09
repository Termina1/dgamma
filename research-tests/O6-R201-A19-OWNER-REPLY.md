# R201 A19 owner ruling

Received synchronously through `contact_supervisor(reason="need_decision")`
before A19-2. The question reported 19 micro-units /20 invocations, identified
only the expected generation-list append order as wrong, and requested exactly
one bounded repair rather than silently treating the cap as extendible.

> RULING: caps count MICRO-UNITS, not invocations (R199 precedent stands); each micro-unit keeps its own ≤3 invocation budget. A19-2 AUTHORIZED: change ONLY the expected incoming/outgoing live-generation lists to the ACTUAL CP3 putCurrentGeneration/scan order (append), no theorem/producer/type change; record the misexpectation in the ledger as fixture-expectation error, not a producer defect. A20 is PERMITTED if a well-defined micro-unit exists inside the clock (new attempts stop 18:26Z) — e.g. a second attachment fixture or the first activation-position transport step — otherwise freeze A after A19. C stays ineligible; B retained-closing join stays open as recorded. Then docs + fresh final validation + gate as planned.

Applied correction: only the concrete expected incoming/outgoing lists in the
fixture type/application, no producer changes. See
`O6-R201-A19-FIXTURE-RULING.json` for the exact byte hashes/replacements;
`A19-1.source`, `A19-2.source` and `A19-amendment.json` are in the raw archive.
A20 was not started; A froze at `df921f18` after A19-2 PASS.
