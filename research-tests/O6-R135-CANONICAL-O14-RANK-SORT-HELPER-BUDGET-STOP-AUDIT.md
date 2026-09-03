# O6 revision 135: Canonical O14 rank-sort helper budget stop audit

## Coordinate and scope

This shift began at the required accepted coordinate
`d2828ca3ff67f1729ab7c6b9d3571c54a3bcbd7d` on
`cp5-thm73-scoping`, with only the permitted untracked `paper/` and
`review-o6-body-adversarial.md`.  It read both R134 audits before editing.
CanonicalSort O14 (`supportOrderingSpike_rhs`) was the only proof class opened.

The supervisor-mandated rank-transitivity correction landed first, by itself, as
`canonicalRankLTETransitive` in commit `75021cc73e17875f561b504d6d93774c0ee85c16`
(`add canonical rank order transitivity`).  Its clauses are plain top-level
equations and it was checked fresh before and after the commit.  It does not
consume O14's fill budget.

## Helper strategy

The attempted fresh helper unit retained R134's protocol-rank stable-sort route.
It packaged:

- stable insertion by `isLTE`, using `lteSuccLeft` in the descending branch;
- an erased `CanonicalRankOrdered` invariant;
- insertion and sorting membership reflection/preservation;
- uniqueness preservation;
- exact Boolean selection of supported registry names;
- a defaulted executable protocol-rank projection, with agreement on
  `NameProtocolRank`; and
- strict-rank conversion to `BeforeIn`.

It used proof-carrying producer records so each comparison/selection decision
would determine one executable output and all corresponding proof fields.  No
O14 body replacement was attempted.

## Strict helper attempt budget

| Attempt | Result |
|---:|---|
| 1 | The main package shape elaborated far enough to expose three mechanical classes: dependent `Elem Here` clauses used distinct explicit names that the index forced equal (nonlinear-pattern diagnostics); three runtime package producers incorrectly called quantity-0 assembly helpers; and two equality transports had the wrong orientation.  The supported-registry membership bridge also needed an explicit observation equation. |
| 2 | After moving dependent eliminations into right-hand-side `case`s, correcting equality orientation, and making runtime assembly helpers relevant, the stable insertion/sort/selection packages checked.  The only remaining obstruction was the supported-active lookup bridge: its explicitly written case expression still left the dependent `value` family ambiguous and did not rewrite `supportedActiveAt`. |
| 3 | Explicit telescopes were added throughout the candidate and the lookup bridge was factored through an exact equality plus `replace`.  Idris still could not bind the dependent `value` family inside the manually restated lookup/lifecycle case, and the downstream `replace` retained a state-family constraint.  Static inspection also found one remaining as-pattern in that candidate, so it was not eligible to retain even apart from the elaboration failure. |

The helper unit therefore exhausted its authorized **3/3** attempts.  Per the
binding rule, no fourth correction was tried.  The entire uncommitted helper
candidate was restored.  The standalone, already-checked transitivity lemma is
the only retained CanonicalSort source change.

## Disposition

O14's body remains exactly `?supportOrderingSpike_rhs`, so its fill budget is
still **0/3** and CanonicalSort remains at five holes.  The project remains at
**18 holes**, split **5/4/8/0/1**.  This is a mechanical elaboration stop rather
than a semantic counterexample to rank sorting, but the helper budget is
binding.  Unit A is parked and the authorized shift proceeds to Unit B (O7
quantity-0 restatement) from the safe committed boundary.
