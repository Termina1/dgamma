# R197 D5 consumer STOP3/3

The PRODUCER providerHeadObserved is checked at40d0d59e and retained, as are
D2's native observed head equation, D4's packet builder, and D6's generic Bool
eliminator (8deec075). This is an OPTIONAL consumer failure, not a producer
failure or a claimed specification contradiction.

D5-1: eliminating the packet, `trans before (sym after)` rejects at its two
identical-looking abstract-if types. Source fully restored before the gated
D6 helper. D5-2: delegating to D6 rejects the same constraint at `after`.
Supervisor explicitly approved D5-3's unprotected signature amendment:
SAME observation record, explicit observed Bool and erased own-field equation;
project the record, eliminate Bool only, transport the fields, call D6.
D5-3 still fails. All three snapshots/logs/JSON retained; no fourth, renamed,
shrunken or consumer retry authorized. Reverted source to exact D6 HEAD hash
b7ef3f6479874691da6dcce7093b0fd5512b7193090151e607f5248e838a1989. Producer and type unchanged.

## Final native error (verbatim, --show-implicits)

```text
1/1: Building DGamma.CP5ProviderHeadObservedSpike (/Users/vyacheslavshebanov/Work/dgamma/research/DGamma/CP5ProviderHeadObservedSpike.idr)
Error: While processing right hand side of providerHeadRetirementFromObserved. Can't solve constraint between: if observedHeadGuard {name} {key} {world} {error} {value} {nameEq} {keyEq} {wanted} {actor} {component} {parent} {flag} {table} {lifecycle} {rest} observation then Just {ty = name} actor else providerIn {error} {world} {key} {value} {name} {{conArg:12484} = nameEq} {{conArg:12487} = keyEq} wanted rest and if observedHeadGuard {name} {key} {world} {error} {value} {nameEq} {keyEq} {wanted} {actor} {component} {parent} {flag} {table} {lifecycle} {rest} observation then Just {ty = name} actor else providerIn {error} {world} {key} {value} {name} {{conArg:12484} = nameEq} {{conArg:12487} = keyEq} wanted rest.

DGamma.CP5ProviderHeadObservedSpike:166:17--166:47
 162 |     (replace {p = \guard =>
 163 |       (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
 164 |         (Bind actor (MkFiber component parent flag table lifecycle) :: rest) =
 165 |        (if guard then Just actor else providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest))}
 166 |       equation (beforeHeadEquation observation))
                       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^


```

At the final failure, the first projected field cannot be supplied to the
explicit replacement predicate, although the full displayed implicit types
are identical. The simple native Bool-branch helper itself DOES typecheck.
This is an elaboration/hidden-index wall; not a proof of falsehood. Lane2 must
not treat the producer as a proved generic compositional consumer lemma.
No resource stop, mutation, additional Building, unsafe escape or new hole.
Supervisor RATIFIED the full stop and continuation ONLY to D7/D8 producer
fixtures, then E and final validation. Both fixtures now pass through the
actual producer. No further D5 attempt occurred.

Owner diagnosis (not a proved compiler-internals claim): Idris2 v0.8.0's
conversion check rejects syntactically identical displayed `if` types over a
record projection; lazy `Delay` desugaring may be involved. A FUTURE producer
variant splitting the packet before its field types mention a projected guard,
or a compiler fix, may be needed. Neither is pursued in R197.
