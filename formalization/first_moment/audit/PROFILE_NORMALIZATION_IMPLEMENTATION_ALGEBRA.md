# Profile normalization: independent implementation audit

## Decision and exact files

Approved without corrections. I compared both definitions and all eight PN1–PN8 statements and their proofs in `FirstMomentModel/ProfileNormalization.lean` with the frozen `PROFILE_NORMALIZATION_CONTRACT.md`, the previously proved profile/fibre definitions, and the authorized TeX's space-time digit profile (lines 700–756).

* Implementation SHA-256: `9bc0039bbdbe5f970ad07bdcf8063c5c2bb46067a80d35fd53e9f60c64f73971`.
* Frozen contract SHA-256: `a8e994b8628e96ceae51a10dd8fc30bb7c771b16f4c14429acc01807a781c49c`.
* Freeze time: `2026-09-17T22:17:44.883493+00:00`.
* All 86 file hashes referenced by `PROFILE_NORMALIZATION_FREEZE.json` match their files. The earlier contracts and authorized sources remain unchanged.

The file contains exactly the two frozen definitions and eight frozen exported theorems. The only entropy helpers, `hnormalized` and `hterm`, are proof-local instances of the reviewed helper schema. There are no extra exported declarations, axioms, placeholders, unsafe declarations, or implementation substitutions. This is the independent statement/algebra review; the parent separately completed the kernel and trust verification of this exact source hash.

## Definitions and interfaces

`sourceCell` is exactly the application of `finProdFinEquiv` to `(timeClass j, P.classify (asProfile D j))`; its codomain is `Fin (R * P.cellCount)`. The later digit flattening therefore has dimension `(R * P.cellCount) * D.k`, as frozen.

`sourceGood` is exactly the existential bound wrapper around the existing `P.IsGoodDigit chi (asProfile D j)`. The actual representative predicate and its strict threshold are unchanged. The parameter chi is arbitrary real data. Neither definition imports a positivity or regularity premise.

All PN1–PN8 binders and conclusions agree with the contract's expansions. In particular:

* PN2–PN5 accept arbitrary y and z and only require legality of x. No prefix, compatibility, raw-pair, stability, or regularity premise was added.
* PN6 has no time label or route argument and retains arbitrary real alpha. PN6–PN8 use precisely the specified legality proof derived from the actual `ProfileWord`'s admissibility and stability.
* PN7 and PN8 retain arbitrary fixed route data and the exact realized key. They neither discard the exceptional values from the key nor claim an injection of all words into their profile keys.
* PN8 is an exact real-power bound on the actual `ProfileFibre` cardinality. It assumes no `Finite` instance, asymptotic entropy correction, or extra positive-count property.

## Proof checks

**PN1 — `sourceGood_fin_iff`.** The existential witness changes only the proof field of the same `Fin` digit. Proof irrelevance makes the forward implication valid, and `l.isLt` supplies the reverse witness. No alphabet membership assumption is omitted because l already has type `Fin D.k`.

**PN2 — `exceptionalPositions_source_eq`.** Both unfolded filters impose `join.length ≤ j.val < x.length`. Inside that interval, `legalVector_digit` and PN1 identify the natural and finite-digit goodness predicates; outside it both membership propositions are false. The proof does not accidentally rely on the zero padding of `legalVector` being legal or good. It handles a lower endpoint beyond the word length by the same empty filter.

**PN3 — `digitCount_source_eq`.** The proof establishes equality of the entire finite sets before taking cardinalities. Injectivity of `finProdFinEquiv` separates exactly the time and partition coordinates. `Fin.ext_iff` and literal digit agreement separate the digit coordinate. The right-associated source triple is correctly read as `a.1`, `a.2.1`, and `a.2.2`; no different flattened triple convention is substituted. The two good-position filters differ only by these proved identities and association/order of conjunctions. Both normalized counts divide by the same `Real.log N`.

**PN4 — `profileR_source_eq`.** Direct rewriting of the source cardinality by PN2 yields the identical cardinality divided by the identical logarithm. There is no rounding or change of exceptional support.

**PN5 — `profileH_source_eq`.** Its zero-aware algebra is valid for arbitrary natural count arrays, including zero total cells and empty index types. Fix a cell a and a digit l.

* If `n a l = 0`, the normalized count is zero, the strict positivity guard is false, and both weighted terms on the right vanish. No logarithm quotient rule is applied in this case.
* Otherwise natural nonzeroness gives `(n a l : Real) > 0`. A single-term lower bound in the nonnegative finite sum gives positivity of the cell total. Both nonzero hypotheses supplied to `Real.log_div` are therefore justified.
* `Finset.sum_div` and cancellation of the positive scale L identify the ratio of normalized counts with the ratio of unnormalized counts. The local term is exactly `(n_l*log(total) - n_l*log(n_l))/L`.
* Distributing and summing gives the existing `typeEntropy` formula. `Nat.cast_sum` is used explicitly; the total is the cast of the natural sum, as required by that definition.

The proof obtains `L=log N>0` from `D.one_lt_N`, which is already part of the model. It unfolds the literal source `profileH`/`digitTotal`, rewrites every digit frequency through PN3, and reindexes the outer `(time,partition)` pair using `finProdFinEquiv.sum_comp`. Its local count array n is exactly `goodDigitCount`; there is no normalization, realization, or compatible-total premise on the helper. This establishes the precise equality `profileH = typeEntropy/log N` with no error term.

**PN6 — `profileWord_profileR_le`.** After PN4, the target is `exceptionalCard/log N ≤ alpha`. The proof uses `div_le_iff₀` with the derived positive logarithm and the original real inequality `p.property.2.2`. It does not replace the cutoff with `exceptionalBudget` or require alpha nonnegative. Negative alpha simply permits no such actual profile word.

**PN7 — `profileWord_profileH_key`.** The existing exact function identity `profileKeyCounts_encode` and PN5 rewrite to the frozen conclusion. The implicit joint-cell cardinality is exactly `R * P.cellCount`. The chosen route only restricts the fibre; it is not assigned a new probabilistic property.

**PN8 — `profileFibre_card_le_rpow_profileH`.** Rewriting the exponent with PN7 makes the target exactly the existing arbitrary-key theorem `profileFibre_card_le_rpow_entropy`. That earlier theorem uses proved finiteness and the literal restriction injection in `ProfileFibreEntropy`; it does not exploit the convention for `Nat.card` of an infinite type. Its exponential-to-power conversion uses the same nonzero `log N`. Specializing to the realized key changes neither the domain nor the exceptional labels.

## Edge cases and limits of the result

Empty extensions, zero good counts, zero cells in the local normalization helper, empty finite index types, and `K=0` are covered by the actual finite filters and sums. No new `R>0` hypothesis is needed; if a map to an empty time-label type exists, its domain is empty. Zero piles outside the legal prefix remain allowed. The source application may set chi to the boundary threshold and use its source time mesh, but these identities need neither choice as a premise.

The terminal/zero-extension case has entropy zero; the exact fibre theorem then gives cardinality at most one, as expected from the already fixed prefix and labels. The module proves source entropy and exceptional-cardinality normalization. It does not prove constancy of exact cL or exceptional costs on a fibre, an ambient approximation, a source variational condition, or a stochastic density estimate.

No correction or new assumption is needed.
