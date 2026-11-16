# Exact profile-normalization proposal: algebra sign-off

## Approval

I approve the two definitions and all eight PN1–PN8 interfaces in `audit/PROFILE_NORMALIZATION_STATEMENTS.md`, SHA-256

`73ad2a8eed5d8938daab619c740891b806cb1ff48c01ec028d8d0774bf641f7d`.

No assumption, type, conclusion, or edge-case correction is needed. This approval includes arbitrary real `chi` in the identity layer, explicit `D` in both adapters, arbitrary `y,z` in the basic identities, and the derived legality proof in PN6–PN8. No implementation or frozen contract has been changed.

The independent reconstruction is in `audit/PROFILE_NORMALIZATION_ALGEBRA.md`. Its source-facing notation used `A.chi`; the proposed independent `chi` parameter is valid because none of these counting or normalization arguments uses the sign of that threshold or an identification with the boundary parameter. The actual source application must choose `chi = A.chi`, as the proposal says. No new model assertion is made by leaving the finite identity more general.

All eight fully expanded proposition signatures were also checked for elaboration under Lean 4.33.1, with the adapter types supplied as local parameters. The derived proof `hpLegal` and every occurrence of the right-associated triple and dependent key type elaborated. These were transient `#check` expressions only; this was a type check, not an implementation or proof verification.

## Exact definitions

`sourceCell D P timeClass` is the proposed application of `finProdFinEquiv` to the time label and the actual profile's partition label. Its codomain is exactly `Fin (R * P.cellCount)`. The digit count vector then has dimension `(R * P.cellCount) * D.k`. This matches the two consecutive flattenings in the existing `encodeProfile`/`profileKeyCounts`, without assuming that two different flattened triple representations are equal.

`sourceGood D P chi j a` is the existential alphabet-bound wrapper around the existing representative predicate. There is no change to `P.IsGoodDigit`, the representative, the strict threshold `2 * chi`, or the pile profile. The proof component in its `Fin` constructor is irrelevant. Neither definition needs regularity or a new positivity hypothesis.

## PN1–PN8

1. **`sourceGood_fin_iff`: approved.** Use `l.isLt` for the reverse implication. For an existential witness `ha`, `⟨l.val,ha⟩ = l` follows from `Fin.ext` (or proof irrelevance). This proves the forward implication for every real `chi`. No legality or range predicate is necessary because the argument already is a `Fin D.k` digit.

2. **`exceptionalPositions_source_eq`: approved.** Expand the model filter and the time-profile filter of `positions`. Both impose `join.length ≤ j.val < x.length`. Inside that guard, frozen `legalVector_digit` and PN1 identify the natural-digit goodness predicate with the vector predicate. Equality is of the full finite supports. A join longer than `x` makes both filters empty; no prefix or raw-pair premise is missing.

3. **`digitCount_source_eq`: approved.** The current `TimeProfile.digitKey` has type `Fin R × Fin P.cellCount × Fin D.k` and value `(timeClass j, P.classify (asProfile D j), X j)`, with exactly the right association used by `a.1`, `a.2.1`, and `a.2.2` in the proposed conclusion. Injectivity of the outer `finProdFinEquiv` identifies the first two coordinates with the joint model cell. Equality in `Fin D.k` is equality of values, and frozen digit agreement supplies the model digit. Reordering the filter's conjunctions proves equality of natural cardinalities. Dividing by the same `Real.log N` is then exact. No compatibility-of-counts premise is introduced.

4. **`profileR_source_eq`: approved.** Unfold `TimeProfile.profileR` and `logScale`, and rewrite the support with PN2. This is a direct identity. It neither rounds the exceptional cardinality nor introduces an inequality or a sign premise.

5. **`profileH_source_eq`: approved.** Apply PN3 to each digit; its finite sum gives the corresponding `digitTotal`. For each cell apply the reviewed zero-aware normalization schema with `L = Real.log N > 0`, derived from `D.one_lt_N`. Reindex the outer pair of labels to `Fin (R * P.cellCount)` using the exact product equivalence. The resulting expression is precisely the existing `typeEntropy` divided by `log N`. The source weighted-entropy interpretation does not require invoking `profileH_source_formula` with its stronger exported assumptions: the literal `profileH` definition suffices.

6. **`profileWord_profileR_le`: approved.** Actual ProfileWord membership supplies admissibility and stable membership, hence exactly the displayed derived legality proof via `stable_desc`. PN4 changes the desired inequality to `exceptionalCard / log N ≤ alpha`. The original real cutoff is `p.property.2.2`; division by positive `log N` gives the result. There is no `0 ≤ alpha` premise. For negative `alpha`, no such profile word exists, because its nonnegative exceptional cardinality could not satisfy the real cutoff. No floor-bound replacement is valid or needed here.

7. **`profileWord_profileH_key`: approved.** Apply PN5 to the actual three words with the derived legality proof, then the existing exact function equality `profileKeyCounts_encode`. The resulting `c` is exactly `R * P.cellCount`. A different proof of the same legality proposition does not change `legalVector`. The route is arbitrary fixed data: restricting a fibre by route never changes this count identity, and no probabilistic interpretation of the route is needed.

8. **`profileFibre_card_le_rpow_profileH`: approved.** Specialize the already proved `profileFibre_card_le_rpow_entropy` to the exact realized `keyp`, and rewrite its exponent by PN7. The preceding `profileFibre_finite` theorem derives finiteness of the actual domain; the new statement does not assume it or exploit `Nat.card` of an infinite type. The bound is for the already defined fibre of a refined descriptor, not an injection from all words into descriptor classes. Unrepresented keys remain covered by the earlier arbitrary-key theorem; this realized-key specialization is exactly what permits the source entropy of a representative word to appear on the right.

## Zero-aware helper schema

The proposed schema is valid for all natural `d,k`, every natural count array, and every positive real scale `L`. Fix a cell and write `S = ∑ l, n_l`.

- For `n_l = 0`, the guard `0 < n_l/L` is false, and both weighted terms in the count-log-count expansion are zero. No log quotient law is used at zero.
- For `n_l > 0`, derive `S ≥ n_l > 0`. The normalized total is `S/L`, the common nonzero scale cancels in `(S/L)/(n_l/L)`, and the valid logarithm quotient law gives `log S - log n_l`.
- The term is therefore `(n_l * log S - n_l * log n_l)/L`. Summing and casting the natural sum yields `(S * log S - ∑ l, n_l * log n_l)/L`.
- A zero total has every natural count zero and contributes zero. Empty outer or digit types are covered by empty finite sums.

This proves the helper exactly as proposed, including its use of `∑ q, (n a q : ℝ)/L` in the numerator rather than treating that normalization as an unproved identity. The only scale sign required is already derived from the model. There is no bound, positivity, realization, or normalization condition on the natural counts beyond being natural counts.

## Edge cases and scope

Zero piles outside the actual legal prefix, empty extensions, zero good-count cells, `K=0`, and an empty time-label type are all preserved. No separate `R>0` or partition-cell-count premise is needed for finite equivalence and sum manipulations. A terminal singleton has empty extension, hence zero entropy; the exact fibre bound specializes to at most one word.

The exceptional positions **and their values** remain fixed in the existing key/fibre definition. This is essential for the entropy injection proved earlier. PN8 would not automatically hold for a newly coarsened fibre that forgot those values. Nothing in this proposal makes that change.

The identities imply constancy of source `profileH` on an encoded fibre. They do not imply constancy of exact `cL`, equality of exceptional cost sums, or validity of a stochastic density estimate. They also do not identify an arbitrary timeClass with the source mesh; the application supplies that deterministic map. No horizon, AlmostLike, regularity, ambient approximation, variational margin, or conditional law is used by these finite statements.

The proposed dependency order and all five proof-local helper schemas are approved. No further public helper or strengthened hypothesis is needed before implementation.
