# Frozen additive exact mean and tail exponent contract

This contract is frozen before any Exponent Lean code. It selects exactly five definitions X.D01–05 and fifteen theorem statements X.01–15, with the complete signatures and semantics reproduced below. The root compared all three independent reports, and each reviewer accepted every final signature before this freeze. Their reports and the root comparison are hashed in exponent_freeze.json.

All previous definitions, theorems, proofs, contracts, and mathematical sources remain unchanged. No added assumption, altered conclusion, extra named helper, new custom instance, extra axiom, or unproved placeholder is permitted. Local proved steps and trusted mathlib results implement the specified dependencies. The four modules are Model (five definitions), Mean (X.01–05/X.15), Tail (X.06–08/X.13), and Estimates (X.09–12/X.14).

The finite logarithmic domain and explicit ambient error are exactly as specified; no asymptotic rate, random-recentering identity, or spatial gain is assumed. The full original goal remains active and incomplete. The original pre-freeze wording below is retained as the selected exact specification.

# Proposed additive contract for exact mean and tail exponents

This independent pre-freeze report proposes five definitions and fifteen theorems. It contains no Lean implementation and changes no earlier source, definition, theorem, review, or freeze. Its scope is the exact finite exponent conversion for the existing actual matrix model, including two small-size consequences and the terminal case.

## 1. Source meaning and limits

I reread the permitted TeX at 430–535 and 1460–1675, especially legality at 446–451, the ambient definition at 490–519, the three density cases at 1486–1513, the conditional collision estimate at 1516–1523, and the singleton and terminal arguments at 1594–1660. I also reread the definition of `ψ_p` at 123–133.

The homogeneous PDF `2103.05068v3.pdf`, page 17, defines the whole-deck size exponent as `1+log_N λ_x`; page 24, Lemma 4.12, identifies the independent-row tail coincidence power. The fixed-column PDF `2510.22783v1.pdf`, page 23, equations (4.11)–(4.14), distinguishes its profile approximation from the actual expected-size logarithm; page 27, Lemma 4.14, uses the fixed-column tail pair factor; pages 28–29, Lemma 4.15, contain the small and singleton arguments. These are the source passages used in this report.

The current TeX's ambient `c_L^{r,b}` must remain `b` minus the log costs after the ambient prefix. It is **not** redefined to be the exact expected-size logarithm. Define instead the exact discrepancy

`ε_w = Real.log μ_w / Real.log N - b`.

Then the correct finite identity is `μ_x = N^(c_L^{r,b}(x)+ε_w)`. No claim that `ε_w` is small, positive, negative, or tends to zero is included. The source's asymptotic ambient hypothesis would require a separately formalized family of data and rate argument; it is not silently converted into a finite bound on this discrepancy.

Likewise, `N^c_E` is exactly the product of the sums of squared pile proportions. It is an upper bound for the fixed-count tail collision product, which can vanish even when `N^c_E` is positive. The two products are not identified.

All density results below use the existing absolute-coordinate `edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x)`. The source's recentering at 509–511 preserves internal cardinality but does not by itself preserve overlap density across two independent samples. No relative-coordinate density bridge is assumed or asserted.

## 2. Data, index conventions, and exact shorthand

Lengths `K`, `M`, and `A` are natural numbers. `M` is the absolute prefix length and `A` the absolute ambient length. The count array is `n : Fin K → Fin k → ℕ`. A prefix is `x : Fin M → Fin k`; an ambient prefix is `w : Fin A → Fin k`.

The two length proofs are `hM : M ≤ K` and `hAM : A ≤ M`. The ambient length bound is the derived proof `hAM.trans hM`, not an extra hypothesis. Prefix extension is represented by the exact pointwise equality

`hprefix : ∀ t : Fin A, x (Fin.castLE hAM t) = w t`.

Legality is imposed on `x` only. The legality of `w` is proved from that condition and `hprefix`. Thus the public signatures do not duplicate source positivity assumptions.

The logarithmic domain is `hN : 2 ≤ N`. This implies `0 < (N : ℝ)`, `1 < (N : ℝ)`, and `Real.log (N : ℝ) ≠ 0`. No separate positivity or nonzero hypothesis for these quantities is added.

The actual matrix bounds also take the original feasibility proof

`hn : ∀ j : Fin K, ∑ a : Fin k, n j a = N`.

Pure log identities omit `hn` when it is mathematically unnecessary. Count entries outside the selected legal prefix can be zero. Neither a positive alphabet-size premise nor positivity of the tail collision factor is assumed.

For readability only, the following mathematical abbreviations are used in conclusions below; they are **not** additional Lean definitions or parameters:

- `μ_x = prefixMean N n hM x`;
- `μ_w = prefixMean N n (hAM.trans hM) w`;
- `L = ambientSizeExponent N n hM A b x`;
- `ε = ambientMeanError N n (hAM.trans hM) w b`;
- `E = tailEdgeExponent N n M`;
- `D = edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x)`;
- `S = ∑ t ∈ Finset.univ.filter (fun t : Fin M => A ≤ t.val),`
  `Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ))`.

`N^u` in every theorem conclusion means `Real.rpow (N : ℝ) u`, with `u : ℝ`. Natural powers of real quantities, such as the existing fourth-power mean bound, retain their usual natural exponents until explicitly converted.

All new names are in namespace `EdgeLocalization`. `Exponent` is only a module directory. Numeric definitions take explicit `N` first, consistently with the existing numeric factors.

## 3. Complete definition inventory

### X.D01 — `legalPrefix`

Signature:

`{K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (x : Fin M → Fin k) : Prop`.

Definition:

`legalPrefix n hM x ↔ ∀ t : Fin M, 0 < n (Fin.castLE hM t) (x t)`.

The value is exactly the displayed universal proposition, corresponding to TeX 446–447. It has no `N` or `hn` argument.

### X.D02 — `ambientSizeExponent`

Signature:

`(N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K)`

`(A : ℕ) (b : ℝ) (x : Fin M → Fin k) : ℝ`.

Definition:

`b - (∑ t ∈ Finset.univ.filter (fun t : Fin M => A ≤ t.val),`

`  Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ))) / Real.log (N : ℝ)`.

The filter on the zero-based digit index selects exactly the source times `M_w < j ≤ M_x`. The source's `r` does not occur in its finite formula once `A=M_w` is fixed, so no redundant time parameter is added. The definition is total; its source interpretation is used under the displayed length, legality, and large-`N` hypotheses.

### X.D03 — `ambientMeanError`

Signature:

`(N : ℕ) {K k A : ℕ} (n : Fin K → Fin k → ℕ) (hA : A ≤ K)`

`(w : Fin A → Fin k) (b : ℝ) : ℝ`.

Definition:

`Real.log (prefixMean N n hA w) / Real.log (N : ℝ) - b`.

This is computed from the existing mean. It is not an error bound, rate field, asymptotic assumption, or supplied identity.

### X.D04 — `columnPsiTwo`

Signature:

`(N : ℕ) {k : ℕ} (n : Fin k → ℕ) : ℝ`.

Definition:

`-Real.log (∑ a : Fin k, (singleFactor N n a)^2)`.

This retains the source `ψ_p(2)=-log Σ_a p_a²` with `p_a=n_a/N`. No positivity is inserted into the definition; it is proved from `hn` and `hN` when needed.

### X.D05 — `tailEdgeExponent`

Signature:

`(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ) (M : ℕ) : ℝ`.

Definition:

`-(∑ j ∈ Finset.univ.filter (fun j : Fin K => M ≤ j.val),`

`  columnPsiTwo N (n j)) / Real.log (N : ℝ)`.

The same absolute tail-index filter occurs in the existing `tailSquareFactor` and `tailCollisionFactor` definitions. This is exactly the source's tail exponent with its displayed minus sign.

## 4. Complete named theorem inventory

There are exactly fifteen proposed new theorems. All argument orders and omitted hypotheses are part of this proposed contract.

### X.01 — `legalPrefix_of_prefix`

Parameters:

`{K k A M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K) (hAM : A ≤ M)`

`(w : Fin A → Fin k) (x : Fin M → Fin k)`

`(hprefix : ∀ t, x (Fin.castLE hAM t) = w t) (hx : legalPrefix n hM x)`.

Conclusion:

`legalPrefix n (hAM.trans hM) w`.

No population, probability, or count-sum premise is required.

### X.02 — `prefixMean_pos_of_legal`

Parameters:

`(N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ) (hM : M ≤ K)`

`(x : Fin M → Fin k) (hN : 2 ≤ N) (hx : legalPrefix n hM x)`.

Conclusion: `0 < prefixMean N n hM x`.

There is no `hn` premise. All selected ratios are positive directly from `hx` and `hN`; the empty product is one.

### X.03 — `log_prefixMean_of_legal`

Parameters are exactly X.02's parameters, in the same order.

Conclusion:

`Real.log (prefixMean N n hM x) = Real.log (N : ℝ) -`

`  ∑ t : Fin M, Real.log ((N : ℝ) / (n (Fin.castLE hM t) (x t) : ℝ))`.

This full-prefix log identity is proved from the existing product definition; it is not an assumption of the later exponent identity.

### X.04 — `log_prefixMean_extension`

Parameters:

`(N : ℕ) {K k A M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hM : M ≤ K) (hAM : A ≤ M) (w : Fin A → Fin k) (x : Fin M → Fin k)`

`(hprefix : ∀ t, x (Fin.castLE hAM t) = w t)`

`(hN : 2 ≤ N) (hx : legalPrefix n hM x)`.

Conclusion: `Real.log μ_x = Real.log μ_w - S`, expanded with the exact abbreviations in section 2.

There is no `b`, `hn`, assumed mean ratio, or separately assumed ambient legality.

### X.05 — `prefixMean_eq_rpow_ambientSizeExponent`

Parameters:

`(N : ℕ) {K k A M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hM : M ≤ K) (hAM : A ≤ M) (w : Fin A → Fin k) (x : Fin M → Fin k)`

`(b : ℝ) (hprefix : ∀ t, x (Fin.castLE hAM t) = w t)`

`(hN : 2 ≤ N) (hx : legalPrefix n hM x)`.

Conclusion:

`prefixMean N n hM x = Real.rpow (N : ℝ)`

`  (ambientSizeExponent N n hM A b x +`

`   ambientMeanError N n (hAM.trans hM) w b)`.

`b` is an arbitrary real number. No sign or interval condition is imposed on `b` or the computed error. The proof derives the identity from X.04 and positive-base logarithm inversion.

### X.06 — `column_square_sum_pos`

Parameters:

`(N : ℕ) {k : ℕ} (n : Fin k → ℕ) (hn : ∑ a, n a = N) (hN : 2 ≤ N)`.

Conclusion: `0 < ∑ a : Fin k, (singleFactor N n a)^2`.

At least one positive count is derived from `hn` and `hN`. No selected positive digit, nonempty alphabet instance, or positive square-sum premise is added.

### X.07 — `tailSquareFactor_eq_rpow_tailEdgeExponent`

Parameters:

`(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (M : ℕ) (hN : 2 ≤ N)`.

Conclusion:

`tailSquareFactor N n M = Real.rpow (N : ℝ) (tailEdgeExponent N n M)`.

`M` need not be at most `K` for this pure tail identity; an empty tail has product one and exponent zero. The proof uses X.06 for each included column, the logarithm of a finite product, and positive-base logarithm inversion. No tail-product identity is supplied as an assumption.

### X.08 — `tailCollisionFactor_le_rpow_tailEdgeExponent`

Parameters are exactly X.07's parameters, in the same order.

Conclusion:

`tailCollisionFactor N n M ≤ Real.rpow (N : ℝ) (tailEdgeExponent N n M)`.

Use the existing `tailCollisionFactor_le_tailSquareFactor n hn M hN` and X.07. This is an inequality, including the case of a zero fixed-count collision factor.

### Shared matrix parameter signature for X.09–12

The following is the complete ordered parameter list, expanded identically in each of X.09–12:

`{N K k A M : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hM : M ≤ K) (hAM : A ≤ M)`

`(w : Fin A → Fin k) (x : Fin M → Fin k) (b : ℝ)`

`(hprefix : ∀ t, x (Fin.castLE hAM t) = w t)`

`(hN : 2 ≤ N) (hx : legalPrefix n hM x)`.

X.10 and X.11 append their stated `δ` and small-size inequality after this list. There is no further matrix, probability, stable-family, concentration, or spatial premise.

### X.09 — `matrix_internal_density_le_ambient_tail_exponent`

Parameters: exactly the shared matrix signature.

Conclusion:

`D ≤ Real.rpow (N : ℝ) (4 * (L + ε) + 2 * E) / 4`.

This expands to the existing absolute density on the left and the three exact new exponent expressions on the right. Its proof starts from the previously proved `matrix_internal_density_le_mean_tail_fourth`, applies X.08 to the fixed-count tail factor, and uses X.05. It does not claim the printed `-c_F` spatial improvement.

### X.10 — `matrix_internal_density_le_small_coarse_exponent`

Parameters: the shared matrix signature, followed by

`(δ : ℝ) (hsmall : ambientSizeExponent N n hM A b x < 2 * δ)`.

Conclusion:

`D ≤ Real.rpow (N : ℝ) (2 * E + 8 * δ + 4 * ε) / 4`.

This follows from `4*L < 8*δ`. It holds for every legal prefix satisfying the displayed source size classification, without a singleton/non-singleton premise. There is no claim that `L+ε` itself is below `2δ`.

### X.11 — `matrix_internal_density_le_small_singleton_exponent`

Parameters: exactly X.10's parameters, in the same order.

Conclusion:

`D ≤ Real.rpow (N : ℝ) (2 * L + 2 * E + 4 * δ + 4 * ε) / 4`.

This follows from `4*L < 2*L+4*δ`. The name identifies its intended application to the source's small singleton estimate; the exact finite theorem applies to all small legal prefixes, so no unimplemented stable-family predicate is assumed. The four copies of the ambient discrepancy are retained. Replacing `4*ε` by `2*ε` or by an unspecified `o(1)` is not part of this statement.

For X.10 and X.11, `δ` is any real number satisfying the displayed inequality with `L`; no separate `δ>0` premise is needed for the algebra. The source's positive-`δ` setting is included.

### X.12 — `matrix_internal_density_le_ambient_size_exponent`

Parameters: exactly the shared matrix signature, with no `δ` or small-size hypothesis.

Conclusion: `D ≤ Real.rpow (N : ℝ) (L + ε)`.

Use the already proved `matrix_internal_density_le_prefixMean` and X.05. This strengthens the applicability of the terminal route without modifying any earlier theorem.

### X.13 — `tailEdgeExponent_at_full_length`

Parameters:

`(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)`.

Conclusion: `tailEdgeExponent N n K = 0`.

This is the empty-sum identity. It requires no `hn`, `hN`, prefix, or legality argument. Real division is total; the numerator is zero even outside the logarithmic domain.

### X.14 — `matrix_internal_density_terminal_exponent`

Parameters:

`{N K k A : ℕ} (n : Fin K → Fin k → ℕ)`

`(hn : ∀ j, ∑ a, n j a = N) (hA : A ≤ K)`

`(w : Fin A → Fin k) (x : Fin K → Fin k) (b : ℝ)`

`(hprefix : ∀ t, x (Fin.castLE hA t) = w t)`

`(hN : 2 ≤ N) (hx : legalPrefix n (Nat.le_refl K) x)`.

Conclusion:

`edgeDensity (matrixLaw n hn) N (sortedRows n) (prefixWord x) ≤`

`Real.rpow (N : ℝ) (ambientSizeExponent N n (Nat.le_refl K) A b x +`

`  ambientMeanError N n hA w b)`.

This is the full-length specialization of X.12. Together with X.13 it explicitly supplies the source's terminal `c_E=0` case. No small-mean hypothesis is used. Equality of length-bound proof terms, if needed, is resolved by proof irrelevance rather than by a premise.

### X.15 — `ambientMeanError_root`

Parameters:

`(N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)`

`(w : Fin 0 → Fin k) (hN : 2 ≤ N)`.

Conclusion: `ambientMeanError N n (Nat.zero_le K) w 1 = 0`.

The existing empty-prefix mean is exactly `N`; hence the whole-deck choice `b=1` has exactly zero correction. No `hn` or extra legality premise is needed for the empty prefix. This checks the sign and normalization against the source's root convention.

## 5. Complete proof dependency plan and local auxiliaries

No additional named declaration is proposed. Bounds, product positivity, finite reindexing, power algebra, and every indicator-free scalar case below remain local proved steps inside the fifteen theorems.

1. **X.01:** specialize legality at `Fin.castLE hAM t`; use `hprefix` and the equality of composed `Fin.castLE` indices. This is a pointwise prefix relation, not an assumed mean relation.
2. **X.02:** derive positivity of `(N:ℝ)` and all selected count casts. Apply positivity of each selected ratio and of the finite product in `prefixMean`. The empty-prefix case uses the empty product.
3. **X.03:** prove the product factors nonzero from legality; apply trusted `Real.log_mul` and `Real.log_prod`. For each factor, `Real.log_div` proves `log(n/N)=-log(N/n)` from the two nonzero casts. No normalization of the counts is used.
4. **X.04:** apply X.03 to `x` and to `w`, using X.01 for the latter. Split the `Fin M` log-cost sum at `t.val<A` versus `A≤t.val`. Reindex the former part by the embedding `Fin.castLE hAM : Fin A → Fin M`; prove both membership directions, injectivity, surjectivity onto that initial segment, and equality of the summands using `hprefix`. The resulting finite sum identity and real subtraction prove the extension formula. The cases `A=0` and `A=M` are included by empty filtered sums; no arbitrary element is selected.
5. **X.05:** expand the two exponent definitions and use X.04 to obtain `L+ε = log μ_x / log N`. Prove `μ_x>0` via X.02 and `log N≠0` from `hN`. Trusted positive-base `Real.rpow_def_of_pos` and `Real.exp_log` (or `Real.rpow_logb` with its proved base conditions) then give the identity.
6. **X.06:** `hn` and `hN` imply a positive sum of natural counts, hence the existence of one positive count. Its squared normalized proportion is positive, and all other summands are nonnegative. This derives the condition needed for the logarithm, including alphabets with zero-count digits.
7. **X.07:** every included square sum is positive by X.06. Its finite product is positive, and trusted `Real.log_prod` identifies the product logarithm with the sum of the column logarithms. Unfold `columnPsiTwo` and `tailEdgeExponent`; the two minus signs give `log(tailSquareFactor)/log N`. Positive-base logarithm inversion proves the claim. Empty tails give `1=N^0`.
8. **X.08:** apply the already proved fixed-count tail comparison and X.07; no new approximation or error is needed.
9. **X.09:** use existing C.54. Existing tail nonnegativity and X.08 justify squaring the tail comparison. Replace the mean with X.05; convert natural powers of positive real powers using trusted `Real.rpow_natCast`, `Real.rpow_mul`, and `Real.rpow_add`. Ordinary real-ring normalization gives `4*(L+ε)+2*E`; division by four preserves the inequality.
10. **X.10–11:** apply X.09. The displayed linear inequalities follow from `hsmall`; trusted `Real.rpow_le_rpow_of_exponent_le` applies because `1≤(N:ℝ)`. Division by four is positive. No sign bound on `L`, `E`, `ε`, or `δ` is used.
11. **X.12:** rewrite the already proved mean density bound using X.05.
12. **X.13:** prove the full-length tail filter empty from each `j.isLt`; simplify the finite sum and zero division.
13. **X.14:** specialize X.12 at `M=K` and `hM=Nat.le_refl K`; the ambient bound proof reduces by proof irrelevance.
14. **X.15:** use the existing exact empty-prefix mean and `log N≠0` to simplify `log N/log N-1`.

The principal dependency paths are

`X.01 → X.04`, `X.02 → {X.03, X.05}`, `X.03 → X.04 → X.05`,

`X.06 → X.07 → X.08`,

`{X.05, X.08, existing C.54} → X.09 → {X.10, X.11}`,

`{X.05, existing C.55} → X.12 → X.14`, with `X.13` providing the terminal tail equality and `X.15` the independent root normalization.

Proposed files: `Exponent/Model.lean` for the five definitions; `Exponent/Mean.lean` for X.01–05 and X.15; `Exponent/Tail.lean` for X.06–08 and X.13; and `Exponent/Estimates.lean` for X.09–12 and X.14. The two mathematical conversion branches can be implemented independently after the definitions compile and the inventory is frozen.

## 6. Boundary cases and assumptions audit

- **`N=0` or `N=1`:** logarithmic conversion theorems deliberately require the source's large-`N` domain `N≥2`. The existing finite density estimates still cover these sizes unchanged. X.13 is purely an empty-sum identity and therefore remains stated for all `N`.
- **Empty prefix or ambient:** legal-prefix predicates are vacuous at length zero. Empty products and sums are used without selecting a digit. X.15 certifies the source root correction is exactly zero at `b=1`.
- **`A=M`:** there are no extension costs, so `L=b`; X.05 still yields the actual mean through the explicit ambient discrepancy. No assumption that the ambient size equals `N^b` is made.
- **`M=K` or `M>K` in a pure tail statement:** the tail is empty. X.07 allows arbitrary `M`; X.13 and X.14 explicitly cover the full-length source case. Actual prefix theorems keep `hM:M≤K`.
- **`K=0`:** all source prefixes and ambients have length zero. With `N≥2`, the empty matrix sample space remains valid; the mean and tail identities reduce to the root and empty-tail formulas.
- **Empty alphabet:** if a column exists, `hn` and `N≥2` cannot both hold. The proof of X.06 derives a positive count from those premises and does not add `k>0`. With no columns and an empty prefix, every formula is still defined.
- **Zero piles away from the selected prefix:** allowed. They contribute zero to square sums without obstructing positivity of the total square sum. A zero selected prefix pile is excluded precisely by source legality, rather than by a new uniform lower bound.
- **A selected pile of size one:** allowed. Its logarithm is finite. The fixed-count pair factor may be zero, and the already proved density estimate may vanish; no positive pair-factor premise is added.
- **Zero tail collision factor:** allowed. It is bounded by the strictly positive square-proportion tail product. Taking its logarithm or equating it to `N^E` would be incorrect and is not done.
- **Degenerate one-pile columns:** allowed. Their square sum is one and their `columnPsiTwo` is zero. The exponent need not be strictly negative, even for a nonempty tail.
- **Arbitrary ambient error:** retained with its sign and coefficient. The small bounds contain `4*ε`, and the terminal/mean bound contains `ε`. No absolute value, positive part, bound, or asymptotic rate is inserted.
- **Ambient and child means:** remain expectations under the same original-`N` full matrix law. No random reduced population, conditional law, or independent resampling of the ambient block is introduced.
- **Stable-family cases:** X.10 and X.11 are exact bounds valid for all legal prefixes with the source size-exponent inequality. They do not prove that a stable family is a singleton, supply the printed negative `c_F` factor, or establish a relative-coordinate window estimate.

## 7. Independent design conclusion

The proposed identities preserve the printed exponent definitions and record the only finite ambient discrepancy explicitly. The final bounds follow from already proved finite density estimates and trusted real logarithm/power calculus. I found no need for an assumed mean-power identity, a positivity premise beyond source legality and `N≥2`, a supplied asymptotic rate, or another named helper. The inventory is ready for independent mathematical and hidden-assumption comparison before a new freeze.

## 8. Final independent comparison and acceptance

After completing this inventory, I read `exponent_contract_reconstruction.md` and `exponent_contract_assumptions.md` in full. Both agree with its definitions, exact signed ambient correction, tail-square identity, two small-case coefficients, and terminal interpretation. The root-selected final inventory remains exactly X.D01–05 and X.01–15 with the four-module layout above.

The reconstruction report offers a different decomposition: a named raw product-split lemma and a named equality `L+ε=log μ_x/log N`, with terminality handled by specialization. The chosen inventory instead names source legality inheritance and the full-prefix logarithmic formula, proves the finite sum split locally in X.04, proves the scalar ratio equality locally in X.05, and includes the explicit terminal specialization X.14. These are alternative proofs of the same mathematical facts; neither route needs a new premise.

In particular, the local split in X.04 is sufficient. Let the full-prefix cost function be the actual real log cost in X.03. Trusted `Finset.sum_filter_add_sum_filter_not` partitions its sum using the predicate `A ≤ t.val`. The complementary indices satisfy `t.val < A`. The map `Fin.castLE hAM : Fin A → Fin M` is a bijection onto that complement: membership follows from the source index bound, injectivity from equality of values, and surjectivity uses the existing value with the proved bound `< A`. For each mapped index, the full-column embeddings agree by `Fin.ext rfl`, and `hprefix` identifies the selected digits. A local `Finset.sum_bij` proof therefore identifies the complementary sum with the ambient cost sum. Substituting the two already proved X.03 identities and rearranging subtraction gives X.04. This argument covers `A=0` and `A=M` through empty sums and requires no raw product-split declaration.

The remaining comparison decisions are exact:

- `ambientSizeExponent` remains the source `b` minus the literal extension-cost sum. It is not replaced by the derived logarithmic expression.
- `ambientMeanError` is computed from the existing deterministic mean, with unrestricted sign and no asymptotic bound. The local cancellation of `b` in X.05 proves an identity; it does not choose a new value of `b`.
- X.07 identifies the positive tail square product with the real power. X.08 retains only the valid inequality for the possibly zero fixed-count tail factor. Neither adds positivity of the latter or a nonempty-alphabet premise.
- X.10 and X.11 retain exactly the cutoff `L<2δ`, arbitrary real `δ`, the denominator `4`, and the errors `4*ε`. The exponents remain `2*E+8*δ+4*ε` and `2*L+2*E+4*δ+4*ε` respectively. No singleton classification or spatial saving is inferred.
- X.12 is the all-prefix mean-power bound; X.14 supplies its explicit terminal specialization, and X.13 gives the terminal `E=0` identity. X.15 deliberately freezes the source whole-deck convention `b=1`; the reconstruction report's broader root formula `1-b` can be established locally if needed but is not another planned declaration.
- Pure algebra keeps its listed omission of `hn`; actual-matrix estimates retain the original feasibility proof. Ambient legality is derived from `hx` and `hprefix`. No mean positivity, logarithmic identity, product split, or exponent conversion is assumed as a hypothesis.
- All bounds concern the unchanged absolute-coordinate density. Neither report supplies a relative-coordinate bridge, and none is included or assumed here.

**Final acceptance:** the five definitions and fifteen theorem signatures are complete and unchanged. The local sum split and local scalar ratio identity suffice; no additional named helper, definition, instance, or hypothesis is needed. No Lean code has been written for this addendum, and every earlier frozen artifact remains unchanged. The statement report is ready for hashing and freeze.
