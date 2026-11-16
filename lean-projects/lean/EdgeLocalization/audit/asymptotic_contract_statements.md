# Proposed asymptotic ambient-size contract

This is an independent pre-code design of exactly **one definition and seven theorems**, A.D01 and A.01–07. No new Lean implementation is authorized by this report. All existing mathematical sources, definitions, proofs, and frozen contracts remain unchanged.

## 1. Source meaning and bounded scope

I reread the permitted TeX at 478–517, the edge-density lemma and its small cases at 1486–1642, and the terminal lemma at 1644–1660. I also reread the old homogeneous paper's size/tail definitions in §4.1.3 and the fixed-column paper's equations (4.11)–(4.15), its small-block and singleton estimates (4.22)–(4.23), and their proof. The source ambient hypothesis is the statement at TeX 494–498 that the **actual expected occupancy** of the fixed ambient prefix is `N^(b+o(1))`. The normalization in the definition of `c_L` is still the original population `N`.

The earlier finite exponent addendum preserved the exact discrepancy

`ambientMeanError N n hA w b = log(prefixMean N n hA w) / log N - b`.

The present addendum derives eventual smallness of that computed discrepancy from the source expected-occupancy hypothesis. It then absorbs the discrepancy in the already proved relative-density conclusions. The single threshold is chosen before any child length or child prefix, so the conclusion is uniform over all legal extensions of the fixed ambient prefix at each population. No estimate uniform over a varying family of different ambient words is asserted.

This does not reconstruct the source's fluctuation exponent or its negative-`c_F` spatial improvement. The fourth-power bound remains the proved count-based bound; its small specialization has the coarse exponent `2E+8δ`, and its singleton-shaped specialization has `2L+2E+4δ`. The terminal bound follows from the first occupancy moment. The relative coordinates and independent full-population matrix law remain those already formalized.

The source also records a length profile `A(N)/log N=r+o(1)` and nested fixed parameters. These are not needed for this numerical dependency: the frozen size exponent contains the actual ambient length, and the proof uses only the displayed expected-size condition. No new profile approximation or rate is assumed. The mathematical statements are consequences on a larger domain, not replacements for a source stable-family or concentration lemma.

## 2. Definition and namespace policy

All new declarations are in namespace `EdgeLocalization`; `Asymptotic` is only a module directory. There is no new family structure, instance, probability alias, expected-size alias, density alias, or error alias.

### A.D01 — `HasSizeExponent`

Exact parameters and type:

`(f : ℕ → ℝ) (b : ℝ) : Prop`.

Exact definition:

`∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →`

`  Real.rpow (N : ℝ) (b - ε) ≤ f N ∧`

`  f N ≤ Real.rpow (N : ℝ) (b + ε)`.

This is the explicit two-sided meaning of `f N=N^(b+o(1))` for an eventually positive function; the real exponent `b` may have either sign. It places no restriction on finitely many initial values of `f`, does not assume `f` positive everywhere, and contains no unproved log estimate. Real powers retain their existing trusted definition at every natural base, including zero. The later theorems explicitly choose a threshold at least two before taking the useful logarithmic inequalities.

## 3. Exact family data for A.02–07

The following is the complete common parameter list, in this order. All listed data and proofs are explicit parameters; `k`, `K`, and `A` are not implicit.

`(k : ℕ) (K A : ℕ → ℕ)`

`(n : ∀ N : ℕ, Fin (K N) → Fin k → ℕ)`

`(hn : ∀ (N : ℕ) (j : Fin (K N)), ∑ a, n N j a = N)`

`(hA : ∀ N : ℕ, A N ≤ K N)`

`(w : ∀ N : ℕ, Fin (A N) → Fin k)`

`(b : ℝ)`

`(hsize : HasSizeExponent`

`  (fun N => (matrixLaw (n N) (hn N)).expectation`

`    (fun ω => (occupancyCount N (sortedRows (n N) ω) (prefixWord (w N)) : ℝ))) b)`.

This hypothesis is on the actual expected sorted occupancy, not on a substitute independent occupancy law, on a random realized count, or on an assumed product mean. The already proved exact occupancy formula will identify it with `prefixMean` when needed.

The family is total on natural populations. Thus the column counts, their actual-population feasibility, ambient length proof, and ambient word are supplied also at `N=0/1`. No legality of the ambient word is imposed at those populations or at every population. The asymptotic definition ignores any finite initial segment, and every logarithmic or density conclusion below proves its own eventual cutoff `N0≥2`. This keeps both the low-population convention and the eventual domain visible.

An empty alphabet is not separately ruled out. A supplied family must satisfy exactly the already existing finite-model types and `hn`; no `Nonempty (Fin k)` or positive alphabet-size hypothesis is introduced. There is likewise no upper/lower restriction on the real exponent `b`.

For the statements below, `hM`, `hAM`, and the child word occur **after** the existential population threshold. They are quantified at the particular `N` under consideration, not as a preselected child family. The pointwise relation uses exactly the previous convention

`∀ t : Fin (A N), x (Fin.castLE hAM t) = w N t`.

## 4. Computed-error theorem inventory

### A.01 — `hasSizeExponent_eventually_log_error_le`

Exact parameters:

`(f : ℕ → ℝ) (b : ℝ) (hsize : HasSizeExponent f b)`

`(ε : ℝ) (hε : 0 < ε)`.

Exact conclusion:

`∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →`

`  |Real.log (f N) / Real.log (N : ℝ) - b| ≤ ε`.

No separate positivity premise on `f`, log-error premise, or assumed limit theorem occurs. The output supplies the cutoff needed to avoid the bases zero and one. The weak bound for every positive tolerance is the exact eventual-smallness property required below.

### A.02 — `ambientMeanError_eventually_abs_le`

Exact parameters: the complete family list from §3, followed by

`(ε : ℝ) (hε : 0 < ε)`.

Exact conclusion:

`∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →`

`  |ambientMeanError N (n N) (hA N) (w N) b| ≤ ε`.

The error is the previously defined error, with the supplied ambient length proof `hA N`. The theorem derives its estimate from the source expected-occupancy condition via A.01 and the earlier exact expected sorted-occupancy formula. Ambient legality and eventual positivity are not extra hypotheses.

## 5. Uniform relative-density theorem inventory

In every theorem A.03–07 the parameters are exactly the common family list in §3 followed by `(ε : ℝ) (hε : 0 < ε)`. In A.04 and A.05, `δ : ℝ` is universally quantified in the conclusion, after the existential threshold and after the population and its threshold proof. Its sign is not restricted.

In every conclusion, the existential threshold precedes `N` and all child data. In the two small wrappers it also precedes `δ`. Consequently, a threshold cannot depend on `δ`, the child length, child word, its coordinate prefix proof, or its legality proof. The proof of the two small wrappers can choose the same threshold as A.03.

The common child binder list for A.03–06 is exactly

`∀ (M : ℕ) (hM : M ≤ K N) (hAM : A N ≤ M)`

`  (x : Fin M → Fin k)`

`  (hprefix : ∀ t : Fin (A N), x (Fin.castLE hAM t) = w N t)`

`  (hx : legalPrefix (n N) hM x),`.

In A.03 and A.06 this list follows `∀ N : ℕ, N0 ≤ N →` directly. In A.04 and A.05 the exact order is first `∀ N : ℕ, N0 ≤ N → ∀ δ : ℝ,` and then this common child list. A.04 and A.05 additionally quantify, after `hx`,

`(hsmall : ambientSizeExponent N (n N) hM (A N) b x < 2 * δ)`.

No new named notation is introduced. The following displays retain the full formula rather than hiding the shift in a new definition.

### A.03 — `matrix_relative_density_eventually_le_ambient_tail_exponent`

Parameters: exactly the family and accuracy parameters specified above.

Conclusion: there exists `N0 : ℕ` with `2 ≤ N0`, such that for every `N ≥ N0` and every child binder in the common list,

`relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))`

`  (prefixWord x)`

`  (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤`

`Real.rpow (N : ℝ)`

`  (4 * ambientSizeExponent N (n N) hM (A N) b x +`

`    2 * tailEdgeExponent N (n N) M + ε) / 4`.

The exact logical outer form is

`∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ M hM hAM x hprefix hx, [displayed inequality]`,

where all inner binder types are exactly the common child list. There is no large-block, small-block, stable-family, or tail-sign premise.

### A.04 — `matrix_relative_density_eventually_le_small_coarse_exponent`

Parameters: exactly the family list followed by `(ε : ℝ) (hε : 0 < ε)`.

Conclusion: the exact outer form is

`∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ δ : ℝ,`

`  ∀ M hM hAM x hprefix hx hsmall, [displayed inequality]`,

where all inner binder types are exactly the common child list and small-cutoff binder above. The inequality is

`relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))`

`  (prefixWord x)`

`  (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤`

`Real.rpow (N : ℝ)`

`  (2 * tailEdgeExponent N (n N) M + 8 * δ + ε) / 4`.

The cutoff is exactly the frozen finite cutoff on `L`, not on `L` plus its ambient error. The conclusion is the coarse small-block bound and contains no asserted negative fluctuation exponent.

### A.05 — `matrix_relative_density_eventually_le_small_singleton_exponent`

Parameters and quantified hypotheses: exactly A.04's, in the same order.

The inequality is

`relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))`

`  (prefixWord x)`

`  (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤`

`Real.rpow (N : ℝ)`

`  (2 * ambientSizeExponent N (n N) hM (A N) b x +`

`    2 * tailEdgeExponent N (n N) M + 4 * δ + ε) / 4`.

This is the previously proved singleton-shaped inequality, valid for every small legal child. It neither assumes nor proves that a stable family is a singleton. The terminology is inherited from its existing finite theorem, without adding a source classification premise.

### A.06 — `matrix_relative_density_eventually_le_ambient_size_exponent`

Parameters: exactly the family list followed by `(ε : ℝ) (hε : 0 < ε)`.

Conclusion: the same outer existential threshold with `2 ≤ N0`, all `N ≥ N0`, and exactly the common child binder list, with no smallness binder, imply

`relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))`

`  (prefixWord x)`

`  (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤`

`Real.rpow (N : ℝ)`

`  (ambientSizeExponent N (n N) hM (A N) b x + ε)`.

There is no denominator and no extra tail exponent, exactly as in the finite occupancy bound.

### A.07 — `matrix_relative_density_eventually_terminal_exponent`

Parameters: exactly the family list followed by `(ε : ℝ) (hε : 0 < ε)`.

Exact conclusion:

`∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →`

`  ∀ (x : Fin (K N) → Fin k)`

`    (hprefix : ∀ t : Fin (A N), x (Fin.castLE (hA N) t) = w N t)`

`    (hx : legalPrefix (n N) (Nat.le_refl (K N)) x),`

`relativeEdgeDensity (matrixLaw (n N) (hn N)) N (sortedRows (n N))`

`  (prefixWord x)`

`  (fun ω => ambientLeft N (sortedRows (n N) ω) (prefixWord (w N))) ≤`

`Real.rpow (N : ℝ)`

`  (ambientSizeExponent N (n N) (Nat.le_refl (K N)) (A N) b x + ε)`.

There is no small-mean or singleton-family premise. The child has exactly full length. The already proved tail-exponent-zero identity remains available; no new terminal tail identity is declared.

## 6. Complete proof dependencies and local auxiliary plan

No named helper beyond A.01–07 is proposed. The following local steps cover the full proof inventory and its exceptional domains.

1. **A.01:** apply `hsize` at the given positive accuracy. If it returns a raw cutoff `N1`, use `N0=max N1 2`. For `N≥N0`, prove `N≥2`, `(N:ℝ)>1`, positivity of the natural base and its logarithm, and positivity of `N^(b-ε)` using trusted `Real.rpow_pos_of_pos`. The lower sandwich then proves `f N>0`; no choice of logarithm on a nonpositive eventual value is needed. Apply trusted `Real.log_le_log` to both sides of the sandwich, and `Real.log_rpow` to each power. Dividing the two inequalities by the proved positive `log N` gives `b-ε≤log(f N)/log N≤b+ε`. The trusted absolute-value inequality and real linear arithmetic give the conclusion. Neither a limit library nor an additional project log lemma is necessary.
2. **A.02:** apply A.01 to the exact expected-occupancy function displayed in `hsize`. For each `N`, the earlier `matrix_expected_sorted_occupancy (n N) (hn N) (hA N) (w N)` identifies this expectation with `prefixMean`. Rewrite this proved equality inside the logarithm and unfold only the existing `ambientMeanError` definition. No separate assumption on the product mean or ambient legality is introduced.
3. **A.03:** apply A.02 with tolerance `ε/4`, proving its positivity locally. Retain its threshold before introducing `N`, `M`, and the child. The output `N0≥2` and `N0≤N` give the finite theorem's `N≥2` premise. Apply the existing R.14 to this child and actual ambient shift. A.02 bounds the absolute ambient error, hence its upper value. The finite R.14 error uses `(hAM.trans hM)` while A.02 uses `hA N`; both are proofs of the same natural inequality, so proof irrelevance gives the definitionally equal error argument without a new hypothesis. Real arithmetic gives `4*(L+error)+2E≤4L+2E+ε`. Trusted power monotonicity at base `N≥2`, then division by positive four, completes the estimate.
4. **A.04:** use the threshold from A.03 at accuracy `ε`. For an arbitrary small child, `L<2δ` implies `4L≤8δ`. Compare the two exponents using trusted power monotonicity and retain `/4`. The threshold was chosen before the child; this proof requires no new threshold depending on its cutoff or on a profile count.
5. **A.05:** use the same A.03 route and the scalar consequence `4L≤2L+4δ` of the unchanged small cutoff. The constant four in front of `δ`, the tail coefficient two, and the requested accuracy remain exact.
6. **A.06:** apply A.02 with tolerance `ε`. Choose the threshold before introducing all child data. Apply the existing R.17 and compare `L+error≤L+ε`. There is no squaring, factor four, or dependence on the child's length in the error bound.
7. **A.07:** specialize A.06, after choosing its threshold, to `M=K N`, `hM=Nat.le_refl (K N)`, and `hAM=hA N`. Its conclusion is the frozen terminal formula. No `δ` or terminal smallness condition is needed, and no new named specialization helper is introduced.

The dependency graph is

`A.D01 → A.01 → A.02 → A.03 → A.04/A.05`,

`A.02 → A.06 → A.07`.

A.02 also uses the previously proved exact expected sorted occupancy formula; A.03 and A.06 use R.14 and R.17 respectively. All remaining arithmetic and logarithmic steps are local proofs using trusted mathlib.

Proposed modules:

- `Asymptotic/Model.lean`: exactly A.D01, importing only trusted real-power material as required;
- `Asymptotic/Error.lean`: A.01–02, importing the new model, the existing ambient error definition, and the exact matrix occupancy formula;
- `Asymptotic/Estimates.lean`: A.03–07, importing the new error theorems and the completed Relative estimates.

## 7. Uniformity and boundary audit

- **Accuracy and quantifiers:** every accuracy is explicitly positive. The threshold depends on the supplied ambient family, its exponent condition, and accuracy. It is chosen before the population, all child data, and, in the small wrappers, the arbitrary real `δ`. Thus both the child uniformity and the `δ` uniformity are stated in the theorem itself. Even an unbounded number of candidate lengths or prefixes at a growing population needs no union bound or cardinality estimate for this deterministic family of inequalities.
- **Different ambient families:** a separate `hsize` for every member of an additional ambient class does not by itself imply a common threshold across that class. No such stronger uniformity is encoded or claimed here. The finitely retained classes mentioned in the source would require a separate finite maximum argument if they are later formalized.
- **Low populations:** the data and definition are total on `ℕ`, including zero and one. Only finitely many initial values can be discarded by the explicit existential threshold. The proved `N0≥2` prevents division by a zero logarithm in the useful inequalities, without adding a low-population assumption to `HasSizeExponent`.
- **Nonpositive or zero means:** the lower positive power sandwich proves eventual positivity of the actual expected occupancy. A family with infinitely many zero expected ambient occupancies cannot satisfy the displayed `hsize`; this is a consequence of the source size hypothesis, not an extra legality condition. Isolated initial zero or negative values of a generic scalar `f` are harmless.
- **Empty alphabet/columns:** only the existing finite matrix family's well-formedness and actual-population count equations are assumed. Empty-column and empty-prefix cases are included. No extra inhabitance or positive-pile hypothesis appears in A.01–02. A.03–07 keep exactly the old finite child-legality premise where the source size exponent needs logarithms of selected piles.
- **Changing lengths:** `K` and `A` may be arbitrary natural-valued functions satisfying `hA`. No `O(log N)` condition is required for these scalar transfers. All children of lengths between `A N` and `K N` are covered after the same threshold.
- **Signs:** `b` and, where present, `δ` are arbitrary real numbers. The mean error remains signed; an absolute bound is proved and only its upper side is used for the density estimate. The strict cutoff on `L` is unchanged. No eventual positivity of `δ`, smallness of a realized occupancy, or sign assumption on the tail exponent is needed.
- **Null events:** the actual expectation and relative density are the existing finite sums. Nothing divides by the probability of an event or conditions on an occupied ambient block.
- **Coordinates:** the shift is still the samplewise strict-lexicographic ambient cut inside the full `N` law. The prior no-loss theorem certifies the source recentering at each outcome. No equality between absolute and relative squared densities is introduced.
- **Constants and source scope:** `/4` is retained in all three fourth-power consequences. The terminal and mean estimates have coefficient one and no denominator. No `O(δ)` or `o(1)` field hides an estimate: each eventual error is the explicit requested `ε`, and every coefficient of `L`, `E`, and `δ` is displayed. The negative-`c_F` gain, stable-block classification, concentration, endpoint windows, and exploration/aggregation arguments remain separate obligations.

The complete candidate is A.D01 and A.01–07 above. It is ready for independent reconstruction and hidden-case comparison before any implementation or additive freeze.

## 8. Statement-designer comparison and acceptance

After saving my independent inventory, I read the complete `asymptotic_contract_reconstruction.md` and `asymptotic_contract_assumptions.md` reports. They confirm the exact scalar hypothesis, the derived positivity and logarithmic control, the actual expected-occupancy interpretation, and the complete seven-theorem dependency route. Neither report identifies a need for an additional named helper or hypothesis.

The only pre-freeze quantifier choice was the position of `δ` in A.04–05. An earlier draft put it among the theorem parameters, which allowed a possibly different threshold for each `δ`. The root requested the stronger explicit joint uniformity. The selected signatures in §5 now quantify `δ` after `∃ N0` and after `∀ N ≥ N0`, immediately before the child data. Both independent reviewers confirm that the ambient-only error threshold proves this order: A.03 is selected before any `δ`, and its two scalar small-cutoff consequences need no new threshold. This is a pre-code selection, not an implementation-time change to a frozen theorem.

All three reports agree that the family hypothesis must remain on actual expected sorted occupancy. The product mean enters only through the previously proved exact identity. Eventual positivity follows from the lower power sandwich; no ambient-legality, positive-mean, rate, nonempty-alphabet, or log-error assumption is added. The threshold's proved lower bound two is sufficient for every logarithmic and power-monotonicity step while leaving arbitrary initial ambient behavior outside the eventual assertion.

The comparison preserves the exact source size exponent, full-population law and computed relative shift, all child proof arguments, signed finite error before absorption, strict small cutoff, coefficients, and denominators. It does not infer a common threshold over unrelated ambient families or over a class whose size and members change with `N`. Nor does it infer the negative-`c_F` improvement or the remaining source classifications and aggregation estimates.

**Statement-designer acceptance:** exactly A.D01 and A.01–07, with the displayed joint child/`δ` quantifier order, are mathematically accepted and ready for the root's final freeze after both reviewers' exact-inventory confirmations. No Lean code has been written and no earlier frozen artifact has been edited.
