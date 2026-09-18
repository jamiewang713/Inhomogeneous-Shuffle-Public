# M: proposed fixed-column moment contract

This contract uses exactly the shared `RiffleLower.FiniteLaw`, real probability, expectation, variance, uniform law, base-column array, sample space, row words, and word-count definitions in `contract-candidate.md`. It introduces no probabilistic assumptions beyond that concrete finite model. It is not yet frozen.

## Definitions owned by this module

* `ColumnArray N K k := Fin K → Fin N → Fin k`.
* `ColumnRandomness N K := Fin K → Equiv.Perm (Fin N)`.
* `columnCount c t a := (Finset.univ.filter (fun i => c t i = a)).card`.
* `rowWord c ω i := fun t => c t (ω t i)`.
* `wordCount c w ω := (Finset.univ.filter (fun i => rowWord c ω i = w)).card`.
* `wordMass c w := ∏ t, (columnCount c t (w t) : ℝ) / (N : ℝ)`.
* `wordMean c w := (N : ℝ) * wordMass c w`.
* `pairWordMass c w := ∏ t, ((columnCount c t (w t) : ℝ) * ((columnCount c t (w t) : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1))`.

All `N,K,k` are natural numbers. Every subtraction in a displayed real probability or moment expression occurs after casting to `ℝ`. An indicator is real-valued `if proposition then 1 else 0`. Predicate events mean `Finset.univ.filter` of the predicate. Empty products equal one. No lemma below excludes zero piles, deterministic columns, `K=0`, or repeated columns.

## Generic exact uniform counting helpers

M01. **`uniform_expect_equiv`**. For finite nonempty types `α,β`, an equivalence `e : α ≃ β`, and `f : β → ℝ`,

`expect (uniformLaw α) (fun a => f (e a)) = expect (uniformLaw β) f`.

M02. **`uniform_pi_expect_prod`**. Let `T` be finite, `A : T → Type` be finite nonempty coordinate types, and `f : ∀ t, A t → ℝ`. Then

`expect (uniformLaw (∀ t, A t)) (fun ω => ∏ t, f t (ω t)) = ∏ t, expect (uniformLaw (A t)) (f t)`.

M03. **`uniform_perm_indicator`**. For `N>0`, `S : Finset (Fin N)`, and `i : Fin N`,

`expect (uniformLaw (Equiv.Perm (Fin N))) (fun σ => if σ i ∈ S then 1 else 0) = (S.card : ℝ) / (N : ℝ)`.

M04. **`uniform_perm_pair_indicator`**. For `N≥2`, `S : Finset (Fin N)`, and `i,j : Fin N` with `i ≠ j`,

`expect (uniformLaw (Equiv.Perm (Fin N))) (fun σ => (if σ i ∈ S then 1 else 0) * (if σ j ∈ S then 1 else 0)) = ((S.card : ℝ) * ((S.card : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1))`.

M05. **`indicator_sum_factorial`**. For a finite type `I` and predicate `B : I → Prop`, put `Y := (Finset.univ.filter B).card`. Then

`(Y : ℝ) = ∑ i, if B i then 1 else 0`,

and

`(Y : ℝ) * ((Y : ℝ) - 1) = ∑ i, ∑ j, if i ≠ j ∧ B i ∧ B j then 1 else 0`.

These are the only general exchangeability/counting helpers planned for the moment implementation. Permutation symmetry can be proved inside M03/M04 using right composition by a transposition. There is no need to assume independence of row indicators.

## Concrete column and word identities

M06. **`columnCount_le` / `sum_columnCount`**. For every `c,t,a`, `columnCount c t a ≤ N`; and for every `c,t`, `∑ a, columnCount c t a = N`.

M07. **`wordMass_bounds` / `wordMean_bounds`**. Under `0<N`,

`0 ≤ wordMass c w ∧ wordMass c w ≤ 1`,

`0 ≤ wordMean c w ∧ wordMean c w ≤ (N : ℝ)`.

M08. **`word_row_probability`**. Under `0<N`, for each `i : Fin N`,

`prob (uniformLaw (ColumnRandomness N K)) {ω | rowWord c ω i = w} = wordMass c w`.

M09. **`word_two_rows_probability`**. Under `2≤N`, for each distinct `i,j : Fin N`,

`prob (uniformLaw (ColumnRandomness N K)) {ω | rowWord c ω i = w ∧ rowWord c ω j = w} = pairWordMass c w`.

M10. **`wordCount_expect`**. Under `0<N`,

`expect (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ)) = wordMean c w`.

M11. **`wordCount_factorial_second_moment`**. Under `2≤N`,

`expect (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ) * ((wordCount c w ω : ℝ) - 1)) = (N : ℝ) * ((N : ℝ) - 1) * pairWordMass c w`.

## Nonpositive covariance and finite lower tail

M12. **`one_column_pair_le_square`**. For naturals `d,N`, assuming `2≤N` and `d≤N`,

`0 ≤ (d : ℝ) * ((d : ℝ)-1) / ((N : ℝ)*((N : ℝ)-1))`,

`(d : ℝ) * ((d : ℝ)-1) / ((N : ℝ)*((N : ℝ)-1)) ≤ ((d : ℝ)/(N : ℝ))^2`.

M13. **`pairWordMass_le_square`**. Under `2≤N`,

`0 ≤ pairWordMass c w ∧ pairWordMass c w ≤ (wordMass c w)^2`.

M14. **`wordCount_variance_le_mean`**. Under `2≤N`,

`variance (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ)) ≤ wordMean c w`.

M15. **`wordCount_lower_tail`**. Under `2≤N`, for any natural `m` satisfying `(m : ℝ)<wordMean c w`,

`prob (uniformLaw (ColumnRandomness N K)) {ω | m ≤ wordCount c w ω} ≥ 1 - wordMean c w / (wordMean c w - (m : ℝ))^2`.

This is a direct application of shared P14 after M10 and M14. It must not import a hypergeometric concentration theorem or require positive pile proportions. The Chebyshev error is deliberately weaker than the article's exponential estimate and is sufficient for the largest-full-word finite lower-bound endpoint.

## Dependency graph

* M01 depends on shared P05 and finite sum reindexing.
* M02 depends on P05 and the finite product-of-sums identity.
* M03 depends on M01 and double counting a permutation's selected positions.
* M04 depends on M01, M03, and double counting selected ordered pairs; transpositions fixing one index suffice.
* M05 and M06 are finite counting identities.
* M07 depends on M06 and elementary nonnegative product bounds.
* M08 depends on M02, M03, and the equivalence of word equality with equality at every coordinate.
* M09 depends on M02, M04, and the same coordinatewise equality equivalence.
* M10 depends on M05, M08, and expectation of a finite sum.
* M11 depends on M05, M09, and expectation of a finite sum.
* M12 is elementary real arithmetic, including the cases `d=0,1`.
* M13 depends on M06, M12, and the product of inequalities.
* M14 depends on M10, M11, M13, and shared P11/P13.
* M15 depends on M10, M14, and P14.

## Independent review of the shared candidate

P01–P08 and P11–P14 are valid for exactly the displayed hypotheses. In P13, no nonnegativity assumption on the random variable is needed; expanding `f(f-1)` proves the conclusion algebraically. In P14, `m<μ` makes the denominator strictly positive. P09/P10 require the stated nonnegative errors; their proof should use error probabilities or split the case `δ≥1`, avoiding multiplication of inequalities by `1-δ` without a sign check.

The fixed-column construction is correct and carries independence of columns by construction. `HasIncreasingRun` specifies both endpoints indirectly: `a≤i.val`, `i<j`, and `j.val<a+m` imply both indices lie in the interval. `1≤m≤N` makes the number of admissible starts exactly `N-m+1`, so the sharper L01/L02 union factor is valid.

L01 and L02 are mathematically valid with the displayed assumptions and the preceding proved modules. They do not assert an inhomogeneous asymptotic cutoff. L02 has the necessary common observable event, so it does not commit the invalid inference that a mixture of laws far from uniform must be far from uniform.

The column-count sum is a theorem about the concrete column function, not literally a definitional reduction. This wording has no mathematical impact, but the formal module explicitly includes M06 so it cannot silently enter as an assumption.

## Independent review of the other module contracts

I approve U01–U08 in `threshold-audit.md` with exactly their displayed definitions and assumptions. U01 requires injectivity for uniqueness of the sorting permutation. U03 is correctly a count times `m!`, including `m=0`; U04 divides by positive factorials. U05's finite union has precisely `N-m+1` starts when `m≤N`. U07 does not require the positions to be numerically ordered. U08 uses only linearity and does not silently assume independence. The proposed extension of a permutation from an embedded subset is a valid bijective proof device.

I approve sorting statements S1–S4 (numbered 1–4), digit statements D1–D4 (numbered 5–8), and cold finite statements C1–C3 (numbered 9–11) in `reconstruction.md`, with the following exact reading already present there: keys have a linear order; `C_f,L_f` count original labelled rows; the output is `Tuple.sort f`, not its inverse; the full-word run uses `1≤m≤C_f(w)`; all finite cell products have natural count exponents; the logarithmic lemma requires positivity only at selected coordinates; cold localization is an explicit deterministic premise, not an imported probabilistic theorem. The exponent identity has no sign or range assumptions. The collision-to-edge injection uses `C_f(w)≥2`, so its first two fiber positions exist and are adjacent. These statements do not make a cold-spot asymptotic assertion.

These approvals concern every proposed mathematical statement in the three other modules. No unlisted top-level lemma is authorized. Intermediate facts may be local `have` statements proved inside frozen theorem proofs; additional exported helpers require a separately reviewed extension contract.
