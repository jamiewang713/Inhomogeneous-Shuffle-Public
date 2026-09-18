# Independent reconstruction of finite source specializations S01–S05

## Verdict and verification boundary

All five candidate statements in `FINITE_SOURCE_ADAPTERS_CANDIDATE.md` are mathematically valid with exactly their stated assumptions. No added positivity, ordering, support, measurability, stochastic, or asymptotic hypothesis is needed. The proof routes below specialize the existing frozen finite results; they do not change F01–F20.

This is a source review before adapter implementation. I read `RiffleTimeProfile.Base` and `RiffleTimeProfile.Ambient`, but have not independently compiled them against the pinned runtime. The parent reports that the time-profile project targets Lean 4.33.1 whereas the frozen finite implementation uses Lean 4.19.0, including a changed `StdSimplex` import path. Thus the listed TimeProfile declarations are inspected source interfaces, not a claim that these dependencies have already passed the current compiler/kernel checks. An isolated import-compatibility snapshot still needs verification; no new assumption is justified by a compatibility failure.

No Lean file was written or changed for this review.

## Source comparison

The current TeX definition at lines 277–299 gives exactly the four regularity clauses used in S01–S03. The proof of `lem:ub-regular-partition-interval-blocking`, lines 868–881, explicitly derives the good and exceptional digit bounds from those clauses. Its finite digit statements need no almost-like assumption: that assumption is used only for the later cell-count estimates.

The proof of `lem:ub-profile-estimates`, lines 945–963, separates tail replacement from maximal-pile domination. S02 and S03 stop at the finite target weights and retain the explicit empirical-cell discrepancies. They do not prove that these target weights are integrals.

The same proof, lines 965–992, compares a side cylinder at a crossing with the whole continuation cylinder and then takes square roots. S04 is the finite product argument behind this comparison. S05 retains the exact ambient discrepancy which the displayed asymptotic source formula suppresses.

The homogeneous proof in 2510.22783v1, Definition 4.3 and equation (4.5), PDF pages 18–19, supplies the same side-piece/continuation comparison; Lemma 4.8, PDF pages 23–24, supplies the representative and tail replacement argument. Its fluctuation maxima omit the first physical column and use the separate left/right boundary lengths. S04–S05 concern the existing TimeProfile maxima over `positions K w v`; they should not be described as an established identification with those older stochastic fluctuation variables. The 2103.05068v3 definitions and equations (4.1)–(4.3), PDF page 16, identify prefix counts with binomial variables only in that paper's independent-row model. No such law is required or established by these adapters.

## Common definitions and exact auxiliary deductions

Let `a(j) = TimeProfile.prob (p j) (x j)` and `L = TimeProfile.logScale N`.

* `positions K A B` is the finite set of `j : Fin K` with `A ≤ j.val < B` (`Ambient.lean:19`). Membership always supplies `j.val < B`; the type already supplies `j.val < K`.
* `LegalPrefix p x M` gives `0 < a(j)` whenever `j.val < M` (`Ambient.lean:22`). `TimeProfile.prob_nonneg` and `TimeProfile.prob_le_one` give `0 ≤ a(j) ≤ 1` for every column and digit, including unused coordinates (`Base.lean:24`, `Base.lean:27`).
* `N ≥ 2` gives `L > 0` through `TimeProfile.logScale_pos` (`Base.lean:122`) and also `N > 0`.
* The exact identity `TimeProfile.digitCost z = RiffleProfiles.cost z` follows from `one_div` and `Real.log_inv`. In mathlib's total-real logarithm convention it is true for every real `z`, including zero. This is an explicit definitional compatibility identity, not a relaxation of the positive-mass hypotheses of frozen log monotonicity or physical logarithm claims. At zero both sides equal zero; legal selected masses must still be supplied where required.
* Therefore `TimeProfile.cL N p x b w M` equals `RiffleProfiles.lengthExponent b (positions K w M) a L` exactly, by unfolding the two definitions.
* `TimeProfile.cE N p M` equals the negative of `RiffleProfiles.normalizedSum (positions K M K) (fun j => psi (p j) 2) L` exactly; converting `(-sum)/L` into `-(sum/L)` is only real arithmetic.

These are direct deductions from the frozen definitions and existing source interfaces. They introduce no external premise.

## S01 — regularity wrapper

**Reviewed assumptions:** arbitrary finite `J : Finset (Fin K)`; `chi > 0`; `P.IsRegular chi C`. Actual and representative selected masses are `a(j)` and `q(j) = prob (P.rep (P.classify (p j))) (x j)`.

**Reviewed conclusion:** `RiffleProfiles.RegularDigits J a q chi (C * chi)`.

Construct all three fields directly:

1. `threshold_pos` is the given strict positivity of `chi`.
2. For `j ∈ J` and `2*chi < q(j)`, apply `P.IsRegular.good_digit` with cell `P.classify (p j)`, simplex point `p j`, digit `x j`, and cell-membership equality `rfl`. It supplies `chi < a(j)` and the digit-cost error. Rewrite both digit costs using the common exact identity to obtain the frozen cost error.
3. For `q(j) ≤ 2*chi`, apply `P.IsRegular.exceptional_digit` at the same cell and digit to obtain `a(j) ≤ 3*chi`.

The pertinent declarations are `Base.lean:153`–163 and the already stated wrappers at lines 169–200. No legality assumption is needed to construct this regularity predicate: positive actual and representative masses at good positions follow from `chi > 0` and the strict threshold. Exceptional actual positivity must come from legality only when a later estimate requires it. In particular this wrapper adds no full-support condition and no condition `C ≥ 0`.

Frozen consequences F02–F04 are then available on the same finite set. Nonnegativity of exceptional cost still requires frozen `LegalOn`, derived from `LegalPrefix` for any such set lying below the legal prefix length. The regularity wrapper alone should not be presented as proving that nonnegativity premise.

## S02 — tail replacement

**Reviewed assumptions:** `N ≥ 2`; `P.IsRegular chi C`; arbitrary real arrays `m, delta` on `Fin P.cellCount`; for every cell, the displayed error bounds `|n_i/L - m_i| ≤ delta_i`, with `J = positions K M K`.

Apply frozen `RiffleProfiles.tail_cell_replacement` (F06/F08) with:

* position set `J` and cell map `j ↦ P.classify (p j)`;
* actual values `f(j) = TimeProfile.psi (p j) 2`;
* representative values `v(i) = TimeProfile.psi (P.rep i) 2`;
* uniform error `epsilon = C * chi`;
* the stated `m` and `delta` arrays; normalization `L`.

The representative error is exactly `P.IsRegular.psi_rep_error`, using `2 ∈ Set.Icc (2 : Real) 4` (`Base.lean:197`). Equivalently apply `psi_oscillation` with `P.classify_rep` for the representative. The count premise is the candidate premise after unfolding `n_i`. The sign conversion in the common deductions yields exactly

`|cE N p M + sum_i m_i * psi (P.rep i) 2| ≤ card(J) * C * chi / L + sum_i |psi (P.rep i) 2| * delta_i`.

No positivity of `chi`, `C`, `m_i`, or additional ordering of `M` is needed. F06 has no such premises. Any sign restriction forced by a nonempty regular cell or a nonempty discrepancy array is a consequence of the supplied hypotheses, not something to add to the theorem. For `M ≥ K`, the actual tail is empty and F06 still proves the resulting target bound.

## S03 — maximal-pile replacement

**Reviewed assumptions:** `N ≥ 2`; `P.IsRegular chi C`; `LegalPrefix p x M`; the candidate count errors on `J = positions K w M`. Target arrays remain arbitrary real arrays.

For `j ∈ J`, legality gives `0 < a(j)` because `j.val < M`. The source theorem `TimeProfile.prob_le_pileMax` (`Base.lean:42`) gives `a(j) ≤ pileMax (p j)`. Apply frozen `RiffleProfiles.maximal_pile_domination` (F09) to deduce

`cL N p x b w M ≤ b - sum_{j∈J} maxCost (p j) / L`.

Here the exact digit-cost/cost identity converts the selected costs and `maxCost` definition (`Base.lean:71`). Independently, F06 with `f(j) = maxCost (p j)`, `v(i) = maxCost (P.rep i)`, and `epsilon = C*chi` gives the target error from `P.IsRegular.maxCost_rep_error` (`Base.lean:192`). Apply `RiffleProfiles.maximal_pile_target` to the preceding one-sided bound and that absolute error. Its conclusion is precisely the candidate S03 statement, with the plus sign on the full error term.

No assumption `w ≤ M` or `M ≤ K` should be inserted. With `w > M` the position set is empty and the same argument is still valid; with `M > K` legality supplies all available selected coordinates and the set remains correctly truncated. No `k ≥ 2` premise is needed either: a supplied simplex already provides all required mass bounds. Maximal mass positivity is derivable from selected positivity, and the source also exports `pileMax_pos`; it is not a new hypothesis.

## S04 — crossing side mass

**Reviewed assumptions:** exactly `N ≥ 2`, `chi > 0`, `w ≤ v ≤ K`, `LegalPrefix p x v`, and one `j ∈ positions K w v` with `chi ≤ side (p j) (x j)`. The function `side` may be any real-valued function of the indicated type.

Let

`E = prefixMass N p x w * product_{h∈positions K w j.val} a(h)`

and let `Tj = positions K j.val v`. This continuation set contains **the crossing coordinate `j` itself** and all later coordinates below `v`. Membership of the witness supplies `w ≤ j.val < v`.

First establish the exact product factorization

`prefixMass N p x v = E * product_{h∈Tj} a(h)`.

To prove it, split `positions K 0 v` into the disjoint union of `positions K 0 w`, `positions K w j.val`, and `positions K j.val v`. Membership characterizations reduce the union/disjointness proofs to the natural inequalities already derived. Apply `Finset.prod_union` twice and reassociate the products. The same two-set argument also identifies `E` with `prefixMass N p x j.val`. The latter exact identity makes its positivity immediate from `prefixMass_pos`, or positivity follows directly from the product formula and legality.

The witness gives `chi*E ≤ E*side (p j) (x j) = sideMass N p x w side j`. Each continuation factor is in `[0,1]`. Frozen F10, `RiffleProfiles.side_mass_ge_continuation`, with set `Tj`, earlier mass `E`, and this side mass, yields

`chi * prefixMass N p x v ≤ sideMass N p x w side j`.

Legality and `N > 0` give `prefixMass N p x v > 0`; hence this side mass is strictly positive. Only now rewrite its coercion through `Real.toNNReal` using `Real.coe_toNNReal` and the derived nonnegativity. The finite-supremum membership bound `Finset.le_sup` shows that the value at `j` is at most `sideMaximum`. Coercion from NNReal preserves this order and proves the stated result.

It is unnecessary to assume that `side` is nonnegative at every other coordinate. Negative values elsewhere are truncated by `toNNReal`; the positive witness alone supplies the required lower bound. It is also unnecessary to divide by the selected crossing probability, so the proof introduces no additional nonzero denominator. Including that selected probability in `Tj` is essential: omitting it invalidates the claimed factorization.

## S05 — finite logarithmic comparison

**Reviewed assumptions:** exactly `N ≥ 2`, `chi > 0`, `w ≤ v ≤ K`, `LegalPrefix p x v`, and `Crossings p x w v chi`; `b` is any real number.

Set

`M = prefixMass N p x v`, `U = sideMaximum N p x w v leftProbability`, and `V = sideMaximum N p x w v rightProbability`.

1. `M > 0` follows from `TimeProfile.prefixMass_pos`. Apply S04 once to each component of `Crossings` (`Ambient.lean:69`), obtaining `chi*M ≤ U` and `chi*M ≤ V`. As `chi*M > 0`, both `U` and `V` are positive.
2. Frozen F11, `RiffleProfiles.fluctuation_log_comparison`, gives

   `(log M + log chi)/(2*L) ≤ min (log U/(2*L)) (log V/(2*L))`.

3. Positivity gives `sqrt U > 0` and `sqrt V > 0` by `Real.sqrt_pos`. Thus both `logExponent` branches are finite; neither equals bottom by its zero branch. For each maximum, use `Real.log_sqrt` with derived nonnegativity to obtain `log(sqrt U)/L = log U/(2*L)` and the analogous identity for `V`. This uses real arithmetic after the square-root logarithm identity; no positivity premise is silently discarded.
4. Rewrite `cF` using those two finite branches. Transfer the real inequality into `WithBot Real` via order-preservation of the coercion (`WithBot.coe_le_coe`), and commute the coercion with `min` (`WithBot.coe_min`). The result has the candidate's exact right-hand side.
5. The inspected source theorem `TimeProfile.cL_exact_mass_exponent` (`Ambient.lean:137`) has precisely the available premises and gives

   `log M/L = cL N p x b w v + (log(prefixMass N p x w)/L - b)`.

   Substitute this identity into the lower bound and regroup division to obtain the candidate left-hand side, coerced from Real into WithBot Real.

The ambient mass at `w` is itself positive by restriction of `LegalPrefix p x v`; no arbitrary-zero logarithm is used. The displayed ambient discrepancy is exact and may have either sign. It cannot be replaced by zero or an unspecified small term. The hypotheses imply that the relevant position set is nonempty; in degenerate cases `w = v` or `K = 0`, `Crossings` is impossible, rather than requiring another premise to exclude these cases.

## Freeze recommendation

Approve S01–S05 with the existing candidate assumptions and conclusions unchanged. The freeze should retain (i) the exact total-real compatibility identity separately from positive physical log uses, (ii) the crossing-inclusive continuation in S04, (iii) the exact ambient discrepancy and explicit WithBot coercion in S05, and (iv) the status of all targets as finite data. These details clarify the stated representation; they do not require modifying any candidate hypothesis.

This approval does not certify the current TimeProfile dependency sources under the pinned toolchain, identify side maxima with stochastic variances, identify prefix masses with shuffle expectations, prove a regular-partition construction, or supply any time measurability or integral bridge.
