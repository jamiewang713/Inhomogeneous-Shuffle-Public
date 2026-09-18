# Ordered actual profile-count limit: exact statement review

**Approve CL1–CL3 and all five proof-local schemas without corrections.**

Reviewed candidate: `audit/PROFILE_COUNT_LIMIT_STATEMENTS.md`, SHA-256 `6a8326d663ffd3107f3078154edaf7f9457970da62ed5fcab505e66c586a3f83`. There are exactly three proposed exported theorems and no new definitions. This review does not implement them or freeze their statements.

I independently reread the authorized unified article's profile-estimate cutoff, bad-profile counting statement and proof, and first-moment class-count application. I inspected the actual definitions and theorem binders in `FirstMoment/Counting.lean`, `FirstMomentModel/BoundaryEncoding.lean`, `FirstMomentModel/ProfileClasses.lean`, `Riffle/Definitions.lean`, and `RiffleTimeProfile/AnalyticParameters.lean`. The algebra and adversarial reviews were compared after this source and type inspection; all three reviews agree.

## Literal interfaces and dependencies

The proposed namespace `InhomogeneousShuffle.FirstMoment.Model` resolves the enclosing `profileCountBound` and `profileCount_exp_bound` from `InhomogeneousShuffle.FirstMoment`. The model-dependent definitions in this namespace already provide `boundaryBudget`, `exceptionalBudget`, `ProfileWord`, `ProfileClass`, and `profileClass_card_le`. Importing `FirstMomentModel.ProfileClasses` and `RiffleTimeProfile.AnalyticParameters` supplies these interfaces and the literal `TimeProfile.exceptionalAllowance` definition. No model, setup, class finiteness, or profile-compatibility binder is implicit in the three generic counting declarations.

CL1's explicit natural binders `k d`, its five real parameters `T a b tb te`, its seven printed positivity/nonnegativity premises, and the final positive real `eps` are valid as stated. The quantified finite data are exactly `N K qb qe : ℕ`, after the single natural threshold. The three inequalities use real casts on their natural left sides. The conclusion uses a real cast on the natural `profileCountBound`, and a real power of the positive natural base cast `(N : ℝ)`. The premises `ha` and `hb` must remain even if a particular implementation does not use them.

CL2 has exactly the same initial `k T C eps hk hT hC heps` package specified in its candidate. The displayed minimum, inverse, logarithm, square root, and floors all have the intended types: the minimum is in ℝ, both floor arguments are real, and `Nat.floor` returns the natural budgets expected by `profileCountBound`. The exceptional allowance is exactly `1 / Real.sqrt (Real.log (1 / chi))`. There is no confusion with a different partition regularity constant: `C` here is the fixed boundary-admissibility constant.

CL3 repeats precisely CL2's initial binders and premises. Its later universal quantification over `D : Riffle.Model`, then `A : Riffle.Setup D`, then the dependent maps and route is well formed. In particular, the route's domain is exactly

`ProfileWord A good (TimeProfile.exceptionalAllowance chi)`.

The realized class on the conclusion's left side has that same domain, cutoff, cell map, good predicate, and route. `c` is a natural codomain dimension, not the already digit-expanded dimension. Consequently the earlier exact theorem must be applied with final count dimension `c * D.k`, and CL2 must be instantiated at `d = c * k`.

The existing theorem supplying the finite step is exactly:

`InhomogeneousShuffle.FirstMoment.Model.profileClass_card_le A cell good alpha route`.

Its conclusion bounds `Nat.card (ProfileClass A cell good alpha route)` by

`profileCountBound D.K D.k (boundaryBudget A) (exceptionalBudget A alpha) (c * D.k)`.

It does not request a `Finite` instance or an additional legal-word premise. The map codomain and route types in CL3 match this theorem directly. After obtaining its natural inequality and casting it into ℝ, the equalities `D.k = k`, `A.C = C`, and `A.chi = chi` rewrite only the numerical right-hand side. This avoids unnecessary transport of the dependent domain or maps.

The resulting budgets are literally the CL2 budgets because

`boundaryBudget A = Nat.floor (A.C / Real.log (1 / A.chi) * Real.log (D.N : ℝ))`

and

`exceptionalBudget A alpha = Nat.floor (alpha * Real.log (D.N : ℝ))`.

No strengthened version of the `Setup` structure is needed; its other fields are universally quantified through `A`.

## Quantifier and inequality checks

The CL1 uniform threshold can be extracted from the already available logarithmic-polynomial estimate before any choice of finite `K`, `qb`, or `qe`. For `log N ≥ 1`, its depth premise implies

`K + 1 ≤ (T + 1) * log N`.

The fixed prefactor `4 * (k + 1)^2 * (T + 1)^(d + 3)` and fixed logarithmic exponent `d + 3` therefore supply a threshold independent of the later finite data. The trusted result already used by the frozen `profileCount_eventually` is `isLittleO_log_rpow_rpow_atTop`, combined there with `tendsto_natCast_atTop_atTop`. Reusing this proof-local argument establishes the requested uniformity; applying sequence-specific eventual conclusions and interchanging quantifiers would not.

The already proved `profileCount_exp_bound` supplies exactly the three terms

`2 * qb * log (1 / tb) + qe * log (1 / te) + k * K * (2 * tb + te)`.

The reciprocal logarithms are nonnegative under the printed weight premises, so all three finite budget substitutions have the correct inequality direction. The exact boundary coefficient two, exceptional coefficient one, and weight contribution `2 * tb + te` agree with CL1. Polynomial absorption contributes only the printed additive `eps` in its real exponent.

For CL2, a positive fixed weight at most one can be chosen from `k,T,eps` before chi. The choice can use `T + 1`, so there is no division by zero at `T = 0`. The two sparse-budget coefficients tend to zero as `chi` decreases: `C / log (1 / chi)` and `1 / sqrt (log (1 / chi))`. Hence the proposed chi threshold can be chosen independently of `d`. Once a particular chi and finite dimension are fixed, CL1 supplies their natural threshold. The order is exactly

`fixed k,T,C,eps → chi0 → chi → d or c → N0 → all finite data`.

No dimension bound uniform in chi is needed, and the statements do not incorrectly quantify an arbitrary dimension after choosing `N0`. The strict bound `chi0 < min 1 (1 / k)` ensures every admitted chi has a positive logarithm `log (1 / chi)`. For `N ≥ N0 ≥ 2`, both natural-floor arguments are nonnegative. `Nat.floor_le` then gives the precise two real inequalities required by CL1. The class domain retains its original real cutoff; flooring is used only for the proved encoder budget.

## Exact finite count and edge cases

The literal bound remains

`4 * (k + 1)^2 * (K + 1)^(d + 3) * sparseCount K k qb^2 * sparseCount K k qe`.

It counts both boundary codes, both terminal/crossing tags, all three stored lengths, every good-digit count, the labeled exceptional set, and the arbitrary route in `Fin 4`. No digit-label factor or boundary factor has been omitted.

All candidate edge cases remain valid: `K = 0`, `T = 0`, `d = 0`, `c = 0`, empty actual class domains, and floor budgets exceeding `K`. In the last case the already proved sparse-count formulas contain zero binomial terms above `K`, so no additional budget-versus-depth premise is justified. CL1 also permits `k = 0` and unit weights, whereas CL2 and CL3 retain their explicit source alphabet premise `2 ≤ k`. If `c = 0` and `K > 0`, the later universally quantified cell map has an empty type, as it should.

The source fixes its boundary constant before chi, then its finite mesh/partition counts before large N. The exact quantifiers preserve that order for our refined class encoder. CL3 bounds each actual class domain uniformly in its later data; it does not bound a union over all choices of setup, prefix, maps, or model. The three declarations establish only the counting contribution to the first-moment assembly. They do not assert bad-profile mass estimates, stochastic localization or density, a homogeneous cutoff, or variational input.

The two other reviews and this review approve the identical candidate hash and all five helper schemas. No type, assumption, coefficient, or quantifier correction is requested before freezing CL1–CL3.
