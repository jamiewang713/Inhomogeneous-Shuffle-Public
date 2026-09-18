# Independent reconstruction of exact finite exponent conversion

I reread TeX 489–518 and 1486–1660, the one-column cost definition at 123–133, and the corresponding length/tail and singleton arguments in both permitted PDFs. The finite algebra below is valid under the original deterministic fixed-column model. It preserves the source's ambient length exponent and carries its exact mean discrepancy. It does not prove the obstructed spatial gain involving minus cF, introduce a profile approximation, or identify absolute density with randomly recentered density. No Lean implementation or earlier frozen file was changed.

## Source definitions and what is being converted

The source defines the logarithm to base N as the natural logarithm divided by log N (TeX 123). It defines psi_p(2) as minus the logarithm of the sum of the squared coordinates of p (133). For an ambient prefix w of length A, an extension x of absolute length M, and the source parameter b, its exact length formula is

`L = b − (sum over A≤j<M of log(N/n[j,x[j]])) / log N`.

This is TeX 503–506 in zero-based column indices. The tail exponent is

`E = − (sum over M≤j<K of psi_(n[j]/N)(2)) / log N`,

as at 513–515. The source does not define L to be exactly the base-N logarithm of the expected size: the ambient mean is specified only as N raised to b+o(1) at 492–508. Its exact finite discrepancy must therefore remain in the formula.

The homogeneous paper, PDF page 17, defines its root length exponent as 1+log_N(prefix mass) and its tail exponent as `(M−K)*psi_p(2)/log N` (extraction 942–954). Its PDF page 24, Lemma 4.12, derives the conditional internal-edge bound by counting equal pairs of strings. The fixed-column paper, PDF page 23, equation (4.11), uses the same exact tail sum but a profile-grouped length exponent; Lemma 4.8 then relates that grouped exponent to log_N(expected size) only up to its explicit O(delta) approximation. Its proof on PDF page 24 first writes the exact log-mean difference between an extension and its prefix (extraction 1423–1439). We use the exact unified-TeX formula, not that older grouped approximation.

The fixed-column paper's Lemma 4.14 on PDF page 27 supplies the exact tail pair factor with denominator N(N−1), while Lemma 4.15(iv), PDF pages 28–29, obtains the small-singleton exponent 2L+2E through concentration and translation arguments (extraction 1693–1707 and 1765–1791). The unified source's terminal statement is explicitly at TeX 1640–1660. No separate terminal lemma from the older PDFs is needed or claimed here.

## Exact finite domain and notation

Take natural N,K,k,A,M with N≥2 and A≤M≤K. Let n be the existing array of nonnegative integer counts with each column sum equal to N. Let `w : Fin A → Fin k` and `x : Fin M → Fin k`, with x extending w coordinatewise. Require x to be legal: the actual selected count in every one of its M columns is positive. Legality of w follows from this extension and need not be a separate hypothesis. Neither legality condition asserts that a random realization actually contains such a row.

N≥2 is the explicit finite version of the source's large-N domain. It proves N>0, N≠1, and log N>0, giving a valid logarithm base and monotonic real powers. The previous all-size finite estimates remain unchanged; the new exponent conversion simply applies them on this stated domain. No positivity of every pile, bound on k or K, profile convergence, good-shuffle assumption, stability assumption, or bound/sign on b is needed.

Write mu_x for the existing `prefixMean N n hM x` and mu_w for `prefixMean N n (A≤K) w`. Every ratio N/n and n/N in a logarithm is real division after casting both natural numbers. Natural division would not represent the source formula. Define the exact ambient mean error

`epsilon_w = log(mu_w)/log N − b`.

This error can have either sign. We do not assume it is zero, positive, small, or uniformly bounded. An eventual source-level assertion epsilon_w=o(1) would require a separately proved asymptotic statement; it is not a new premise of this finite conversion.

## Proposed definition inventory

The following five definitions suffice; names can be fixed by the independent statement designer before a new freeze.

1. `LegalPrefix n hM x`: every selected actual count `n (Fin.castLE hM t) (x t)` is positive. This definition depends on the count array, its prefix length bound, and the word, but not on N or a law.
2. `columnPsiTwo N counts`: minus `Real.log` of the sum over digits of `(singleFactor N counts digit)^2`. This is precisely source psi at parameter 2; no general real-parameter pressure function is needed.
3. `tailEdgeExponent N n M`: minus the sum of `columnPsiTwo N (n j)` over full indices j with M≤j.val, divided by `Real.log (N : Real)`.
4. `ambientLengthExponent N n hM A b x`: b minus the sum of `Real.log ((N : Real)/(selected count : Real))` over prefix indices t with A≤t.val, divided by log N. Its dependence on the ambient prefix is through A and b, exactly as in the source formula. It must not be defined by a logarithm of mu_x.
5. `ambientMeanError N n hA w b`: `Real.log (prefixMean N n hA w) / Real.log (N : Real) − b`.

The exponent definitions can use Lean's total real functions on arbitrary inputs, but their source interpretation and logarithmic identities are asserted only on the explicit domains below. In particular, defining Real.log at zero does not license dropping legality or N≥2 from an identity that exponentiates a logarithm.

## Complete bounded lemma inventory and proof routes

This is a proposed inventory of fourteen named lemmas. Every other operation described here can remain a local proof using existing project declarations and trusted mathlib. No new log-base, extension-product, probability, or conditional-law definition is needed. A final design can use these exact mathematical boundaries and freeze the chosen names before implementation.

**E.01 — Positive prefix mean.** For N≥2 and a legal prefix x, mu_x>0. Every selected factor is positive because its numerator is positive and N>0; their finite product is positive, including the empty product, and multiplication by N remains positive. This purely algebraic fact needs no count-sum hypothesis. It supplies a local positive product proof as well as the asserted positive mean.

**E.02 — Positive one-column square sum.** For a single count array summing to N≥2, `sum_a (singleFactor N counts a)^2 > 0`. The positive total supplies at least one positive count; its squared normalized mass is positive, and all other squares are nonnegative. This derives any required alphabet inhabitance locally, without adding a nonempty-alphabet premise. This is true even if all counts are at most one.

**E.03 — Exact mean extension product.** For A≤M≤K and x extending w,

`mu_x = mu_w * product over A≤j<M of n[j,x[j]]/N`.

The statement is a finite product identity and needs neither legality, feasibility, nor N≥2. Partition the prefix product into indices below A and those at least A. Identify the first factor with the product for w using `Fin.castLE`, the extension equality, and equality of the composed full-column index maps. Associate the existing leading factor N. The empty segment A=M gives product one.

**E.04 — Exact logarithmic extension identity.** Under N≥2 and legality of x,

`log(mu_x) = log(mu_w) − sum over A≤j<M of log(N/n[j,x[j]])`.

Derive legality of w from the extension. Apply E.01, E.03, and trusted `Real.log_mul` and `Real.log_prod` to the positive selected factors. On each factor, `log(n/N) = −log(N/n)` follows from `Real.log_div` with both positive inputs. No logarithm of a zero realized occupancy is involved; only the deterministic mean is logged. No feasibility hypothesis is needed by this algebra once legality is supplied.

**E.05 — Source length exponent plus exact error.** With the same data,

`L + epsilon_w = log(mu_x)/log N`.

This follows by substituting the two frozen-form definitions and E.04. It preserves b and the original source sum literally; b cancels in the proof instead of being reset to log_N(mu_w).

**E.06 — Mean as a real power.** Under the same domain,

`mu_x = (N : Real) ^ (L + epsilon_w)`.

Use E.05, E.01, N>0 and N≠1, and the trusted `Real.rpow_logb` after unfolding `Real.logb`. This works for negative values of L+epsilon_w and for means below one. No lower bound on either exponent is added.

**E.07 — Exact square-tail power identity.** For feasible n, N≥2, and arbitrary natural M,

`tailSquareFactor N n M = (N : Real) ^ (tailEdgeExponent N n M)`.

E.02 proves positivity of each selected square sum. Thus the tail product is positive, even for an empty index set, and `Real.log_prod` gives its logarithm as the sum of their logarithms. By the definition of psi, this is minus the sum appearing in E. Divide by log N and apply `Real.rpow_logb`. The tail-product positivity and its logarithmic identity are local proved steps of E.07. No selected-prefix legality is needed, because this is a statement only about complete tail columns.

**E.08 — Exact fixed-column tail inequality.** Under the same feasible N≥2 domain,

`tailCollisionFactor N n M ≤ (N : Real) ^ (tailEdgeExponent N n M)`.

Combine the already-proved C.46, `tailCollisionFactor_le_tailSquareFactor`, with E.07. Crucially, E.07 is an identity for `tailSquareFactor`, not for `tailCollisionFactor`. For example, a column with all positive piles of size one has zero distinct-label coincidence factor but a strictly positive square sum. Its source E is finite. We never take a logarithm of the exact without-replacement tail factor and never replace this inequality by equality.

**E.09 — Fourth-power ambient density conversion.** For feasible n, N≥2, legal x extending w, and arbitrary real b,

`D_abs(x) ≤ (N : Real) ^ (4*(L+epsilon_w)+2*E) / 4`,

where `D_abs` is exactly the already-defined edge density under `matrixLaw n hn` and `sortedRows n`, with prefix `prefixWord x`.

Start with C.54, `D_abs≤mu_x^4*q_tail^2/4`. The exact tail factor is nonnegative by the existing C.44. E.08 and positivity of real powers justify squaring its inequality. E.06 rewrites the mean, and trusted real-power multiplication/addition identities combine the factors into the displayed exponent. The constant remains exactly 1/4. This has no cF term, no case assumption, and no hidden o(1).

**E.10 — Small-length tail-only form.** Add only the case condition L<2delta, with real delta. Then

`D_abs(x) ≤ (N : Real) ^ (2*E+8*delta+4*epsilon_w) / 4`.

From 4L<8delta and base N>1, monotonicity of real powers compares E.09 with this bound. The proof does not need delta positive; the source's positive-delta regime is included. This applies in particular to small non-singleton blocks, but it is not the source's stronger displayed estimate with minus cF.

**E.11 — Small-length form retaining the singleton exponent.** Under the same L<2delta condition,

`D_abs(x) ≤ (N : Real) ^ (2*L+2*E+4*delta+4*epsilon_w) / 4`.

Use `4L < 2L+4delta` in E.09. This has the source singleton exponent 2L+2E with the fully explicit finite error `4delta+4epsilon_w`. It holds for every small legal prefix, so a singleton/stability hypothesis is unnecessary. The case L<0 is included without any replacement of L by zero. Since real powers of positive N are positive, dropping the factor 1/4 also gives the printed type of upper-bound normalization.

**E.12 — Direct ambient mean conversion.** With the E.09 data but no small-length condition,

`D_abs(x) ≤ (N : Real) ^ (L+epsilon_w)`.

Combine the already-proved C.55 with E.06. This is the sharper direct estimate needed for the terminal interpretation; no second-moment concentration input is necessary.

**E.13 — Full-length edge exponent is zero.** For every N and n,

`tailEdgeExponent N n K = 0`.

The tail index finset is empty, so its sum is zero and the stated total division gives zero. This definitional identity needs neither feasibility nor a log-base hypothesis. On the large-N domain, E.12 specialized to M=K together with E.13 is exactly the finite terminal statement

`E=0` and `D_abs(x)≤N^(L+epsilon_w)`.

These two existing named conclusions explicitly cover the terminal case without requiring another duplicate named inequality. Establishing that a particular terminal retained pair gives such an x is a separate stable-partition obligation.

**E.14 — Empty-ambient error.** For N≥2 and the empty ambient word,

`ambientMeanError(empty,b) = 1−b`.

The empty-prefix mean is N by the already-proved empty product identity, and log N/log N=1. In the source's whole-deck case b=1 this gives epsilon_w=0 exactly. A nonempty ambient prefix does not inherit this cancellation merely because its expected size has an asymptotic exponent b.

The six newly frozen overlap statements can translate E.09–E.12 into inequalities for expected same-position shared edges if later desired. No separate duplicate overlap-exponent theorem is included in this fourteen-lemma inventory; that conversion uses the proved exact overlap identity directly.

## Exact small and terminal consequences versus source asymptotics

The small-length assumption L<2delta appears verbatim in the source's cases. E.10 supplies a valid bound with exponent 2E+8delta+4epsilon_w. E.11 supplies the singleton-shaped exponent 2L+2E+4delta+4epsilon_w without using singleton classification, a small-occupancy moment, or a spatial spread theorem. For a sequence for which the source's ambient mean condition is actually established, epsilon_w tends to zero, so the displayed explicit errors have the desired 4delta+o(1) form. That convergence is explanatory context here and is neither assumed nor proved by this finite inventory.

The terminal bound at TeX 1645–1659 follows at the finite numerical level from occupancy rather than the source sketch's unnecessary small-mean second-moment step. E.12 and E.13 keep its cE compatibility term equal to zero and carry only epsilon_w. No condition L<2delta, retained-boundary property, or singleton stability condition is needed for this count-to-mean inequality itself.

None of E.09–E.13 implies the large-block exponent 4L−cF+2E or the small non-singleton exponent −cF+2E in TeX 1493/1498. This addendum must not be labeled as a formalization of those stronger statements.

## Remaining cases and domain checks

* N=0 and N=1 remain covered by the previous finite theorems, but are excluded from the logarithm-base conversion by the explicit N≥2 domain. They are not silently assigned a source log_N interpretation.
* With N≥2, feasibility of a present column forces at least one positive pile, even if k=0 was not syntactically excluded. If k=0 and K>0, the assumptions are inconsistent; if K=0, the empty matrix and empty words remain allowed for every N≥2.
* K=0 forces A=M=0. Both tail factors equal one, E=0, mu=N, L=b, and epsilon_w=1−b. Thus L+epsilon_w=1 and the generic formulas include the deterministic empty-word graph.
* A=0, A=M, and M=K are all handled by the literal empty interval sums/products. For A=M and x extending w, mu_x=mu_w and L=b exactly.
* Zero nonselected piles and zero tail piles are allowed. Zero selected prefix piles are outside the source's legal-word logarithmic domain; the older finite density theorems still apply to them separately. No logarithmic equality at a zero mean is asserted.
* A selected prefix pile of size one is legal. Its mean can be positive even though its graph has no two equal rows in that prefix; the exact finite inequalities remain valid.
* A zero exact tail collision factor is allowed. E is defined through positive sums of squares, so no infinity or division by that zero factor is introduced.
* There are no assumptions L≥0, E<0, epsilon_w≥0, delta>0, K=O(log N), or b in a prescribed interval in the algebraic steps that do not need them. Source-specific later arguments may establish or use such restrictions separately.

## Absolute coordinates and the outstanding ambient bridge

TeX 509–512 declares a sample-dependent recentering at the ambient block's random left endpoint. Existing `edgeDensity`, C.54/C.55, and the frozen overlap identities use absolute sorted deck positions. The bounds in this report therefore concern those existing absolute coordinates. The source's statement that translation does not change an internal edge count is correct, but by itself does not identify a sum of squared position probabilities or an independent-copy intersection before and after separately random translations.

A future relative-coordinate theorem could use a separately defined recentered row/edge map and prove its count comparison directly before applying the generic density bound. It must supply that finite bridge. This report neither inserts the bridge as an assumption nor claims it has already been proved. The ambient parameters in the present exponent conversion identify exact expected prefix sizes, not a new conditional population or coordinate system.

## Dependency verdict

The algebraic dependencies are E.01→E.04, E.03→E.04→E.05→E.06; E.02→E.07, and C.46/E.07→E.08. C.54/E.06/E.08→E.09→E.10/E.11. C.55/E.06→E.12; E.13 gives its terminal specialization. The empty-prefix identity gives E.14. Trusted mathlib logarithm and real-power theorems discharge the analytic identities; finite product splitting supplies the only new combinatorial step. No Riemann-sum, profile, concentration, or resampling lemma is imported as an assumed interface.

This is a mathematically valid bounded inventory for independent statement design and hidden-case comparison. Exact names and argument signatures should be compared and frozen before any implementation. The existing cL and cE meanings are preserved, with epsilon_w carried exactly throughout.

## Final-signature comparison and acceptance

I have compared all five definition bodies X.D01–X.D05 and every ordered parameter list and conclusion X.01–X.15 in `exponent_contract_statements.md` with the reconstruction above and the complete independent assumptions report. **I accept the selected fifteen-theorem inventory exactly as specified, with no remaining pre-freeze correction.** No Lean code was written during this comparison.

The selected definitions preserve the source actual-count suffix-cost meaning of cL, the exact signed discrepancy epsilon_w, and the source cE obtained from minus the sum of psi(2). The zero-based filters select exactly the intended source intervals. The square-tail product, rather than the possibly zero fixed-count collision product, is the quantity equal to N raised to cE.

X.01 derives legality of the ambient prefix from the pointwise extension relation and legality of x. X.02–X.05 need only those positive selected counts and N≥2; omitting feasibility there is correct. X.03 proves the full-prefix logarithmic formula, and X.04 proves its extension difference by local finite sum decomposition. X.05 then derives the exact power identity with the computed ambient error. No desired mean identity, separate ambient legality, positive mean, or nonzero logarithmic denominator is inserted as an assumption.

X.06 derives square-sum positivity from feasibility and N≥2, including zero piles. X.07 is valid for arbitrary natural M, including M≥K, and X.08 only bounds the exact fixed-count tail factor by the positive square product. X.09 keeps the coefficient 1/4 and exponent 4(L+epsilon_w)+2E. X.10 and X.11 correctly use L<2delta itself and keep, respectively, 2E+8delta+4epsilon_w and 2L+2E+4delta+4epsilon_w. Arbitrary signed b, L, epsilon_w, and delta are allowed whenever the displayed premises hold. The singleton-shaped conclusion requires no unimplemented singleton predicate. X.12 correctly converts the existing density-at-most-mean inequality.

X.13 is an all-N empty-sum identity and needs neither feasibility nor the logarithmic-domain premise. X.14 is precisely the full-length specialization of X.12; together they supply E=0 and the finite terminal exponent bound. The derived ambient length proof agrees with the displayed proof by proof irrelevance. X.15 correctly specializes the empty ambient prefix to the source root convention b=1: its mean is N, so the exact error is zero for N≥2 without feasibility or legality assumptions.

The earlier fourteen-item proposal and the selected fifteen-item inventory differ only in the reviewed decomposition before freeze: derived legality and the full-prefix log identity are exposed; the raw product split and exponent-ratio algebra are proved locally; the terminal specialization is named explicitly; and the root conclusion fixes b=1. Every selected obligation has the reconstruction's complete proof route and needs no additional named helper. I accept the four-module dependency layout: Model for the five definitions, Mean for X.01–05/X.15, Tail for X.06–08/X.13, and Estimates for X.09–12/X.14.

This acceptance includes empty/equal-length prefixes, empty matrices and tails, selected singleton piles, zero exact collision factors, and the absence of any hidden sign premise. It concerns the existing absolute-coordinate density only. It adds no profile approximation, error bound, exploration conditioning, relative-coordinate bridge, or spatial saving, and does not establish the source's stronger obstructed minus-cF estimates.
