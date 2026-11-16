# Independent inequality and missing-hypothesis audit

This report independently reads only `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf` (the two PDFs through existing source-text extracts). No peer reports or Lean files were read. No theorem assumptions have been changed and no Lean code has been written.

## Verdict before freezing

The three numerical exponent rearrangements in the unified article are correct. Optimization over theta is also correct when the error is uniform over theta. These scalar lemmas can be formalized independently of the stochastic model.

The final common-edge bound cannot honestly be declared established from the written upstream results. The unified article includes the first deterministic column in its boundary and fluctuation definitions, producing a direct counterexample to its anti-concentration/conditioning-transfer input. The profile-class definition also omits exceptional digit values, although the claimed within-class entropy count requires them. Final summation needs two explicit counting factors rather than the one displayed in the sketch. These issues must be resolved before freezing an unconditional model-level final theorem; none may be silently assumed away.

## 1. Large-block numerical exponent

Write `L = c_L(x)`, `V = c_L(y∨z)`, `F = c_F(y∨z)`, `B = B_theta(s,u)`, and `C = B_2(u,T)`. The source supplies, with explicit error variables replacing asymptotic notation,

- `3 ≤ theta ≤ 4`, `Q ≥ 0`;
- `L ≤ V - S - Q + eL`;
- `L ≤ F + delta` (stable stopping);
- `F ≥ V/2 - eF`;
- `V ≤ beta + eV`;
- `H ≤ theta*S - B + eH`, `E ≤ -C + eE`.

An exact rearrangement, avoiding the extra detour through a lower bound on `S`, is

`4L - F + theta*S ≤ theta*V + (4-theta)*L - F - theta*Q + theta*eL`

`≤ theta*V + (3-theta)*F + (4-theta)*delta - theta*Q + theta*eL`

`≤ ((theta+3)/2)*beta + ((theta+3)/2)*eV + (theta-3)*eF + (4-theta)*delta + theta*eL`.

Hence

`4L-F+2E+H ≤ ((theta+3)/2)*beta-B-2C + ((theta+3)/2)*eV +(theta-3)*eF +(4-theta)*delta +theta*eL +eH+2eE`.

All sign uses are valid: `4-theta ≥ 0`, `3-theta ≤ 0`, `theta ≥ 0`, and `(theta+3)/2 > 0`. No assumption `beta ≥ 0`, `V ≥ 0`, or `F ≥ 0` is needed. In particular, do not introduce one for convenience. If all five errors are bounded by a common nonnegative `e`, the error is at most `(23/2)*e + delta` by separately bounding the coefficients; a somewhat sharper common coefficient is possible but unnecessary.

The exact algebra does not need the large-block size lower bound. That bound is needed by the probabilistic edge-density input. The numerical lemma also applies to nonterminal singleton stable classes when the same fluctuation and stability inequalities hold.

This is the inhomogeneous version of the calculation in 2510, Lemma 4.16(a), pp. 30–31. The homogeneous identity `psi_mu(theta_mu) = 2 psi_mu(2)` must not enter the inhomogeneous theorem.

## 2. Small non-singleton exponent

The exact scalar input is the first-crossing/parent estimate

`S ≤ V - F + eS`,

together with `theta ≥ 0`, `F ≥ V/2-eF`, `V ≤ beta+eV`, and the same entropy/tail estimates. It gives

`-F + theta*S ≤ theta*V-(theta+1)*F+theta*eS`

`≤ ((theta-1)/2)*beta + ((theta-1)/2)*eV +(theta+1)*eF +theta*eS`.

After adding `2E+H-theta*S`, the target envelope has coefficient `(theta-1)/2` and error `((theta-1)/2)*eV +(theta+1)*eF +theta*eS +eH+2eE`.

The signs are correct for theta in `[3,4]`. Nonnegativity of `Q` is used earlier, when deriving the parent estimate, and should not be replaced by an upper bound on `Q`. A last exceptional digit adds zero to `S`; a last good digit adds at most `log(1/(2chi))/log N`, which is `o(1)` only because chi is fixed before N tends to infinity. The exact finite statement must account for this term.

The size condition `L<2delta` and the lower bound `F≥delta-(log N)^(-1/2)` are prerequisites for the edge-density estimate, not for this algebra. The article's inference that a low-F small class must be a singleton needs a quantified fluctuation error: a bare unspecified `o(1)` does not by itself imply it is smaller than `(log N)^(-1/2)`. The explicit boundary comparison gives an `O_chi(1/log N)` error in the whole-deck setting, which would suffice if actually proved and used.

## 3. Singleton exponent

For `x=y∨z`, the suffix interval `(s,u]` is empty, so `u=s`, `S=Q=H=0`. The scalar argument is simply

`c_L(x)+c_E(x) ≤ beta(s)-B_2(s,T)+eV+eE ≤ -eta+eV+eE`.

A terminal pair has `|x|=K` and `c_E(x)=0` exactly. Since `K=floor(T log N)`, its scaled time is `s=K/log N`, not literally `T`. The sentence `s=T` in the numerical proof is false at finite N. It can be replaced, without a new hypothesis, by the floor-error bounds from `0≤a≤log k` and `0≤psi_2≤log k`, or the singleton N3 margin can be applied at the actual `s`.

The terminal edge-density lemma itself has an elementary proof `sum_m p_m^2 ≤ E|E(G_Bx)| ≤ E|I(B_x)|`; its displayed proof unnecessarily invokes a small-mean second-moment estimate without assuming a small mean. The statement can be proved directly for every terminal prefix from the first moment of its population.

## 4. Optimization over theta

No supremum/infimum exchange or homogeneous optimizer is needed. If a finite real exponent `Z` satisfies

`Z ≤ f(theta)+e` for every `theta∈[3,4]`,

then `Z-e` is a lower bound for the nonempty image of `f` on `[3,4]`; therefore `Z-e ≤ inf f`. Combining this with the frozen margin `inf f≤-eta` gives `Z≤-eta+e`.

This approach does not require attainment, continuity, an optimizer selector, or extra compactness assumptions. The pointwise bound itself supplies boundedness below of the image. If the proof instead chooses a theta close to the infimum, nonemptiness and the relevant conditional-completeness hypotheses must be discharged, and the approximation loss must be budgeted. Uniformity of `e` in theta is essential.

The source integral costs are bounded for fixed k and theta∈[3,4]. However the source calls `mu_t` a family of probability measures without explicitly stating measurability of the time kernel. A foundational implementation of the integrals must resolve this from the intended meaning of time profile; it cannot add a hidden measurability axiom after freezing.

## 5. Profile-class counting

### Missing exceptional digit values: explicit counterexample

The unified Definition of space-time digit profile (tex approximately 722–747) records good-digit counts and the exceptional LOCATION set `Q_x`. It does not record the digit at those locations. By contrast, 2510 Definition 4.7 and its final first-moment assembly explicitly record the pairs `{(t,x[t])}`.

For a concrete family, take `k=5`, fixed `0<epsilon<chi` with chi small, and constant column proportions

`p=(a,a,a,epsilon,epsilon)`, `a=(1-2epsilon)/3`.

The large boundary indices are 0 and 2. Under the unified boundary convention, take the retained admissible pair `y=z=(1)`. Let q be the first integer for which

`1 + log_N(a) - q*log_N(1/epsilon) - (1/2 + (1/2)*log_N(a)) < delta`.

Every word beginning with 1 followed by q choices from `{3,4}` is a first-crossing stable prefix, with the same actual size exponent, boundary pair, exceptional location set, good-count data, and entropy `H=0`. There are `2^q` such prefixes. As N tends to infinity,

`q/log N → (1/2-delta)/log(1/epsilon) > 0`.

For sufficiently small chi and epsilon comparable to chi, this is below `alpha_chi = 1/sqrt(log(1/chi))`, so all these profiles survive truncation. Nevertheless

`|class| = N^{((1/2-delta)*log 2)/log(1/epsilon)+o(1)}`,

which contradicts the claimed `|class|≤N^{H+o(1)}=N^{o(1)}` at fixed chi. This is not repaired by calling a fixed positive chi-dependent exponent `o(1)`.

A mathematically available route is to define, before freezing, an explicit refined counting class which also fixes exceptional digit values. This does not strengthen a model assumption, but it is a new definition which must be visible. Alternatively retain an explicit `alpha_chi*log k` exponent in the class bound. The final prose claims digit values were already counted, so a refinement expresses its apparent intent; the original profile definition by itself does not.

### Further counting details

- The number of retained exceptional LOCATION-and-VALUE data is bounded by `sum_{q≤alpha_chi log N} binom(K,q) k^q`. Its logarithmic exponent tends to zero with chi. Coarse counts add a fixed power of `K+1` once chi and the time mesh are fixed.
- Boundary data similarly use a binomial tail with cutoff `C_bdry log N/log(1/chi)`, plus polynomial factors in K for stopping times. The count can be made `N^epsilon` by choosing chi first and N later.
- The article says that the unweighted number of exceptional choices in the discarded tail `q≥alpha_chi log N` is `exp(O(alpha_chi log(1/alpha_chi) log N))`. Literally this is false: the tail contains the bulk binomial levels. The weighted tail still has the required small bound because the factor `(4chi)^q` dominates. Use a binomial/Chernoff tail or an explicit ratio argument, not the unweighted claim.
- Expected population mass carries an initial factor at most N; the displayed exceptional-tail probability omits it. This is harmless for a target arbitrary polynomial decay only if that factor is included before selecting chi.
- With actual probabilities varying inside one regular cell, the exact `c_L(x)` is not constant inside a coarse profile. Only its representative approximation and H are constant (after fixing exceptional values). Split classes further by the finite large/small/singleton routing, or sum pointwise estimates with common H. Do not import the old paper's assertion that its differently defined `c_L` is exactly class-constant.

## 6. Final expected common-edge assembly

### Correct finite summation shape

Independence and equal distribution of G and G' give the identity

`E|E(G)∩E(G')| = sum_m P(m∈E(G))^2`.

The proof must preserve both independence and equal distribution; otherwise the summands are products of two possibly different probabilities. Measurability/integrability are automatic for a finite model only after the finite graph/random-variable definitions are in place.

If each retained edge probability is bounded by a sum of at most M block probabilities, Cauchy–Schwarz contributes M. Summing over all block/profile classes and replacing their sum by a maximum contributes the number C of classes. Thus the correct shape is

`sum_m p_m^2 ≤ discarded_error + constant*M*C*max_class(sum_{x in class,m} p_{x,m}^2)`.

The article assigns both M and C the bound `N^epsilon`, then displays only one `N^epsilon` factor. For fixed finite epsilon that displayed implication is false. Its asymptotic intended conclusion survives by budgeting epsilon/2 (or smaller) independently for each source of multiplicity before parameter choice. Keep M and C separate in Lean until both are explicitly absorbed.

The independently reviewed exact finite version is valid: if all relevant quantities are nonnegative, `p_m ≤ d_m + sum_{i active at m} q_{i,m}`, `#active(m)≤L`, `sum_m d_m^2≤D`, `classOf:I→C`, and each class has `sum_{i in class,m} q_{i,m}^2≤U`, then

`sum_m p_m^2 ≤ 2D + 2L*(#C)*U`.

Nonnegativity must include L, or another fact must imply it even in the empty-edge-set case. In a finite product sample law, the expectation-of-common-edges identity is exact by expanding the indicator of an intersection and distributing the finite sums. With the common nonnegative scalar error e, the proposed numerical losses `12e+delta`, `14e`, and `2e` are valid (for `delta≥0`): the first two raw coefficient maxima are 11.5 and 13.5 respectively.

Large, small non-singleton, small singleton, and terminal singleton classes have respective exponent bounds `-delta1+edge_error`, `-delta1+edge_error`, `-2delta1+edge_error`, and `-delta1+edge_error`. Each must remain negative after the class count, localization multiplicity, constants, and discarded terms are included. The final selection order must be coherent: first choose the allowed counting exponent from eta, then choose chi sufficiently small to attain it, then take N large. One cannot fix chi and afterwards demand arbitrarily small counting exponents.

### Decisive false upstream anti-concentration input

Take the whole-deck ambient block, k=3, N divisible by 3, and every column with exactly N/3 copies of each digit. Set `y=z=(1)`. In the unified definition the first digit is a genuine left and right crossing, so this is a retained admissible nonterminal pair whenever K>1. Both side pieces at the first column have deterministic size N/3. Consequently

`F = (1/2) log_N(N/3) = 1/2 - (1/2)log_N 3`.

For `x=(1)` the interval starts at the deterministic beginning of the first-column digit-1 pile. Thus its left endpoint has point mass 1. The claimed conditional anti-concentration bound, with RHS `N^{-F+O(delta)+o(1)}`, tends to zero for sufficiently small delta and cannot hold on an event of probability tending to 1.

This counterexample also lies on a retained LARGE STABLE prefix. Choose M minimal with

`1-M log_N 3-F < delta`,

and let `x=(1,0,...,0)` have length M. Then x is first-crossing stable, `L≈1/2+delta`, and H=Q=0; all digits are good. Its left endpoint is still exactly the beginning of the first-column digit-1 pile. Conditional on the internal information, both endpoints are fixed. In the article's `a=b=1` hypergeometric construction, the sample size is the entire remaining population:

`d2 = N - n_1^(1)`, `n = N - n_1^(1)`, hence `1-d2/n=0` and `Var(Y3)=0`.

This directly contradicts the conditioning-transfer lemma's claimed positive lower bound on complementary population fractions and the claimed variance lower bound.

All stated macroscopic hypotheses can hold: the constant uniform profile is almost-like, every column is good, and choosing `T log 3 > 3/2` makes all the source FM margins strictly negative. Indeed for the whole deck, after evaluating the large envelope at theta=3, its maximum is at most `max(3-2T log 3,1-T log 3)`. So the obstruction is not excluded by the variational assumptions.

The old deterministic-column paper 2510 explicitly avoids this problem: Definition 4.3 starts crossing positions after column 1, and its fluctuation maxima start at index 2 (pp. 18–20). It conditions on the first pile and uses the first-good-shuffle assumption to prove a non-exhaustion fraction. The unified article removed that exclusion without a valid replacement. The local density of good columns does not make deterministic first-column counts fluctuate.

There are additional upstream proof gaps even aside from this counterexample:

- The endpoint-window proof bounds every left piece using `F=min(F_left,F_right)`. This does not follow when the left scale is the larger one. The old argument chooses the smaller side and then transfers the endpoint bound using the block-size bound. This choice must be explicit.
- The localization proof calls `exp(-N^{delta-o(1)})` smaller than `exp(-N^delta)` to obtain a contradiction. The inequality goes the other way when the o(1) loss is positive. A strict power gap is needed in the thresholds or in the concentration estimate.
- The localization coverage statement has an exponentially small failure although discarded families were only bounded by arbitrary polynomially small MASS. Such a mass bound does not imply the displayed exponential coverage probability. The final proof can instead keep discarded edge mass as a separate polynomial error; it must not treat the literal coverage statement as already proved.
- Counts of individual prefixes are generally polynomially many after profile truncation, not `N^{o(1)}` merely because the number of profiles is subpolynomial. Exponentially good concentration can absorb a polynomial union bound, but that stronger count must be stated correctly.

## Proof-architecture context

The upper branch is: fixed-column graph representation → truncated chi-square reduction and sparse factorial bound → boundary/stable partition and profile estimates → localization and edge-density bounds → the six assigned first-moment components → conditional exploration first moments (requiring uniform conditional block regularity) → Portenko/directional exponential moments → total-variation convergence. Recursive first-moment margins serve the accessible conditioned blocks; whole-deck FM alone cannot be substituted for them in the exponential-moment step.

The lower branch is separate: largest-prefix occupancy obstruction, or a variational cold witness → profile/entropy counting → buffers and localization → collision first/second moments → a permutation test. It does not supply a missing upper anti-concentration theorem.

The **inactive historical lower overview**, entirely inside the `comment` environment beginning at tex 2562 and ending at tex 2786, contains an algebraic inconsistency: from its own h and gamma definitions,

`gamma-h/2 = 3/2 + ((theta-3)/2)J_theta - (1/2)B_theta - B_2`,

whereas tex approximately 2623 writes `-B_theta`. Thus its subsequent Xi formula and the statement `2Xi(theta,u)=N1(0,0,u;1)` cannot be used; the latter also ignores that N1 is an infimum. These are historical notes, not a defect in an active displayed theorem. The later **active** full lower section has the correct relation

`(2Gamma-h)-F_theta = (theta-3)(J_theta-beta/2)`

and should be the source for a lower dependency map.

The random-cut upper extension conditions on a typical deterministic sequence and averages the total-variation bound. This requires uniformity of the deterministic bound over those sequences. A corresponding expected-common-edge claim for a mixture must specify whether the two graphs share a sampled environment or have independent environments. With independent environments, Cauchy–Schwarz can control cross-environment scalar products by their diagonal bounds, but the exceptional environment probability contributes up to N times that probability to an unnormalized edge count; merely `o(1)` typicality does not give polynomial first-moment decay. The random total-variation corollary only needs an `o(1)` exceptional probability and is consistent with this distinction.

The random-cut lower extension requires a single union test, not averaging deterministic total-variation lower bounds. The inactive historical overview proposes a union over at most `exp(O((log N)^2))` deterministic integer cut sequences and exponentially small uniform false-positive probabilities; integer-valued pile sizes and the uniform quantitative testing bound would have to be retained. The active random upper corollary is outside that comment environment and uses conditioning and averaging as described above.
