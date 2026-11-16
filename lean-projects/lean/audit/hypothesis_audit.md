# Independent hypothesis audit

Status: pre-freeze review; no Lean statements or assumptions have been frozen by this report, and no Lean code has been written by this reviewer.

The only mathematical sources read were `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf`. PDF page numbers below are the displayed PDF page numbers, which agree with the printed numbering in the relevant passages. Temporary plain-text extractions were made solely from these PDFs.

## Main finding

The finite one-step hypergeometric core has a sound formulation, including empty populations and zero variance. The manuscript's ambient conditioning-transfer and non-exhaustion claims cannot be frozen as written: they have a direct counterexample, and the ambient conditional laws also leave part of their revealing information unspecified. Those are mathematical obstructions, not Lean implementation difficulties.

## 1. Exact source locations and dependence

| Family | Current manuscript | Homogeneous fixed-column source | Earlier multinomial source |
|---|---|---|---|
| Hypergeometric law, expectation, concentration | `lem:ub-hypergeometric-estimates`, lines 1121–1152; `eq:hypergeom-concentration` | 2510, §2.3, pp. 8–10, Lemmas 2.3–2.7 | 2103 uses binomial laws; it does not justify replacing fixed-column laws by independent Bernoulli rows |
| Variance and point masses | Same manuscript lemma; conditional variance displays at lines 1343–1414 | 2510, Lemma 4.6 and proof of Lemma 4.5, pp. 20–23 | 2103, Lemma 4.13, pp. 24–25, is specifically a conditional binomial argument |
| Conditional hypergeometric variables | `lem:ub-ambient-concentration-anti-concentration`, three reveals at lines 1284–1429 | 2510, Lemma 4.5, pp. 20–23 | 2103, Lemma 4.13, pp. 24–25 |
| Ambient conditioning transfer | `lem:ub-ambient-conditioning-transfer`, lines 1154–1200; `lem:ub-conditional-preservation`, lines 1923–1930 | 2510, Lemma 5.5, p. 37, and §5.3–5.4, especially (5.22)–(5.24) and Lemma 5.8, p. 44 | 2103, Lemma 5.6, p. 33, requires an explicit unexhausted mass condition |
| Successive thinning, conditioned labelled rows | `lem:successive-thinning-tail`, lines 3018–3167; `cor:iterated-hypergeom`, lines 3169–3354 | 2510, Lemmas 2.6–2.7, pp. 9–10, give prefix concentration | Not a replacement for fixed-column conditional laws |
| Random-pile extension | `cor:random-time-profile-upper-bound`, lines 1999–2011; `thm:lower-bound-blueprint`, lines 2737–2747 | 2510, §3.3 and §6.1; random lower testing discussed p. 5 and Lemmas 6.5–6.6 | Earlier paper supplies the ascent-test architecture |

The upper-bound dependency chain is: fixed independent columns → prefix and side-piece counts → concentration and non-exhaustion → conditional endpoint point masses → edge-density bounds → numerical first moment → conditional preservation during exploration → conditional first moment → exponential moment → truncated chi-square → deterministic upper bound → averaging over random piles.

The lower-bound chain using this agent's part is: fixed independent columns → exact one-step conditional laws → Laplace-transform thinning bound and prefix-tree concentration → (a) largest-prefix obstruction; (b) relative endpoint control and bridge localization. The cold-count branch additionally requires factorial moments, conditioned labelled-row residual laws, occupancy covariance control, and the ascent test. The newer manuscript explicitly imports only the one-step estimates as U4 and proves its multi-column thinning internally. Failure of the upper ambient point-mass claim does not by itself invalidate the independently proved lower prefix concentration.

For random piles, first sample the complete integer-valued pile sequence, then sample independent uniform columns conditional on it. This is the manuscript's mixture model. Pile sizes chosen in response to previously exposed shuffle randomness do not automatically have that conditional product law.

## 2. Foundational conventions that must be explicit before freezing

1. There is an argument-order inconsistency. The upper manuscript defines `Hyp(n1,n,m)` as successes, population, sample size. The lower manuscript, immediately before `eq:survivor-hypergeometric-transition`, defines `Hyp(M,x,m)` as population, successes, sample size. The 2510 paper defines the first convention on p. 8, but some conditional displays on pp. 21–22 put population first. Use named fields `N`, `K`, `m` and one permanent order; do not transcribe the ambiguous positional notation.
2. Feasibility is `K ≤ N` and `m ≤ N`, with all three natural numbers. A uniform distribution on an empty collection of subsets is not a probability distribution. The feasible empty population has `N=K=m=0` and exactly one outcome, the empty subset.
3. The upper manuscript's description of two uniformly chosen subsets omits their independence. The 2510 definition on p. 8 explicitly says independent. If the two subsets are the same random `K`-subset, their intersection is always `K`, generally not of mean `K*m/N`. A fixed marked set and one independent uniform sample is an equally valid canonical representation.
4. The within-column row indicators are dependent. Do not represent the hypergeometric variable as a sum of independent Bernoulli variables. Binomial domination in convex order is a theorem, not a defining assumption.
5. Every conditional assertion is on positive-probability atoms or almost surely. On a null atom a conditional probability has no canonically prescribed probability-law interpretation.

## 3. Individual review of the proposed finite core

The parent proposed natural parameters `N,K,m` with `K≤N,m≤N`, outcomes `Fin(m+1)`, and real weight

`w(q) = choose(K,q) * choose(N-K,m-q) / choose(N,m)`.

### Normalization and support — approved

For `q : Fin(m+1)`, this is the exact hypergeometric mass. Vandermonde's identity gives total weight one, and all weights are nonnegative. The denominator is positive because `m≤N`, including `choose(0,0)=1`.

**Important guard:** this formula is not valid unguarded for arbitrary natural `q`. If `q>m`, natural subtraction gives `m-q=0` and can create spurious positive mass. For example, `N=3,K=2,m=1,q=2` gives a spurious `1/3`. Keep outcomes in `Fin(m+1)`, or define arbitrary point masses by an event sum/explicit `q≤m` guard. Values below the support boundary `K+m-N` automatically have zero weight through the second binomial coefficient.

Finite weighted expectation and variance are valid probability interfaces; no extra integrability hypotheses are needed on a finite space. A transfer theorem to an ambient random variable must establish its exact finite law, rather than assume its first two moments only.

### Expectation — approved

Freeze `μ=(K:ℝ)*(m:ℝ)/(N:ℝ)` with real total division. At `N=0`, feasibility forces `K=m=0`, the only outcome is zero, and both sides are zero. The equivalent conventional statement for a positive population follows without an additional probabilistic assumption.

### Factorial moments — approved

For every natural `r`,

`E[(Y)_r] = (m)_r (K)_r / (N)_r`

is correct with falling factorials and total real division. At `r=0` both sides are one, including `N=0`. If `r>N`, then `r>m`, every outcome has zero falling factorial, the numerator is zero and the denominator is zero, so both sides are zero under the explicit total-division convention. If `r≤N` but `r>m` or `r>K`, the numerator and expectation vanish. An implementation must distinguish natural falling factorials from an unrestricted real polynomial when casting.

### Variance — approved with exact casting

The correct formula is

`Var(Y)=K*m*(N-K)*(N-m)/(N^2*(N-1))`,

with real casts before subtraction. This gives zero for `N≤1` under total division. Prove those branches explicitly before any cancellation by `N` or `N-1`. At `N≥2`, zero variance is equivalent to at least one of `K=0`, `m=0`, `K=N`, or `m=N`; all these cases are deterministic.

The extraction of 2510 Lemma 4.6 on p. 20 prints the denominator as `n²(n²−1)`. That is not the variance: `N=2,K=m=1` has variance `1/4`, while that denominator gives `1/12`. The current manuscript's `n²(n−1)` is correct. Do not import the printed denominator mechanically.

### Concentration — approved as a target, not yet as proved

The source target is an **absolute** `c>0` such that for all feasible parameters and all real `t≥0`,

`P(|Y-μ|≥t) ≤ 2 exp(-c min(t²/(μ+t),t))`.

Place the existential constant before the universal quantification over parameters. For `μ=t=0`, interpret the ratio by total division and check directly: the left side is one, the right side two. If `μ=0,t>0`, the law is zero and the tail probability is zero. At any deterministic boundary, all positive-deviation tails vanish. No positive-mean hypothesis may be inserted.

The proof sketch's name “Hoeffding” alone is not an adequate proof of this mean-sensitive Bernstein form: the usual additive bounded-sampling estimate has a sample-size denominator. One needs a verified convex-order/binomial-Chernoff argument or another complete proof. The two regimes of 2510 Lemmas 2.4–2.5, pp. 8–9, provide supporting mathematics but include large-mean restrictions/typographical inconsistencies, so they cannot be copied as a single all-parameter theorem without proof.

For small means, a threshold with an additive term is essential. The manuscript's prefix bound `N^ε(√μ+1)` handles `μ=0` correctly. A purely relative approximation is not available uniformly at bounded means.

### Point-mass anti-concentration — approved as a target, not yet as proved

Freeze an absolute `C>0`, quantified before all feasible parameters, and `Var(Y)>0` (equivalently `σ=√Var(Y)>0`) for

`P(Y=q) ≤ C/σ`.

For zero variance, record the separate universal bound `P(Y=q)≤1`; do not apply total division to `C/0`, which would give the false upper bound zero. A unified formulation `P(Y=q)≤min(1,C/σ)` is valid only in the positive-variance branch unless the zero case is explicitly split.

For a tiny positive mean, a large right side is harmless. It is not necessary to assume `μ≥1` or central support. The current proof sketch still needs a complete argument controlling the mode and Stirling estimates, or a proven discrete log-concavity theorem with an appropriate quantitative conclusion. This reviewer does not certify the specific numerical constant `16` without seeing its reconstruction; existential absolute `C` matches the source.

### Finite conditional transfer — approved with the following exact interface

Use a finite outcome space with weights, a finite reveal variable `G`, and positive-mass reveal atoms. For each such atom, establish feasible parameter values `N_g,K_g,m_g` and equality of the conditional law of `Y` to the canonical finite hypergeometric law. This law equality gives the expectation, variance, concentration, and point-mass formulas on that atom. On null atoms do not claim that division by their probability produces a probability measure; either omit the atom or state only an almost-sure result.

A random threshold may be used in a conditional tail bound if it is constant on the reveal atom. In the prefix argument, `p_v X_parent` and the corresponding threshold have exactly this property.

For coarse-to-fine anti-concentration, require `U` to be a function of the finer reveal `G`, and endpoint `Z=A(G)+Y`, with an injective shift in `Y`. A good-parameter event `H` measurable in `G` must imply the variance lower bound. It suffices that the selected global event `S` is contained in `H`; `S` itself need not be measurable in `G`. Then the joint event `P(Z=j,S|U)` can be bounded by conditioning on `G` and summing. Merely knowing an unconditional lower bound on variance, or averaging conditional variances, is insufficient.

## 4. Explicit counterexample to ambient non-exhaustion

Take `k=3`, a root ambient block, `K≥2`, and first-column pile sizes

`(floor((N-1)/2), 1, ceil((N-1)/2))`.

Choose fixed `χ<1/3` and large `N`, so the left and right large-pile digits are `0` and `2`. Let `y=z=x=(1)`. Both boundary crossings occur immediately; hence this pair is nonterminal, retained, and fluctuation-regular. Its two side-piece expectations are of order `N/2`, so `c_F=1/2+o(1)`. Its block has exactly one row, so `c_L=0`, and it is even the singleton stable block under `def:boundary-pairs-stable-blocks`.

Nevertheless the block endpoints are the fixed first-column cumulative counts. There is no endpoint fluctuation. In the proof's case `a=b=1`,

`d2=N-n_1^(1)=N-1`,

which equals the entire residual population. Thus

`1-d2/(N-n_1^(1))=0`,

and the conditional hypergeometric variable is deterministic. The claimed positive complementary fraction and variance lower bound are false. Conditioning on the internal block information cannot change this.

The claimed endpoint point-mass bound also fails: for the deterministic endpoint `j0`, `E[P(endpoint=j0,S_x|U_x)]=P(S_x)→1`, whereas the asserted bound tends to zero when the fixed δ is sufficiently small relative to its implicit constant.

This counterexample can be placed at the start of an otherwise uniformly nondegenerate sequence of good columns. A local good-shuffle density does not remove it. The issue is precisely that the manuscript includes the first available column in the fluctuation maximum and uses the restricted ambient population in the residual variance calculation.

In contrast, 2510 Lemma 4.5, pp. 20–22, takes `u,v≥2`, keeps the full population `N`, and uses the first-column block size `N'=n_{x[1]}^(1)≤(1-χ)N`. Its deterministic estimate `a2+|R1|≤N'` supplies an unexhausted sample complement. The discussion on p. 23 explicitly notes that fixed first-column counts make the first digit's sorted location predictable. The current manuscript has lost this protection.

No proposed repair is treated here as already authorized or frozen: changing the fluctuation definition, the population, or a buffer hypothesis changes the current theorem interface and must be decided explicitly before freezing.

## 5. Additional ambient and conditioning gaps

### 5.1 Unrevealed ambient histogram

At manuscript lines 1288–1291, `n_l^(j)` is redefined as the ambient column count. For an unrevealed future column `b`, these counts are random. Revealing all other columns and column-`b` entries only in `R1` does not determine the ambient histogram. Therefore `L_b-a3` is not measurable in the stated `F1`, and the displayed `Hyp(L_b-a3,N_w-|R1|,a2)` does not yet describe the conditional law.

One must either retain the full original population and full original column counts, or explicitly reveal the ambient histogram/outside-ambient entries and prove the resulting conditional law. This changes the revealing information and must be specified before a theorem is frozen. The same issue affects cases 2 and 3.

### 5.2 Small means do not yield lower transfer

The first clause of `lem:ub-ambient-conditioning-transfer` supplies only an upper bound for small means, but its “Consequently” clause has no lower-size restriction on `c_F` and asserts a strictly positive conditional mean and complementary fractions for every retained pair. Such a conclusion cannot follow for small expected ambient counts.

For example, let an ambient prefix be the intersection of two independently chosen piles of size `sqrt(N)` (take square `N`), so its expected size is one and its probability of being empty stays bounded away from zero. Subsequent three-way macroscopic columns have legal left and right crossings with positive finite expected side masses. On the event that the ambient block is empty, every conditional count and variance is zero. This event cannot be discarded with stretched-exponentially small failure probability. The anti-concentration application later restricts to macroscopic `c_F`, but the transfer lemma as stated does not.

### 5.3 Expectation is not realized size

The ambient definition uses `E|I(B_w)|=N^{b+o(1)}`. Later prose writes `|I(B_w)|=N^{b+o(1)}` as if conditioning alone implied it. A separate large-mean concentration event is needed; a small ambient block can be empty. At `N_w=0` or `N_w=1`, branch explicitly before dividing by `N_w-1` or claiming positive variance.

### 5.4 Profile counts do not count words

The transfer proof says there are only `N^{o(1)}` prefix sets after profile truncation. Subpolynomially many profiles can contain polynomially many distinct words. A direct bound such as `k^{K+1}=N^{O(1)}` is available when `K=O(log N)` and still suffices for a stretched-exponential union bound. A finite theorem should count the actual deterministic family of tested sets, not identify its cardinality with the number of profiles. Data-dependent selection of a test set must be measurable before its column is sampled or be covered by a deterministic family.

### 5.5 General exploration conditioning is not a fixed-row prescription

The labelled-row conditioning theorem is valid because the event factors over independent columns and leaves each column uniform with residual counts. An event specifying lexicographically first rows or all strings on one side of a boundary generally couples columns. The short sketch in `lem:ub-conditional-preservation` does not establish the required conditional law for such exploration events. The homogeneous source devotes Lemma 5.5 and §§5.3–5.4 to this issue; 2103 Lemma 5.6, p. 33, likewise has a concrete unexhausted-mass hypothesis and gives a counterexample near the final word.

## 6. Sound non-exhaustion algebra, separated from missing geometry

A finite algebraic lemma can express exactly what the variance argument needs. Let residual population size be `n=N-r`, residual successes `K-s`, and sample size `m`, all feasible. If `n≥2`, conditional mean is at least `M≥0`, and

`1-(K-s)/n ≥ β ≥ 0`, `1-m/n ≥ α ≥ 0`,

then the variance formula gives `Var(Y)≥M α β`, because `n/(n-1)≥1`.

These are explicit premises of a general arithmetic lemma, not facts established by the manuscript's ambient geometry. They must not be smuggled in as new assumptions of the original ambient theorem.

The homogeneous mechanism for establishing them is also exact. If `m+r≤N-h`, then the sample complement satisfies `(N-r-m)/(N-r)≥h/N`. If the revealed success count satisfies `|s-rK/N|≤e`, then the residual success fraction differs from `K/N` by at most `e/(N-r)`. Thus, if `1-K/N≥β0` and `e≤β0(N-r)/2`, the residual success complement is at least `β0/2`. Parallel lower bounds transfer the mean. Every denominator needs an explicit positive residual-population branch.

## 7. Labelled-row conditioning and thinning audit

`lem:successive-thinning-tail` explicitly requires admissibility `r_{t,l}≤n_l^(t)`. With independent uniform columns, this is exactly what makes a finite labelled prescription possible and of positive probability. The residual population is `N-r`, the residual target pile is `n_{a_t}^(t)-r_{t,a_t}`, and **both** change after conditioning. The target count excludes the fixed labelled rows; a deterministic correction is needed for a total count.

When `r=N`, the residual population is empty, every residual pile is zero, and the bound is the trivial equality `1≤1` at mean zero. The source proof divides by `M` and must branch before that step. The empty word (`m=0` columns) leaves all `M` rows alive and has mean `M`; at `M=0` this remains zero. A zero target pile at any time makes all later survivor counts identically zero.

The one-step transform inequality `E[s^H]≤(1-q+qs)^x` needs `0<s≤1`, feasible parameters, and a positive-population branch or explicit empty-population proof. If `q=0`, the recursion in the source can produce `a_{t-1}=0`; later steps must allow `a_t≥0`, not require strict positivity at every step. The lower-tail constant `(1-log 2)/2` is explicitly derived in the current manuscript.

`cor:iterated-hypergeom` correctly uses a deterministic ancestor-closed finite prefix family and conditional thresholds measurable in the previous columns. The induction is sound for `p=0` and `p=1`. The statement `P(C(w)<2)≤exp(-c μ)` is derived for sufficiently large `N` from `μ≥L log N`; for a finite version, use the exact condition `μ≥4`. The extra `o(N^{-D})` term is unnecessary in the source proof.

`lem:conditional-factorial`, lines 4400–4453, does **not** explicitly require the conditioning event “b fixed rows carry w0” to be admissible. Its lower bounds on the piles selected by the other word `w` do not guarantee that `w0` is possible. For instance, a `w0` digit may have zero original pile size. This theorem needs the conditioning-event feasibility stated before freezing; it cannot claim a residual product probability law on an impossible event. This is an actual missing statement condition, unlike `lem:successive-thinning-tail`, which already supplies it.

## 8. Random-pile extension audit

The upper mixture argument requires a bound uniform over the stated good deterministic pile sequences (or an appropriate bounded convergence argument with explicit quantifiers). Merely pointwise convergence for each arbitrarily chosen sequence is not a finite bound that can automatically be averaged.

The lower mixture argument cannot average total-variation lower bounds: mixtures of distinguishable measures can equal the reference measure. The common test is the union of deterministic tests over typical pile sequences. With fixed `k` and `K=O(log N)`, there are at most `(N+1)^{kK}=exp(O((log N)^2))` integer pile sequences. Consequently a uniform `exp(-N^c)` false-positive bound survives the union. The largest-run test is already common to all sequences. The cold-set test depends on the sequence and requires the many-to-one step in the source. Both parameter-count finiteness and uniform error estimates belong in the interface.

## 9. Freeze decision

Approved for freezing after comparison with the independent probability and representation reports: feasible finite hypergeometric law; normalization; exact factorial moments, expectation, variance and deterministic boundary lemmas; the source's all-parameter concentration and positive-variance point-mass targets; positive-atom conditional transfer; exact residual laws for admissible fixed labelled-row prescriptions; finite prefix-tree concentration; and the generic non-exhaustion arithmetic implication with its explicit premises.

Not approved for freezing as source theorems: ambient conditioning transfer, ambient non-exhaustion, ambient endpoint anti-concentration, or general exploration conditional preservation. The first three have the concrete first-column counterexample above; the last needs the missing probability-space argument. This reviewer has not approved a numerical point-mass constant of 16 absent a complete proof.
