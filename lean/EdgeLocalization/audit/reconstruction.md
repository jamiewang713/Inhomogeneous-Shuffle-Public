# Independent mathematical reconstruction before freeze

This report was reconstructed independently from the three authorized mathematical sources. No other agent report was read before this report was completed. No Lean code or theorem assumptions were introduced. Source line numbers refer to `time_inhomogeneous_riffle_shuffle_unified_article.tex`; PDF page and lemma references refer to the supplied PDFs, read through their authorized text extractions.

## Decision

The assigned statements cannot all be proved with the present definitions and assumptions. The ambient anti-concentration theorem is false, and the defect reaches both the large-block and small non-singleton edge-density conclusions. The principal reason is that the manuscript counts deterministic first-column mass as endpoint fluctuation. The old deterministic-cut paper deliberately excludes the first column from this fluctuation and uses a good first column to keep a residual population available for resampling. The new local-good-column condition does not resolve this defect: the counterexamples below have every column good.

The internal shuffle-graph edge estimates, a stronger terminal singleton bound, elementary stable-prefix partition facts, localization conditional on belonging to the retained part, and a small-singleton density consequence survive. Their exact finite statements can be proved without assuming the false anti-concentration interface. A repaired definition or a weaker asymptotic theorem must not be relabeled as one of the original statements.

## Whole-proof structure and dependencies

### Definitions and common input

* Lines 85–171: fixed column counts, independent uniformly permuted columns, simplex profile, costs `a`, `ψ`, tilted costs and entropies, integrated costs `A`, `Bθ`, `Jθ`.
* Lines 173–309: global margins `Λ0`–`Λ3`, almost-profile cuts, randomized-profile cuts, regular finite simplex partition, and local good columns.
* Lines 315–374: ambient exponents, local margins `FM`, and recursive accessible-block margin `RFM`. Accessibility itself is described through the later exploration rather than formally constructed here.
* Lines 386–428 and 444–519: sorted strings, shuffle graph, prefix tree, legal strings, cylinder intervals, ambient recentering, and the exact tail collision exponent.
* Lines 521–697: left/right first-boundary crossing prefixes, admissible truncation, compatible boundary pairs, two fluctuation quantities and their minimum, stable first-crossing and terminal-fallback rules.
* Lines 699–786: space-time digit profile and numerical first-moment margin. This second first-moment-margin definition duplicates the earlier mathematical content under slightly different notation.

### Upper bound

1. Graph representation (402) gives the component-sorting law. Truncated chi-square (410) and sparse factorial comparison (429) reduce total-variation convergence to an exponential moment of shared graph edges on a regular sparse event.
2. Stable partition (788) and global boundary decomposition (828) organize all strings. Regular partition/blocking (857) gives profile estimates (898), which supply expected block sizes, fluctuation comparison, entropy and tail exponents. Bad-profile reduction (1039) bounds discarded mass and the number of retained classes.
3. One-step hypergeometric estimates (1121) are intended to imply ambient conditioning transfer (1154), then ambient size/window/anti-concentration estimates (1202). These latter implications are not valid as presently stated; see the counterexamples.
4. Stable geometry and quantitative endpoint windows are intended to give per-edge localization and the relevant-block count (1436). Internal graph collisions plus conditional translation anti-concentration plus windows yield the three density cases (1486); terminal singleton edges are handled separately (1640).
5. `FM`, profile estimates, and stable parent inequalities yield the numerical lemma (1662). The first moment (1817) combines retained-class counting, per-edge bounded multiplicity, entropy, and the four routes: large nonterminal, small non-singleton, small singleton, terminal singleton.
6. Conditional preservation (1923) plus recursive `FM` gives conditional first moment (1931). Directional exploration and the Portenko estimate (1949) yield shared-edge exponential moments (1961). Regularity and sparsity (1974), sparse factorial comparison, and truncated chi-square complete the deterministic upper theorem.
7. The uniform deterministic theorem implies the randomized upper theorem (1999), using the good-realization event and convexity/coupling of total variation.
8. Buffered pointwise upper bound (2029), margin monotonicity (2159), and the four-margin critical-time corollary (2291) identify an upper critical time. The one-column inequality (2349) implies auxiliary-margin dominance (2397), hence the reduced `Λ0, Λ1` formulation. These steps depend on completion of the earlier probabilistic upper bound.

The `RFM` uniformity is needed during exploration, not merely for the original ambient deck. Proving the first moment only at `(r,b)=(0,1)` would not complete the exponential-moment argument.

### Active lower bound

Lines 2562–2785 are enclosed in a `comment` environment. Their simple cold-spot blueprint and random lower extension are old-sketch material, not active proved results. The active lower proof starts at 2791.

The active lower proof imports graph representation, regular-cell estimates, one-step hypergeometric estimates, and margin dominance (2841–2913), but proves its own multi-column concentration and occupancy machinery.

* Labelled survivor sets and conditional residual column counts (2915–3017) → successive thinning lower tail (3018) → iterated hypergeometric prefix-tree concentration (3169).
* Maximal-pile prefix plus the preceding concentration → a long equal-string component → a long contiguous increasing run after component sorting → largest-prefix lower bound (3377), separated from a uniform permutation by `N/m!`.
* Entropy inequalities (3498) and buffered bridge window (3540) → cold-witness reduction (3583), with explicit cases in the optimizing tilt, temporal endpoints and the bridge displacement. The reduction provides a positive ambient exponent, a prefix-buffer inequality, enough cold collisions, and a bridge containing two good columns.
* Truncated tilted prefix family (3847) → type estimates (3885) → relative cold-set geometry (3928).
* Bridge/full-string family (4004–4094) → tail type estimates (4095). Iterated prefix concentration → relative endpoint theorem (4123) → cold-prefix endpoint control (4226). Endpoint control plus bridge buffers (4242) → localization (4282).
* Fixed-column factorial moments (4340) → conditional factorial moments (4400), central-window factorial comparison (4454), and fixed-column two-category Poisson bounds (4536) → occupancy approximation (4738) → cold collision count (4832) → many cold graph edges (4866), using localization.
* Uniform translate-scan ascent bound (4899), block value-set bounded differences (4951), component-value bounded differences (4979) → Lalley component comparison (5026) → Lalley cold-spot test (5115).
* Relative cold geometry plus many cold edges plus Lalley → cold lower bound (5167). Finally split `Λ0 ≥ κ0` versus `Λ0 < κ0`; in the second case the main hypothesis forces `Λ1 ≥ η`. These two branches prove the buffered reduced lower theorem (5194–5210).

The active lower proof uses only specified common upper inputs; it must not inherit the false ambient anti-concentration theorem as an assumed lower-bound fact.

### Random pile sizes

The active randomized upper corollary conditions on the realized cut sequence. Independence between the random cut vectors is unnecessary once the conditional shuffle law is the specified fixed-count product law. On a typical event its conditional TV distance is bounded uniformly by the deterministic estimate; the atypical probability is added.

The old randomized lower blueprint (2737–2747, commented out) needs a different argument: a realization-dependent separating test cannot simply be averaged to get a uniform test. Its proposed union has at most `(N+1)^(kK)=exp(O((log N)^2))` members. A uniform false-positive bound `exp(-N^c)` for each deterministic test would dominate this cost. Typical-cut probabilities and deterministic success estimates must also be uniform. This remains a claimed extension obligation in the supplied active article. The supplied homogeneous deterministic-cut paper gives the randomized upper argument in §3.3, PDF p.17, Lemma 3.13 and the following proof.

## Assigned statements: reconstruction and audit

### A. Stable partition, graph localization, and retained coverage

Source: lines 788–856 and 1436–1484; old deterministic-cut PDF Lemmas 4.9–4.10, pp.25–26; multinomial PDF Lemmas 4.5–4.6 and 4.10–4.11, pp.20–23.

The stable partition is a finite-tree stopping argument. Fix a compatible pair and `v=y∨z`. Split explicitly:

1. A boundary prefix is terminal: stable family is `{v}`.
2. Nonterminal and the threshold already holds at `v`: stable family is `{v}`.
3. Nonterminal and threshold does not hold at `v`: along every full continuation either the first threshold crossing occurs, possibly at depth `K`, or no crossing occurs and the full word is a fallback leaf.

Because `cL` is nonincreasing and the pair's `cF` is constant, the first crossing is unique. Two distinct stopped prefixes cannot extend one another. Fallback words are leaves and cannot be descendants of an earlier crossing. This proves disjoint coverage and, after sorting, a partition into possibly empty intervals. Empty random intervals must be allowed.

Equal adjacent full strings belong to exactly the same prefix cylinders. Thus an edge at `m` and membership of its first endpoint in a stable cylinder imply that both endpoints lie there. This deterministic assertion is valid independently of any concentration estimate.

For a finite family of retained cylinders `F`, put `R_m={x∈F : P(m∈I_x)≥ε}`. The exact union-bound statement is

`P(m belongs to some retained cylinder but to no R_m cylinder) ≤ |F| ε`.

If retained cylinders cover the ambient block, add the probability of being outside that block. If admissibility truncation removes cylinders, their missing probability must be added. The original displayed unconditional failure probability over retained admissible pairs omits this term. The proof itself only supplies polynomial discarded expected mass, `N^(−C0)`, not an exponentially small probability. A proof of that stronger displayed statement cannot be obtained from the stated truncation.

Concrete mechanism for polynomial coverage failure: use a fixed small leftmost pile of proportion `p<χ`, with two other piles bounded below. A row beginning with `q` copies of digit zero, where `q>C log N/log(1/χ)`, is necessarily assigned a nonadmissible left boundary prefix. Whenever such a row occurs, the lexicographically first row is discarded. Its expected count is `μ=N p^q`, a negative power of `N` for a suitable `q`. Fixed-column negative correlation gives `E X²≤μ+μ²`, hence `P(X>0)≥μ/(1+μ)`, also polynomial. With `q≤K`, this contradicts the stated exponential retained-coverage bound. The local good-column condition is satisfied.

### B. Number of relevant stable blocks

Source: lines 1446–1483; old PDF Lemma 4.10, pp.25–26.

The count `2Kk` is plausibly recoverable with unchanged stable definitions, but the written proof is insufficient. Parents of different stopped prefixes need not form an antichain: a stable child of an ancestor and a deeper stable child on another branch may have nested parents. Grouping parents by depth removes this issue. At a fixed depth their intervals are disjoint and lexicographically ordered. If three parents are relevant, the mean interval of the middle parent separates the two outer ones. Whichever side of the middle interval's midpoint contains `m`, relevance of the outer interval on the other side requires an endpoint displacement at least half the middle expected length.

The parent condition is `cL(parent)−cF≥δ`. Together with `cF≥cL(parent)/2−e_N`, it gives a large mean and a mean-to-fluctuation gap. A quantitative concentration estimate at **half the expected parent length** can then give a tail smaller than `exp(−N^δ)`, for example `exp(−c N^(2δ−o(1)))`. This would allow at most two parents per depth and at most `k` children per parent. Fallback leaves require a separate direct same-depth argument unless `FM` has already excluded them.

The manuscript only invokes a window of unspecified width `N^(cF+O(δ)+o(1))`. Its hidden coefficient may exceed the available gap `δ`, so that stated window is not enough. Moreover, `exp(−N^(δ−o(1)))` is generally **larger** than the defining relevance threshold `exp(−N^δ)`; saying this is a contradiction reverses the necessary comparison. The exact half-mean tail must be proved before freezing this cardinality theorem.

Degenerate cases: singleton pair contributes one, so the claimed `≤2Kk` needs `K≥1`; at `K=0` the root terminal singleton gives `1≤0`. Empty retained family gives cardinality zero. The ambient terminal case `|w|=K` is a singleton and must not call the parent function. Population size and `log_N` need `N>1`.

### C. Endpoint windows and anti-concentration

Source: lines 1154–1434; old PDF Lemmas 4.4–4.6, pp.19–22; multinomial PDF Lemmas 4.9 and 4.13, pp.22–24.

The intended window proof decomposes an endpoint into disjoint first-difference prefix counts, concentrates each count and the cylinder size, and takes a union bound over at most `K` terms. The paper's sentence that **every left summand** has mean at most `N^(2cF)` is false because `cF` is the minimum of the two side maxima. A repair of this proof, without changing the window statement, starts from whichever side attains the minimum, proves that endpoint's window, and obtains the other endpoint from the block-size deviation. For later pieces, use their inclusion in `B_v` and the quantitative comparison `E|B_v|≤χ^(−1) min(side means)`.

The anti-concentration proof has three mandatory reveal cases: `a>b`, `a<b`, `a=b`. The row sets revealed in the omitted column must be determined by the other columns; internal information must be measurable in the finer reveal field. On a measurable parameter-good event, the residual count is hypergeometric, a remaining endpoint is a measurable shift plus that count, and its variance is

`mean · (1−marked/population) · (1−sample/population) · population/(population−1)`.

Both complementary fractions must be strictly positive and quantitatively controlled. Large expected side masses do **not** imply the sample/population complement: the sample may be the entire residual population. This is exactly what happens in the counterexample below. The old proof used `N′≤(1−χ)N` from the good **first** column and chose the varying column strictly after it.

The stated ambient conditioning-transfer lemma's universal complementary-fraction assertion is therefore false. Successive thinning and side-mass concentration cannot turn an identically zero complementary fraction into a positive one. Another issue is that its count of prefix sets as `N^o(1)` conflates the number of profile classes with the potentially `N^H` prefixes inside a class; a polynomial count is still harmless against a correctly established exponential tail, but must be counted correctly.

For `cF<δ` the manuscript uses a trivial point-mass bound, absorbed by `O(δ)`. That low-fluctuation branch is valid as a bound with an explicit sufficiently large coefficient; it does not cure the high-fluctuation counterexample.

### D. Internal shuffle-graph edge estimate

Source: lines 1510–1518; old PDF Lemma 4.14, p.27; multinomial PDF Lemma 4.12, p.24. The later manuscript fixed-column factorial-moment lemma, lines 4340–4398, independently supports the exact counting mechanism.

Let `H` be the labelled rows having prefix `x`, and `h=|H|`. Conditional on the prefix columns, all tail columns remain independent uniform permutations with the original **global** counts. They must not be replaced silently by independently prescribed counts inside `H`. For distinct rows in `H`, the exact probability of an equal tail is

`q₂ = ∏_(j>|x|) [Σ_ℓ n[j,ℓ](n[j,ℓ]−1)]/[N(N−1)]`.

For a realization with tail multiplicities `z_t`,

`edges = Σ_t (z_t−1)_+ ≤ Σ_t choose(z_t,2)`.

Linearity of expectation gives the stronger conditional bound

`E[edges | prefix columns] ≤ choose(h,2) q₂ ≤ h² q₂`.

Each column factor is at most `Σ_ℓ(n[j,ℓ]/N)²`, so `q₂≤N^cE` exactly, with an empty tail product equal to one. No tail mixing, profile approximation, stable partition, or anti-concentration is needed. Handle `h=0,1`, `N=0,1`, and a zero collision factor explicitly; the denominator formula can be stated for `N≥2` and those small populations separately.

For the global mean `μ=E h`, fixed-column two-row counting gives `E choose(h,2)≤μ²/2`, hence `E edges≤μ² q₂/2`. Also `edges≤h` deterministically.

### E. Large-block density

Source: lines 1486–1569; old PDF Lemma 4.15(i), p.28.

The intended decomposition is: conditional atom bound for the translation × expected number of internal edges gives a pointwise edge probability; size and endpoint concentration restrict the relevant locations; square the pointwise bound and multiply by the window cardinality. The algebra gives `4cL−cF+2cE` when the required translation bound is actually valid. One must split the good-event and bad-event edge probabilities explicitly and sum the latter over `N−1` possible edges; they cannot simply be erased.

This original conclusion is false with the current `cF`; see the large-block counterexample below. A stronger intermediate estimate cannot prove a false conclusion. Excluding deterministic first-column mass or subdividing first by an appropriate good initial column changes the definition/decomposition and requires a new theorem, not an implementation shortcut.

### F. Small non-singleton density and low-fluctuation singleton classification

Source: lines 1571–1599; old PDF Lemma 4.15(ii)–(iii), p.29.

The intended small non-singleton argument replaces `E h²` by `N^O(δ)` while retaining translation atoms `N^(−cF+O(δ))` and a window `N^(cF+O(δ))`, giving `−cF+2cE`. The explicit threshold `cF≥δ−(log N)^(−1/2)` is used to keep the regular atom scale. This density conclusion is false; the simple two-row counterexample below certifies failure directly.

For the low-`cF` classification, constancy of `cF` and a **quantitative** fluctuation comparison at `v` are needed:

`cL(v)≤2cF + O_χ(1/log N)`.

Then `cF<δ−(log N)^(−1/2)` forces `cL(v)−cF<δ` for sufficiently large `N`, and the stable family is `{v}`. Merely writing `cF≥cL/2−o(1)` does not suffice: an arbitrary `o(1)` need not be smaller than `(log N)^(−1/2)`. The ambient definition only stipulates `E|B_w|=N^(b+o(1))`, so its ambient normalization error must also have a rate or be handled exactly before freezing the threshold claim. At the whole deck, `b=1` and the normalization is exact.

### G. Small singleton density

Source: lines 1600–1638; old PDF Lemma 4.15(iv), p.29.

Although the displayed proof goes through the false anti-concentration result, the conclusion has an alternate proof under the original small-size hypothesis. For any graph-block edge probabilities `p_m`,

`Σ p_m² ≤ (Σ p_m)² = (E edges)² ≤ μ⁴ q₂²/4`.

If `μ≤R`, this is at most `R² μ² q₂²/4`. Taking `R=N^(2δ+o(1))` gives `Σp_m²≤N^(2cL+2cE+4δ+o(1))/4`, which is the asserted exponent form. This argument needs neither singleton status nor endpoint smoothing. It uses the exact fixed-column factorial estimate, not an assumed replacement hypothesis. The exponent bound must be interpreted with an explicit upper error on `μ`, rather than unspecified finite-`N` equality.

### H. Terminal singleton density

Source: lines 1640–1660. There is no need to invoke the small-mean concentration lemma, which was only stated for nonterminal pairs.

If `|x|=K`, all rows in the cylinder have exactly the same full string. Therefore `edges=(h−1)_+` exactly and

`Σ_m p_m² ≤ Σ_m p_m = E edges = μ−P(h>0) ≤ μ`.

The empty tail gives `cE=0`; hence the original bound holds in a stronger form with no `O(δ)` loss beyond the ambient mean normalization. This works for arbitrary expected size and for `h=0` or `h=1`. No `FM` hypothesis is required for this deterministic/probabilistic bound; `FM` is used later only to make the exponent negative.

## Actual fixed-column counterexamples

### Minimal variance and deterministic-endpoint certificate

Take `k=3`, `K≥2`, and first-column counts `(a,b,c)` with all three positive. Let `x=y=z=(1)` in the whole ambient deck, and choose `χ` smaller than both outer proportions. This is an admissible nonterminal pair. Its left and right side means are exactly `a,c`, so the manuscript assigns fluctuation `sqrt(min(a,c))`. But its interval is exactly `[a+1,a+b+1)` for **every** admissible matrix. Both endpoints are deterministic, even conditional on internal information.

In the `a=b` reveal case (using `a,b` there as column indices), the residual population consists of all non-middle rows and `d₂` equals its entire size. The hypergeometric draw samples the whole population, so its variance is zero. The claimed positive variance lower bound and non-exhaustion fraction cannot hold.

A minimal concrete certificate suitable for finite Lean verification is `N=3`, first column `(1,1,1)`: the left endpoint of digit-1 rows is 2, and the residual draw has population 2, marked count 1, sample size 2, hence value identically 1 and variance 0. To see the asymptotic anti-concentration contradiction, use `N` divisible by 3 and counts `(N/3,N/3,N/3)`. Then the endpoint atom is 1 while the claimed atom scale is `N^(−1/2+O(δ)+o(1))`.

### Large-block density counterexample, including a valid large-time margin

Take `N` along an integer subsequence for which `n=N^(1/4)` and all specified cuts are integral. First cut: `((N−n)/2,n,(N−n)/2)`. Every later cut is uniform thirds. Choose `K=floor(T log N)` with fixed sufficiently large `T`. The limiting profile is uniform thirds, the first exceptional cut changes cell frequencies by only `O(1/log N)`, every column is good, and the global/recursive numerical margins can be made strictly negative by taking `T` large.

Again `v=x=y=z=(1)`. Then `cL=1/4`, `cF=1/2+o(1)`, and it is an immediate singleton stable block. It falls in the large-block case for `δ<1/8`. Its interval is deterministic with `n` vertices.

Let `q₂,q₃` be exact tail two-row and three-row coincidence probabilities. Uniform columns give `q₂=3^(−(K−1))(1+o(1))` and `q₃=3^(−2(K−1))(1+o(1))`. The pointwise integer inequality

`choose(z,2)−choose(z,3)≤(z−1)_+≤choose(z,2)`

implies

`choose(n,2)q₂−choose(n,3)q₃≤E edges≤choose(n,2)q₂`.

For large `T`, the triple term is negligible, so `E edges ≍n²q₂`. All these edges lie among the deterministic `n−1` positions; Cauchy therefore gives `Σp_m²≥(E edges)²/(n−1) ≍n³q₂² = N^(3/4+2cE+o(1))`.

The claimed large-block bound instead is `N^(1/2+2cE+O(δ)+o(1))`. Choosing `δ` sufficiently small leaves a positive exponent gap. This is a counterexample to the conclusion, not only to its proof.

### Small non-singleton density counterexample without asymptotic occupancy approximation

Let `N` be divisible by 12 and `K≥3`. Use first-column counts `(N/4,N/2,N/4)`, second-column counts `(2,(N−2)/2,(N−2)/2)`, and uniform thirds thereafter. Again all columns are good, the limiting profile is uniform, and large `T` gives the desired first-moment margins.

Take pair `y=z=v=(1)` and stable child `x=(1,0)`. Here `cF=log_N sqrt(N/4)=1/2+o(1)`, `cL(v)=log_N(N/2)=1+o(1)`, while `μ_x=1` and `cL(x)=0`. The parent threshold fails and the child crosses it, so this is a small non-singleton first-crossing stable block, with the high-`cF` condition satisfied.

Its left endpoint is always `m=N/4+1`. There are exactly two zero rows in the second column, so `Z=|B_x|≤2`, and

`P(Z=2)=(N/2)(N/2−1)/(N(N−1))→1/4`.

Conditional on `Z=2`, the two rows form an edge at `m` exactly when their tail strings coincide, an independent event of probability `q₂`. Consequently `p_m=P(Z=2)q₂` and `Σp_i²≥(1/16+o(1))q₂²=N^(2cE+o(1))`.

The claimed bound is `N^(−1/2+2cE+O(δ)+o(1))`, which fails for small `δ`. This exact two-row construction is also suitable for a finite fixed-column certificate.

## Required concentration and stable-block obligations before any freeze

1. Define the probability space exactly as independent uniform fixed-count columns, with column counts summing to `N`, and define all conditional sigma-fields. Fix one hypergeometric parameter order: the upper and lower text currently use different orders.
2. Prove prefix/prefix-family factorial moments and concentration under successive nonidentical thinnings, including zero means and random ambient populations. State rates, family cardinality and conditioning uniformity explicitly.
3. Prove stable first-crossing uniqueness, antichain coverage, equal-string edge containment, and terminal fallback handling, with `K=0` or `K≥1` fixed explicitly.
4. Distinguish retained-part coverage from full coverage. A polynomial discarded-mass error cannot be absorbed into a stretched-exponential localization error.
5. For the relevant-block count, establish half-mean endpoint deviation tails with an exponent strictly stronger than the relevance threshold, then group parents by depth. Treat fallback leaves separately or first prove their exclusion from `FM`.
6. For endpoint windows, start from the smaller side and propagate to the other endpoint. This is a repairable proof gap.
7. Do not freeze the original ambient anti-concentration, large density or small non-singleton density statements as attainable goals. Their counterexamples satisfy the structural assumptions, and increasing the mixing time does not remove the relative exponent failures.
8. If a repaired stopping rule or fluctuation definition is requested later, it needs a new independent review and freeze. No stronger input assumption is an acceptable workaround under the present task contract.

## Alternate-decomposition assessment with original definitions unchanged

There is no alternate decomposition that proves all original assigned conclusions: the density counterexamples are quantitative contradictions. The strongest useful surviving finite consequences established above are exact tail pair factors, exact prefix factorial moments, the conditional `choose(h,2)q₂` edge bound, the terminal identity `E edges=μ−P(h>0)`, finite retained-coverage union bounds, and the small-size `Σp²≤μ⁴q₂²/4` consequence. They can support honest partial formalization and explicit counterexample certificates. They cannot be described as completion of the original upper first-moment proof.

## Subsequent independent review of proposed contract D1–D8, F01–F33

After completing and saving the independent reconstruction above, I read `pre_freeze_contract.md` at the parent's request. **Approved mathematically as a finite partial contract, with no theorem or assumption changes required.** It does not assert completion of the original asymptotic goals. In particular, it does not insert an unproved concentration, independence, uniformity or collision-factor hypothesis.

* D1 is an actual finite probability-law definition. Nonnegative normalized weights suffice for F01–F11. An empty sample type admits no such normalized law, so there is no missing empty-space branch. F11 remains valid for any target with decidable equality and any good event, without independence.
* F12 is finite interchange of summation plus the inclusion `H(ω)⊆s`; the inclusion is essential and is explicitly frozen. F13 applies `0≤P≤1` termwise and then F12. Empty `s` and empty `H` are included.
* D2–D5 are more general than the source's sorted fixed-length finite-alphabet model, but F14–F25 hold on that larger domain, so this generality does not weaken a needed hypothesis. `Finset.range (N−1)` makes N=0 and N=1 edge sets empty. F14–F20 follow from the two membership predicates and equality substitution. F20 should be implemented as the stated biconditional, without silently adding sortedness.
* F21 is the injection `i↦(i,i+1)`. If `i<N−1`, both coordinates lie below N and `i<i+1`; these arithmetic facts also handle the otherwise impossible N=0 or N=1 premise. Equal rows and prefix membership are already in the edge definition. No collision independence is involved.
* F22 is F13 with the literal edge index range, F23 follows from F16 and monotonicity, F24 follows from F21 and monotonicity, and F25 combines F22/F24. Thus the claimed probability bounds hold for every finite deck law. F23 is the surviving finite terminal-density consequence, but constructing the actual shuffle law and translating its expected occupancy into the manuscript exponent remain outside this contract, as the contract correctly says.
* D6–D7 and F26–F28 describe exact first-column counts. The canonical three-interval column exists even at a=b=0. The zero-based endpoints a and a+b match the source's one-based endpoints after adding one. Neither condition b>0 nor sorting is needed for the empty-middle-cylinder endpoint count identities.
* F29–F30 follow from deterministic endpoints under every law on balanced columns. They apply to every good event, which certifies the actual obstruction rather than only a formal unconditional atom.
* F31 has the required a>0 so division by 2a has nonzero denominator. Positive outer counts and zero sampling slack coexist for **every** balanced column, including b=0. For a=0 the division identity as written need not hold, and that case is explicitly excluded.
* F32 is an unconditional arithmetic zero identity due to its final factor, including n=0 and n1>n. It is not presented as a hypergeometric law for invalid population parameters, so no hidden admissibility hypothesis is needed.
* F33 follows from F30 and q<P(S); it is valid also for an empty good event when q<0. At nonnegative q the premise itself forces P(S)>0, so no extra positive-mass hypothesis is needed.

Every named F statement has a direct finite proof from the frozen definitions and ordinary arithmetic/sum/finite-set facts. I found no mathematical reason to revise the current F01–F33 contract. The report's second-column-size-two construction additionally disproves the original small non-singleton density claim, but that fuller fixed-column product-model certificate is correctly left outside F01–F33 rather than introduced as an assumed interface.
