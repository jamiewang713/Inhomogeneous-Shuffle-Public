# Whole-source reread: meaning of the small non-singleton estimate

This responds to the user's instruction to reread the entire TeX and identify the result's intended meaning. It is a mathematical interpretation and proof-dependency audit, not a new frozen contract or a claim of additional Lean verification. The source, frozen contract, and Lean implementation have not been changed.

The root agent read lines 1–5221 in source order, including the commented earlier lower-bound outline at 2562–2785. Three independent agents also reread the full source, respectively reconstructing the argument, designing its interpretation as a theorem statement, and auditing hidden assumptions. Their reports accompany this file. The comparison with the older fixed-column argument uses only the permitted `2510.22783v1.pdf`, especially Sections 3.1 and 4.1–4.2, pages 12–13 and 18–23.

## What the result is intended to measure

For a fixed deterministic prefix x, write

\[
 e_x=|E(G_{B_x})|,\qquad
 p_x(m)=\mathbb P((m,m+1)\in E(G_{B_x})),\qquad
 D_x=\sum_m p_x(m)^2.
\]

The quantity D_x is the expected number of shared edges in the x-blocks of two independent matrices, on the same position coordinates. It is not the expected number of edges in one block and is not a bound on an individual realization. The passage from squared probabilities to overlap is explicit at lines 1837–1841; the blockwise version follows by exactly the same independence argument.

“Small” means c_L(x)<2δ, a bound on the exponent of the expected block size. “Non-singleton” means the stable prefix family is not {v}, where v=y∨z. It does not mean that the realized block has at least two rows. See the stopping definition at 656–694 and the case statement at 1499–1511.

The intended −c_F factor is a spatial spreading gain. Conditional on the internal contents U_x, the relative internal graph is fixed, while its location is supposed to remain random (1530–1541). If its expected edge count is approximately N^{c_E} and its position is spread over approximately N^{c_F} sites, the heuristic is

\[
 p_x(m)\lesssim N^{c_E-c_F},\qquad
 D_x\lesssim N^{c_F}N^{2c_E-2c_F}
 =N^{2c_E-c_F}.
\]

The estimate is unconditional after averaging over U_x. Conditioning is a proof device, not a restriction in the displayed theorem. The restriction to a good event is also a proof device with an error that must be estimated; it cannot silently remove examples from the theorem.

## Its place in the whole proof

The upper-bound chain is:

1. Fixed-count independent columns define sorted strings and the shuffle graph (386–439).
2. Boundary pairs and stable prefixes partition the relevant strings; exceptional data are discarded with a separately controlled error (521–1119).
3. Per-edge localization controls how many block probabilities must be added before squaring (1436–1484).
4. A profile class contains at most N^{H_x+o(1)} prefixes. The quantity actually used for the small branch is therefore N^{H_x}D_x (1817–1913, specifically 1886–1892).
5. The numerical lemma makes this class contribution decay; subpolynomial bookkeeping then gives the first moment of all shared edges (1662–1913).
6. Conditional preservation and the recursive first-moment margin allow the argument to be used during exploration; exponential moments, sparsity and truncation yield total-variation convergence (1923–1997).
7. Random pile sizes are handled by a uniform deterministic bound on typical realizations followed by averaging (1999–2015).

The later reduction proves Λ₂≤Λ₀ and Λ₃≤Λ₀ (2397–2468). Thus the small-block and singleton margins are auxiliary. Only the largest-pile margin Λ₀ and the large-block margin Λ₁ affect the upper threshold. This is significant: failure of a sharper individual small-block estimate need not prevent the small-block contribution required by the final argument from being bounded.

The active lower proof confirms this division. It has a largest-prefix obstruction and a cold-spot obstruction corresponding to Λ₀ and Λ₁. Its explicit import list (2842–2884) does not import upper endpoint anti-concentration or the edge-density lemma. It proves relative endpoint concentration separately, retains the ambient position L_{a_s} as an unknown translate, and scans over possible translates (3449–3451, 4123–4223, 4899–4948, 5115–5162). Its definition of the actual location-variance exponent c_loc (3362–3373) does not redefine the upper c_F.

The random lower-bound assertion occurs in the inactive earlier outline (2732–2747). The active expanded lower theorem is deterministic. This distinction is part of the whole-proof dependency map; the upper random-pile averaging step does not establish the lower mixture assertion.

## What the old proof explains about the intended fluctuation scale

The older fixed-column paper explicitly separates the first digit from random location fluctuations:

- Section 3.1 first obtains a good initial shuffle through a proved total-variation reduction.
- Definition 4.3 starts boundary crossings after column 1.
- Its fluctuation maxima start at column 2. The first-column cumulative count is a deterministic offset in the endpoint decomposition.
- Lemma 4.5 resamples a later column in the whole population N. The first-digit slice has size N′=n^{(1)}_{x[1]}≤(1−χ)N, providing a genuine complement in the hypergeometric variance.
- The discussion after Definition 4.7 explains that fixed first-column sizes make positions begin behaving randomly at the second digit; first-digit boundary strings require separate treatment.

This supplies a coherent intended reading: c_F should measure randomness remaining in the translation after the deterministic first-column structure is accounted for. A large deterministic cumulative pile size is not itself a source of positional randomness.

The new TeX's local-good-shuffle remark (311–313) points toward this initial-shuffle reduction. However, its written definitions permit the first post-ambient column to be a boundary crossing and to attain a fluctuation maximum (533–650); the whole-deck ambient is explicitly w=∅ (496–497). Its resampling paragraph restricts all sets to the ambient population (1290 onward). The rest of the file does not supply an initial-column exclusion or justify the necessary complementary population fraction.

Accordingly, the intended smoothing mechanism is identifiable, but simply treating the printed definition as though it excluded the first column would change a definition. Likewise, replacing c_F by the lower proof's c_loc, treating a random translation as deterministic in a squared-probability calculation, or declaring local good columns to be an anti-concentration theorem would not be legitimate interpretations of the existing statement.

The earlier explicit example still tests the printed stronger statement. It does not show that the small-block contribution required for the main upper theorem is unbounded, nor does it disprove the main upper theorem.

## Exact collision-pair estimate under the existing model

There is a direct alternative for the small branch that uses the stated fixed-column law and no additional distributional hypothesis. It also avoids converting a high-probability size bound into a moment bound.

Take N≥2 and a deterministic legal prefix x of length M≤K. Define

\[
 \mu_x=N\prod_{j\le M}\frac{n^{(j)}_{x[j]}}N,
 \quad
 a_j(x)=\frac{n^{(j)}_{x[j]}(n^{(j)}_{x[j]}-1)}{N(N-1)},
 \quad
 q_x=\prod_{j>M}\sum_\ell
       \frac{n^{(j)}_\ell(n^{(j)}_\ell-1)}{N(N-1)}.
\]

All terms are nonnegative. Each internal adjacent equal-row edge determines a different unordered pair of original row labels with the same full word and prefix x. Independence of columns and exchangeability of labels therefore give

\[
 \mathbb E e_x
 \le {N\choose2}\prod_{j\le M}a_j(x)\,q_x
 \le \frac{N-1}{2N}\mu_x^2q_x
 \le \frac12\mu_x^2q_x.
\]

Here a_j(x)≤(n^{(j)}_{x[j]}/N)^2 follows directly from 0≤n^{(j)}_{x[j]}≤N. Since every p_x(m) is nonnegative,

\[
 \boxed{D_x\le\Big(\sum_m p_x(m)\Big)^2
       =(\mathbb E e_x)^2
       \le\tfrac14\mu_x^4q_x^2.}
\]

Write D_x^rel for the separately defined density when each sample's positions are recentered at its ambient left endpoint. The same cardinality argument proves the same upper bound for D_x^rel. This does not assert D_x^rel=D_x: independently translating the copies can change which edges overlap. Neither bound requires independence between the ambient translation and the block contents. For N=0 or N=1 the internal edge set is empty, and that case is handled before division by N(N−1). A pile of size 1 or a zero tail coincidence factor can make the pair bound exactly zero; no positivity assumption for those factors is needed. The empty tail product is 1.

For the fixed ambient-prefix model, its expected-size assumption E|B_w|=N^{b+o(1)} and independence of later columns give μ_x=N^{c_L^{r,b}(x)+o(1)}. Also q_x≤N^{c_E(x)} by the same one-column pair inequality. Hence

\[
 D_x\le\tfrac14 N^{4c_L(x)+2c_E(x)+o(1)}.
\]

For every small block c_L(x)<2δ, this implies both

\[
 D_x\le N^{2c_E(x)+8\delta+o(1)}
 \quad\text{and}\quad
 D_x\le N^{2c_L(x)+2c_E(x)+4\delta+o(1)}.
\]

The second estimate recovers the printed small-singleton exponent, without using endpoint anti-concentration. The first estimate is weaker than the printed small non-singleton bound, but it suffices for the classwise contribution below.

For a terminal full-word prefix, a still simpler estimate is D_x≤E e_x≤μ_x and c_E(x)=0. This proves the terminal bound's finite probabilistic content without a small-mean assumption.

## Why the weaker small-block estimate suffices

Use β(s)=β_{r,b}(s) in this paragraph. Let v=y∨z and F=c_F(v;y,z). Let ε collect the existing profile replacement and vanishing errors; it is not a new hypothesis.

For a nonterminal stable family not equal to {v}, its initial stopping condition and the source's fluctuation comparison give

\[
 c_L(v)-F\ge\delta,\qquad
 F\ge\tfrac12c_L(v)-\varepsilon.
\]

Thus c_L(v)≥2δ−2ε, and the maximal-pile comparison gives β(s)≥−O(ε). After nonterminal terminal-fallback blocks are excluded by the existing tail-size argument, x is a first crossing. The parent condition gives S_x≤c_L(v)−F+O(ε). This remains true if the crossing digit is exceptional: adding that digit changes S_x by zero, as the source states at 1005–1007.

Choose θ=3 in the retained-profile entropy bound. The source's one-column inequality gives B₃(s,u)≥2A(s,u) and B₂(u,T)≥A(u,T). Consequently

\[
\begin{aligned}
 H_x+2c_E(x)
 &\le 3S_x-B_3(s,u)-2B_2(u,T)+O(\varepsilon)\\
 &\le \tfrac32\beta(s)-2A(s,T)+O(\varepsilon)\\
 &=2\beta(T)-\tfrac12\beta(s)+O(\varepsilon)\\
 &\le-2\eta+O(\varepsilon),
\end{aligned}
\]

using only the tail-size part β(T)≤−η of the already assumed FM condition. Combining this with the exact small-block bound yields

\[
 N^{H_x+o(1)}D_x
 \le N^{-2\eta+8\delta+O(\varepsilon)+o(1)}.
\]

The existing parameter hierarchy makes the exponent negative. This supplies the small non-singleton class contribution actually used at 1886–1892. It also works for low-F non-singletons directly, so the stronger assertion that all such blocks must be singletons is unnecessary for this alternative proof decomposition.

This is an alternative mathematical derivation of the required small-class conclusion under the original model assumptions, using the source's retained-profile estimates and cardinality bounds. Those dependencies still need their own Lean proofs. It is not a proof or a reinterpretation of the stronger displayed N^{−c_F+2c_E+…} inequality.

## Conditional use and formalization consequences

For a fixed deterministic ambient prefix w, the preceding exact calculation already applies to the full word x under the original unconditioned law. Conditional on all columns through |w|, the membership set of B_w is fixed with size h and future columns remain independent fixed-count columns on the whole population N. The conditional equal-pair expectation is choose(h,2) times the prescribed pair factors for |w|<j≤M and q_x. For h≥2 it is at most ((h−1)/(2h))μ_cond²q_x, where μ_cond=h times the product of later prescribed proportions. For h=0 or h=1 there are no internal edges. In every case the per-column sampling denominators remain N(N−1), not h(h−1). An unconditional expected ambient size cannot be substituted for h in this conditional statement without a further estimate.

If exploration instead produces a verified residual independent fixed-column model on M remaining labels with specified residual counts, the same finite calculation can be applied with those parameters. Arbitrary exploration conditioning does not automatically have this form. The conditional-preservation result at 1923–1943 still owes that verification and the exponent comparison; it cannot be replaced by an assumed interface.

The revised diagnosis is therefore narrower than the earlier completion audit:

- The small-block part needed by the full first-moment argument has a source-assumption-preserving mathematical route.
- The printed small-singleton and terminal estimates have direct finite collision/count proofs.
- The printed sharper small non-singleton statement remains a different, stronger claim.
- The large-block smoothing, relevant-block localization, and conditional exploration model still require their own reviewed arguments. This reread does not certify them or the whole upper theorem.
- No assumption, theorem statement, or definition in the existing freeze has been changed. No new Lean theorem has been implemented or counted as verified in this reread.

The correct next formalization boundary is the exact fixed-column collision calculation and the small-class conclusion actually needed by the full proof. Any decision to replace a printed theorem by that different conclusion must be explicit; an abstract anti-concentration hypothesis must not be inserted to conceal the missing proof.

## Comparison of the independent reports

All three independent reports were saved before their authors reviewed this synthesis. The root read and compared all three reports. Each reviewer then checked the finite pair bound, small-case exponents, case distinctions, and conditional-law scope in this synthesis.

| Review role | Independent conclusion | Comparison outcome |
|---|---|---|
| Mathematical reconstruction | The quantity is shared-edge overlap; the old proof uses a deterministic first-digit offset and a larger resampling population. Exact pair counting and θ=3 give the required small-class decay. | Agrees with the chosen decomposition; requested clearer source references and explicit outstanding profile/cardinality formalization. Both are incorporated. |
| Theorem-statement design | The printed −c_F statement is an unconditional per-prefix claim. Exact pair counting proves a weaker finite bound that the existing N₁ margin can absorb. | Independently verified the stronger θ=3/tail-margin calculation after comparison. Requested explicit conditional population sizes and coefficients; incorporated. |
| Hidden-case audit | The whole-file conventions do not remove deterministic first-column boundaries. The alternative handles zero/one-row cases, zero collision factors, exceptional stopping digits, and low-F non-singletons. | Agrees; requested separate notation for global and recentered density. D_x^rel is now distinguished from D_x. |

These comparisons validate the mathematical interpretation and alternative decomposition, not a newly frozen Lean theorem inventory. The existing 33-theorem implementation remains the only compiler-verified scope.
