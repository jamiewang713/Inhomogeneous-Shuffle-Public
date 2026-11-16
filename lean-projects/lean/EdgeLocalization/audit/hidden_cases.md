# Independent hidden-case audit before freezing statements

This report was prepared independently from the three permitted mathematical sources. No other agent's report was read, and no Lean code was written. The mathematical-paper skill's audit checklist was applied. Locations below refer to the supplied TeX line numbers or the printed pages and lemma numbers in the two supplied PDFs.

## Outcome

The supplied definitions do **not** support all assigned conclusions. The endpoint anti-concentration theorem is false, and the large-block edge-density estimate itself is false, even for a homogeneous, strictly positive, locally good deterministic cut sequence satisfying the first-moment margins. Thus replacing a proof sketch by more detailed Lean tactics cannot complete the assigned statements unchanged.

Several useful conclusions survive with exactly the original shuffle model: the internal collision estimate, occupancy domination, terminal singleton estimate, and small singleton estimate. Their proofs need no endpoint anti-concentration. The localization coverage statement also contains an independent false claim: a polynomial truncation loss is promoted to an exponentially small failure probability.

## Whole-proof roles and dependency structure

1. Common data are a deck size, alphabet, deterministic integer column counts, independent uniform column permutations, sorted full strings, and the shuffle graph. A fixed legal prefix determines a random contiguous interval and an internal shuffle subgraph. Two independent copies turn expected shared-edge counts into a sum of squared marginal edge probabilities.
2. The upper bound passes through graph representation, a truncated chi-square estimate, a sparse-component factorial estimate, and an exponential moment of shared edges. The exponential moment uses directional exploration, conditional preservation of column profiles, an ambient first-moment estimate, and a Portenko-type iteration.
3. The ambient first moment splits the legal tree by left/right boundary stops, then by the stable stopping rule. Truncation bounds the number of boundary/profile classes. Profile entropy and cost inequalities feed the numerical margin lemma. Per-edge localization limits the number of stable summands at one edge; the large, small non-singleton, small singleton, and terminal estimates bound each summand; numerical margins then sum the classes.
4. Reduced global margins are derived from local margins and accessible ambient exponents. Monotonicity and the dominance of the two auxiliary margins yield the reduced upper threshold.
5. The matching lower bound has a separate largest-prefix branch and a cold-spot branch. Successive hypergeometric thinning supports the largest-prefix obstruction. In the cold branch, entropy inequalities produce a buffered witness, tilted prefix/type estimates construct cold intervals, a bridge and relative endpoint theorem localize them, factorial moments and occupancy approximations produce many cold edges, and a translated Lalley ascent test separates the shuffled law from uniform. The final case split is `Lambda0 >= kappa0` versus `Lambda0 < kappa0`, with `Lambda1 >= eta` forced in the latter branch.
6. The random-pile-size upper extension conditions on the realized cut sequence, invokes the **uniform** deterministic upper bound on the almost-like/local-good event, and averages total variation. Merely proving pointwise convergence for each deterministic sequence would not justify this step. No matching random-cut lower-extension theorem is supplied in the final lower-bound section; such an extension cannot be inferred by averaging deterministic total-variation lower bounds without a common separating test.

Assigned-theorem dependency map:

| Assigned result | Required earlier objects/results | Audit status |
|---|---|---|
| Stable localization coverage | Legal-word antichain partition; boundary decomposition; union bound; truncation accounting | Stated coverage false after truncation and outside an ambient interval |
| Number of relevant stable blocks | Stable parent inequality; order/disjointness at each depth; quantitative endpoint tails | Sketch lacks the necessary scale and order proof; `K=0` exception |
| Endpoint windows | Prefix-piece decomposition; one-sided count concentration; a precise ambient conditioning convention | Some proof steps invalid; conditioning/centers ambiguous |
| Conditional endpoint atoms | One-column hypergeometric atom bound; measurable revealing fields; positive variance and both population complements | False for supplied definitions |
| Large-block density | Translation conditional on internal information; endpoint atoms; occupancy/collision estimate; deterministic window | Conclusion false for supplied definitions |
| Small non-singleton density | Same atom estimate; small occupancy moment; window | Same obstruction; an explicit inhomogeneous variant is given below |
| Small singleton density | Pair collision estimate and a finite-sum inequality suffice | Recoverable without endpoint input |
| Terminal singleton density | Edge count bounded by occupancy | Recoverable without concentration or a small-mean assumption |
| Internal shuffle-graph edges | Equal-string components; unordered equal-row pairs; independence of future columns | Recoverable, with empty and one-row cases explicit |

## Source comparison: the missing deterministic first-column issue

The 2025 paper explicitly addresses this issue. Definition 4.3 (printed pp. 18–19) starts boundary crossings after column 1, and the fluctuation maxima range over `2 <= i <= M_y` and `2 <= i <= M_z`. Proposition 4.2 requires a chi-good first shuffle. In the proof of Lemma 4.5 (pp. 20–22), the population remains the entire `N`-row population, whereas the selected first-digit slice has size `N' = n^(1)_{x[1]} <= (1-chi) N`. The estimate `a2 + |R1| <= N' <= (1-chi)N`, and its analogues, provide actual unused population. The discussion preceding Definition 4.7 (p. 23) expressly says deterministic first-column counts cause fixed locations and that randomness starts at the second digit.

The supplied TeX instead includes the **first** column after the ambient prefix in the boundary stops and fluctuation maxima (lines 534–545, 604–639). It then resamples inside the ambient population (lines 1288 onward). These are substantive changes. Genuine side mass on both sides of a digit does not imply the sampling fraction is bounded away from 1.

The 2021 paper has independent, multinomial row strings. Its Lemma 4.13 (pp. 24–25) uses an explicitly binomial conditional location and separately handles deterministic extreme-prefix locations. Its stable definition ensures those extreme cases have small fluctuation exponent. That argument cannot be imported into fixed-column-count shuffles while retaining the TeX's new fluctuation definition.

## Counterexample 1: the endpoint atom theorem is false

Take the whole deck `w = empty`, `k = 3`, `N` a multiple of 3, and every column count equal to `(N/3,N/3,N/3)`. Let `K >= 2`, `chi < 1/3`, and

```
y = z = x = (1).
```

Both boundaries cross genuinely at column 1. The pair is admissible, nonterminal, retained, and fluctuation-regular. The left and right pieces each have expected size `N/3`, hence

```
cF = (1/2) log_N(N/3),   cL(x) = log_N(N/3).
```

Both endpoints of the interval occupied by strings starting with 1 are deterministic, because the first-column pile sizes are deterministic. The internal information can be interpreted as either a multiset or labelled pre-sort rows; the conclusion is the same. For any good event `S_x` with probability tending to 1, at least one positive-probability value of the conditioning information has conditional probability of `S_x` tending to 1. The conditional maximal endpoint atoms therefore cannot be bounded by `N^(-1/2 + O(delta) + o(1))` with delta sufficiently small. Integrating the two claimed atom bounds would already contradict `2 P(S_x) -> 2`.

The failure is visible inside the proposed `a=b` hypergeometric calculation: with `a=b=1`, `d2 = N - n_1^(1)` equals the entire remaining population, so the sampling complement is zero and the variance is zero. The ambient-transfer assertion that this complement is at least `N^(-O(delta)-o(1))` is false.

This example can have arbitrarily many uniform future columns, so almost-like cuts, all-tail local goodness, and the upper first-moment margins do not remove it. The endpoint lemma also applies to arbitrary `x in A`, not only stable `x`, so no stable-membership issue affects this counterexample.

## Counterexample 2: the assigned large-block density conclusion is false

Use the whole deck, `k=3`, `N` divisible by 10, homogeneous deterministic proportions

```
p = (4/5, 1/10, 1/10),   T = 5,   K = floor(5 log N).
```

Fix `chi < 1/10`. All columns are good and the cuts have the constant profile. Let `v=y=z=(1)` and let `x` be `1` followed by zeros, stopped at its first stable crossing. Put

```
a = log(5/4),   psi = log(50/33).
```

The definitions give

```
cF = (1/2) log_N(N/10) = 1/2 + o(1),
cL(x) = 1/2 + delta + o(1),
M_x / log N = (1/2 - delta)/a + o(1),
cE(x) = -psi (5 - (1/2 - delta)/a) + o(1).
```

This is a nonterminal first-crossing block, and is in the large case for sufficiently small delta. The left endpoint of `B_x` is the deterministic rank `m=4N/5+1`, because its digits after the initial 1 are all minimal digits.

Let `Z` be the occupancy of the full word `xi=(1,0,...,0)` of length K. Then `Z>=2` puts the edge `(m,m+1)` in `G_{B_x}`. Its mean satisfies

```
mu_N = E Z = (N/10)(4/5)^(K-1) = N^(1-5a+o(1)) -> 0.
```

For `r=2,3`, fixed-column factorial moments give

```
E (Z)_r = (N)_r [(N/10)_r/(N)_r] [(4N/5)_r/(N)_r]^(K-1)
          = (1+o(1)) mu_N^r.
```

The elementary pointwise inequality

```
1_{Z>=2} >= ((Z)_2 - (Z)_3)/2
```

therefore proves `P(Z>=2) >= (1/2+o(1)) mu_N^2`. In particular the squared edge-density sum is at least

```
N^[4(1-5a)+o(1)] = N^[-0.4628710262...+o(1)].
```

The exponent in the claimed large-block upper bound, as delta tends to zero, is

```
3/2 - 10 psi + psi/a = -0.7930551698...
```

There is a strict gap of `0.3301841435...`. An `O(delta)+o(1)` loss cannot close this gap when delta is chosen sufficiently small with the meaning prescribed in the source's parameter hierarchy.

This is not an example excluded by the first-moment margins. Here `beta(5)=1-5a=-0.1157177565...`. Taking theta=4 in the infima gives an upper bound for the first numerical margin with maximum

```
max(7/2 - 10 psi, (7/2) beta(5))
= max(-0.6551544396..., -0.4050121479...) < -0.4.
```

Indeed `psi_4 >= 2 psi_2`, so for each s the maximum in u occurs at u=s. The analogous theta=4 bound for the second margin has maximum at s=T and equals `(3/2) beta(T)<-0.17`; the third margin has maximum `beta(T)<-0.11`. Thus `FM(0,1,5,0.1)` holds, with room for the approximation errors. The case is admissible without any exceptional digits before the stopping time.

The conditional atom estimate also fails for this actual stable x: its left endpoint is deterministic even though `cF -> 1/2`.

## Counterexample 3: a small non-singleton variant

Start with the preceding homogeneous sequence. At a time `j_N` just before the zero branch would first cross the stable threshold, replace a single column by one whose zero-pile fraction is chosen so that the occupancy mean of `x=1,0,...,0` of length `j_N` is asymptotically constant. The zero pile has order `N^(1/2-delta)` and the other two piles split the remaining rows approximately equally. Choose `j_N` with

```
(j_N-1)/log N = (1/2-delta)/a + o(1)
```

and with its parent still satisfying `cL(parent)-cF >= delta`. Integer rounding can be done on the positive pile sizes; it changes logarithmic exponents by o(1).

The new column is chi-good, and a single changed column changes every profile cell count by only `1/log N`. Thus the same constant macroscopic profile and strict margins remain applicable. The pair is still `y=z=(1)` and `cF -> 1/2`. The chosen x is a first-crossing descendant with `cL(x)=o(1)<2delta`, so it is small non-singleton, and its one exceptional digit is retained by the exceptional-profile cutoff.

Its deterministic left endpoint remains `m=4N/5+1`. For the full zero-tail word, the factorial-moment lower bound now gives squared density at least

```
N^[2 - 20a - 4delta + o(1)].
```

At delta=0 the exponent is `-2.4628710262...`; the claimed small non-singleton exponent tends to

```
-1/2 - 10psi + psi/a = -2.7930551698....
```

The same strictly positive exponent gap remains. This construction is recorded as an asymptotic counterexample schema; the homogeneous large-block example above is already sufficient to disprove completion of the original assigned theorem collection.

## Localization and relevant-block count

### Coverage outside the ambient block

Lines 1438–1455 quantify over every `m in {1,...,N-1}` while taking unions only inside one fixed ambient prefix. Even after recentering, that ambient interval need not contain m. For example, a uniform binary first column and `w=(0)` give an ambient interval of deterministic length `N/2`; `m=N-1` is never in any of its stable intervals. The claimed failure probability is then 1. This is a statement-domain issue, not an endpoint-concentration issue.

### Truncation does not have exponentially small failure probability

The bad-profile lemma provides an expected mass/edge error of `N^(-C0)`, not `exp(-N^(delta-o(1)))`. The proof at lines 1463–1472 excludes that loss and then states an unconditional coverage bound that omits it.

A whole-deck counterexample is available with fixed positive proportions `(chi/2, 1/2, 1/2-chi/2)`. Every column is good. Let q be just larger than `C log N/log(1/chi)` and smaller than K, which is possible after choosing chi sufficiently small. If any row starts with q zeros, the lexicographically first row does too and its left boundary stop is inadmissible. Its rank 1 is consequently outside all retained admissible cylinders. The expected number of such rows is `N(chi/2)^q=N^(-O(C))`, and its second factorial moment is at most the square of its mean. The probability that it is nonzero is bounded below by `mu/(1+mu)`, a polynomial in N. This is much larger than the displayed exponential failure probability. No profile assumption in the source turns this polynomial event into an exponential one.

### Parent counting needs a different quantitative lemma

* Parents of different first-crossing leaves need not be an antichain: one can be an ancestor of another when one child crosses early and another continues. A per-depth grouping can justify a K factor, but it must precede the ordered-disjoint argument; the present proof first asserts at most two parents globally and only then appends K.
* The proposed contradiction compares a relevance threshold `exp(-N^delta)` with an upper tail `exp(-N^(delta-o(1)))`. The latter is **larger**, in general, and does not contradict relevance. A truly stronger tail, with its constants and slack fixed, is needed.
* The parent gap is `cL(parent)-cF >= delta`; the displayed endpoint window is `N^(cF+O(delta)+o(1))` with no constant controlled below that gap. It does not by itself yield an ordered separation estimate. A finite quantitative concentration theorem with an adjustable deviation parameter is needed.
* Terminal pair families have one element. If `K=0`, the claimed upper bound `2Kk` is zero; for the root block with `N>=2`, the relevant family has one element. The asymptotic regime can ensure `K>=1` eventually, but a finite theorem must expose that case.
* A nonterminal pair may have a singleton stable family because it crosses initially; first-crossing families can also have only one leaf when legal branching is unary. The test `A_stable={v}` is different from merely `card A_stable=1`.

The deterministic statement “an equal-string graph edge with one endpoint in a prefix cylinder has both endpoints there” is sound. It needs sorted row equality and prefix membership, and should be proved independently of probabilistic localization.

## Endpoint-window and conditioning obligations

These issues are in addition to the atom counterexample.

1. `cF` is the **minimum** of two one-sided exponents. Lines 1268–1271 incorrectly say each left piece is bounded by `N^(2cF)`. Only pieces on the side realizing that minimum have that bound. For the whole deck, one may choose the smaller side and transfer to the opposite endpoint using the block occupancy; this is a proof correction, not an extra assumption. Both orientations must be written explicitly.
2. In an ambient block, recentering removes its left translation but does not make its random size deterministic. A right-oriented endpoint decomposition contains that ambient size. Conditioning on an actual revealed ambient row set would fix it, but then the conditional means and exponents must be related to the original expected-size parameter. The sentence `|I(B_w)|=N^(b+o(1))` is not true identically under the stated definition `E|I(B_w)|=N^(b+o(1))`.
3. Conditioning on a deterministic cylinder `B_w` is not itself a sigma-field specification. The exact revealed information, conditional law, conditional expectations, and centering convention must be fixed before Lean statements are frozen.
4. The ambient-transfer lemma claims that there are only `N^o(1)` relevant prefix sets after profile truncation. There are `N^o(1)` profile **classes**, but a class can contain polynomially many distinct prefixes. The total number of legal prefixes is still `k^K=N^O(1)`, which can be absorbed in a sufficiently strong exponential union bound; the specific subpolynomial count claim is unsupported.
5. A global chi-good column can have a monochromatic or empty realized restriction to a small ambient row set. Genuine global side mass does not prove non-exhaustion of the conditional hypergeometric population. For active anti-concentration this must be established quantitatively, not assumed under the name “conditioning transfer.”
6. The good event used for a conditional atom theorem need not be measurable with respect to the finer revealing field if the argument bounds `P(Y=q,S | F)` by `P(Y=q | F)`, but the stated variance lower bound must hold for every finer-field value whose intersection with S has positive conditional probability. A bound only on an unconditional high-probability set, with no such measurability or support statement, is insufficient.
7. `U_x` must not contain sorted positions. If “rows” means the row multiset or original labels, the internal graph is determined up to translation; if it includes sorted ranks, the endpoints are already measurable. The 2025 paper explicitly uses a multiset.
8. With empty occupancy, the interval still needs a canonical left and right endpoint; interpreting an empty set as an arbitrary half-open interval makes endpoint statements meaningless. The rank-before-prefix count supplies canonical equal endpoints.

## Hidden quantitative issue in the low-fluctuation singleton implication

Lines 1585–1592 infer an exact singleton conclusion from

```
cF < delta - (log N)^(-1/2),
cF >= (1/2)cL(v) - o(1).
```

This inference is invalid for an unspecified o(1): that error need not be smaller than `(log N)^(-1/2)`. The whole-deck exact expected-size identity and fixed chi would give an explicit `O(1/log N)` error and repair the implication there. The source's ambient definition permits an arbitrary expected-size discrepancy `e_N=o(1)` through `E|B_w|=N^(b+e_N)`.

At the level of the stated estimates, take `cL(v)=2delta`, `cF=delta-2/sqrt(log N)` and allow the fluctuation-comparison error `2/sqrt(log N)`. The initial gap exceeds delta; a legal small-pile child can cross the threshold. Then it is false that the stable family is `{v}`, although the stated comparison and low-fluctuation test both hold. The ambient-exponent error is exactly a source of this discrepancy. An explicit rate is absent and cannot be silently frozen as an assumption.

The first-moment proof routes all remaining small nonterminal cases through this implication, so this is also a coverage issue for its case split.

## Exact finite survivors and a different decomposition

Let Q be the occupancy of a prefix x and let `H_x` be its internal graph. For every realization,

```
0 <= |E(H_x)| <= Q,
|E(H_x)| <= binom(Q,2).
```

The first inequality follows by decomposing occupied full-string classes: each class of size q contributes `max(q-1,0)` adjacent edges. The second follows by injecting each adjacent equal-string edge into an unordered equal-row pair. These are valid for `Q=0` and `Q=1` with zero edges, including empty prefixes and terminal words.

For `N>=2`, define the tail two-row collision probability

```
D_x = product_{j=M_x+1}^K
        [sum_l n_l^(j)(n_l^(j)-1) / (N(N-1))].
```

Given the first `M_x` columns, future columns are independent uniform column permutations. Every fixed unordered pair of rows in the prefix set has conditional tail-collision probability `D_x`. Consequently

```
E[|E(H_x)| | first M_x columns] <= binom(Q,2) D_x.
```

Conditioning only on Q gives the same inequality; cases where `P(Q=q)=0` must be expressed almost surely or handled by finite conditional sums. If a tail column has all selected digit piles of size at most 1, its pair-collision factor may vanish, and the graph has zero relevant duplicate edges. Empty tail products equal 1. No independence between the eventual concentration event and the tail strings is needed if one bounds that event by the event `{Q <= size bound}` before averaging.

Writing `mu=E Q`, fixed-column prefix pair probabilities satisfy

```
E[Q(Q-1)] <= mu^2,
D_x <= product_{j>M_x} sum_l (n_l^(j)/N)^2 = N^cE(x).
```

Here the one-column inequality is `(n)_2/(N)_2 <= (n/N)^2`, valid for `0<=n<=N` and `N>=2`; zero and one-card piles cause no difficulty. The stronger factorial formula should be proved directly from the uniform column-permutation model rather than imported from a different distribution.

If `p_m=P((m,m+1) in E(H_x))`, then finite sums give

```
sum_m p_m^2 <= sum_m p_m = E|E(H_x)| <= mu,
sum_m p_m^2 <= (sum_m p_m)^2 <= (mu^2 D_x / 2)^2.
```

These yield two assigned results without any additional assumption:

* **Terminal singleton:** `M_x=K` gives `cE=0`, and the first finite inequality gives `sum p_m^2 <= mu = N^(cL+o(1))`. The proof at lines 1656–1658 incorrectly invokes a small-mean estimate without a small-mean hypothesis; the direct occupancy domination proves the actual conclusion for every terminal block, large or small.
* **Small singleton:** if `cL<2delta` and `mu=N^(cL+e_N)`, the second finite inequality yields `sum p_m^2 <= N^(2cL+2cE+4delta+4e_N)/4`. This is the advertised `N^(2cL+2cE+O(delta)+o(1))`, and it actually holds for every small prefix, without singleton status. Thus the assigned singleton theorem can be proved as a consequence while keeping its original hypotheses. There is no need to add a conditional atom hypothesis or use the false endpoint theorem.

For `N=0` or `N=1` there are no path edges. A finite combinatorial version should prove that separately. Logarithmic exponents belong only to the `N>1` asymptotic layer. The source's probability setup itself uses division by N and `log_N`, so one should not pretend its formulas already define the zero-deck case. For `K=0`, the sole legal full word is empty, every row string agrees, the root graph is the full path, and the empty tail factor is 1. The exact inequalities above remain valid.

## Freeze requirements and recommendation

Before any Lean implementation, resolve or record as blocked the false source conclusions rather than turning them into hypotheses:

* Do not assume the supplied endpoint atom theorem, ambient non-exhaustion statement, or large/small non-singleton density theorem as an interface: that would merely conceal the gap behind unproved assumptions.
* Do not modify cF to omit an initial column, require a good first ambient column, enlarge the resampling population, restrict the ambient conditioning, or weaken the localization error without explicitly recording that these differ from the source. The 2025 paper suggests a repair direction, but it is a changed mathematical contract.
* The exact finite collision/occupancy lemmas above can be frozen honestly. Their mathematical assumptions are already consequences of the given shuffle model, not new distributional hypotheses. Their empty, singleton, terminal, zero-collision-factor, and empty-tail cases can be formalized explicitly.
* The strongest immediate genuine counterexample certificate is the deterministic first-column endpoint example, followed by the homogeneous large-density asymptotic example. The latter demonstrates that a new decomposition preserving all original definitions cannot prove every assigned conclusion.

Independent report complete. This report is ready to compare against the reconstruction and theorem-design reports before freezing any Lean statements.

## Review of the proposed finite contract after independent completion

After finishing the report above, I read `pre_freeze_contract.md` and independently checked D1–D8 and all statements F01–F33. They are valid for their stated domains. The finite-law assumptions contain normalization and nonnegativity only; the deck representation makes no unproved sorting, fixed-count, or independence claim. The edge estimates are universal exact inequalities and do not covertly import the blocked asymptotic theorems.

The checks include `N=0`, `N=1`, empty index sums, the empty prefix, arbitrary row-list lengths, zero-probability events, `a=0` or `b=0` in the balanced column construction, and the positive-denominator use in F31 when `a>0`. F32 is solely a zero arithmetic numerator, so it need not assume valid hypergeometric population parameters.

Two clarification-only changes were requested before freeze:

1. Write `Finset.range (N-1)` explicitly in D4/F15. The informal inclusive display `{0,...,N-2}` can be misread under truncated natural subtraction for `N<=1`, even though the prose intends an empty range.
2. If F31's conclusion includes positive side counts of a column, quantify `c : BalancedColumn(a,b)` explicitly. Its existing `a>0` assumption supplies the nonzero real denominator.

Subject to these clarifications, this reviewer approves the finite contract. This approval does not cover the original asymptotic stable localization, relevant-block count, endpoint atom, large-block density, or small non-singleton density conclusions. Nor does it certify the separately listed unimplemented product-collision law or exponent translation.
