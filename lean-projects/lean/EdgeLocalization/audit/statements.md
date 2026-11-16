# Independent statement-design report

Status: **pre-freeze; no Lean declarations or proof code written.** This report was prepared independently from the three permitted mathematical sources. It does not treat a missing upstream result as an assumption or replace a source statement by a repaired statement.

Sources inspected: `time_inhomogeneous_riffle_shuffle_unified_article.tex`; the text extractions of `2103.05068v3.pdf` and `2510.22783v1.pdf` under `audit/sources/`. The mathematical-paper skill and its required audit/writing instructions were also read. No other project proofs, audit reports, or mathematical sources were read.

## 1. Whole-proof structure

The old homogeneous model in 2103 uses independent row strings and binomial conditional shifts. The deterministic-column model in 2510 uses independent columns with fixed counts; its conditional shifts require hypergeometric arguments. The inhomogeneous article follows the latter model. Neither the independent-row law nor its conditional binomial law can be imported into the fixed-column model.

### Definitions and dependence

1. Deck size `N`, alphabet size `k`, time `T`, `K = floor(T log N)`, deterministic pile counts `n[j,l]`, and proportions `p[j,l] = n[j,l]/N` define the finite shuffle-matrix law.
2. The law defines lexicographically sorted rows, prefix cylinders `B_x`, occupancy `Y_x`, prefix intervals `I(B_x)`, shuffle graph `G`, internal graph `G_{B_x}`, and independent shared-edge count `|E(G) ∩ E(G')|`.
3. A profile `mu_t` and the one-column functions `a`, `psi_theta`, `I_theta`, and tilted entropy `H_theta` define integrated functions `A(r,s)`, `B_theta(r,s)`, and `J_theta(r,s)`.
4. A regular simplex partition, representatives, and a time mesh define almost-profile-like cuts, good columns, local good-shuffle assumptions, good/exceptional selected digits, and all Riemann-sum errors.
5. Ambient prefix `w`, birth index `M_w`, parameters `(r,b)`, and the finite counts define `c_L^{r,b}(x)` and `c_E(x)` for extensions of `w`.
6. `chi` and each column define its first/last pile of mass at least `chi`; these define left/right first-crossing prefix families and the boundary maps `L(omega), R(omega)`.
7. The boundary exceptional-digit threshold defines admissibility. Compatible boundary pairs define `v = y join z`, `A_{y,z}`, `s = |v|/log N`, and terminal/nonterminal cases.
8. The side-prefix families `P_{x,i}` and `Q_{x,i}`, their expected occupancies, and their maxima define left/right fluctuation quantities and extended-real `c_F`.
9. `c_L`, `c_F`, `delta`, and terminal status define the root-singleton, first-crossing `Gamma`, terminal-fallback `Lambda`, and stable family `A_stable`.
10. Time-cell/simplex-cell/digit counts and exceptional locations define the stable profile statistics `S_x`, `Q_x`, `R_x`, `H_x`.
11. Integrated costs and `(r,b)` define `beta_{r,b}`, the three local numerical margins, `FM`, accessibility, and `RFM`.
12. The whole-deck margins `Lambda_0,...,Lambda_3` and their maximum define the full and reduced upper critical times.
13. The lower proof defines a maximal-pile ambient prefix `a_s`, the witness function `F_theta`, integrated entropy and the exponents `h` and `Gamma`; truncated tilted types define cold prefixes and relative cold intervals.
14. A bridge word using two good columns and a 2-tilted tail class define collision-likely full words, occupancy events `A_y`, and their count `Z_theta`.
15. A relative cold set and its deterministic translates define the translate-scan ascent test. Independent component sorting from the graph representation connects this test to the shuffled permutation.
16. A distribution over deterministic integer cut arrays defines the random-pile mixture law. Randomized profile-likeness is a probability statement about those arrays, not independence of their entries.

### Upper-bound lemma graph

`fixed-column matrix law`
→ graph representation
→ truncated chi-square inequality and sparse factorial inequality.

`prefix tree + boundary definitions`
→ stable partition and global boundary decomposition.

`regular partition + almost-like cuts`
→ interval blocking and profile estimates
→ bad-profile/admissibility reduction and entropy class counts.

`one-step hypergeometric law`
→ one-step concentration and point-mass estimates
→ ambient conditioning transfer
→ size concentration, endpoint windows, conditional endpoint atoms.

`stable partition + endpoint windows`
→ relevant-stable-parent count
→ per-edge localization.

`independent future columns`
→ collision-pair formula
→ internal adjacent-edge estimate.

`internal edge estimate + conditional endpoint atoms + endpoint windows`
→ large-block density
→ small non-singleton density
→ small singleton density.

`occupancy and path-edge counting`
→ terminal singleton density.

`FM + profile estimates + stable stopping conditions`
→ fallback exclusion and numerical margin inequalities.

`localization + density cases + entropy counts + numerical margins`
→ ambient first moment.

`conditional preservation + RFM + ambient first moment`
→ conditional first moment during exploration
→ directional Portenko estimate
→ shared-edge exponential moment.

`regularity/sparsity + sparse factorial + shared-edge exponential moment + truncated chi-square`
→ deterministic upper bound.

`negative global buffered margins`
→ accessible local margins
→ deterministic upper bound at a fixed time.

`margin monotonicity + one-column dominance`
→ auxiliary margin dominance
→ full/reduced threshold identity
→ reduced upper critical-time theorem.

### Active lower-bound lemma graph

The old lower overview at TeX lines 2562–2785 is inside a `comment` environment. It is not the active lower theorem or a proved replacement for the later argument.

`fixed-column law + one-step concentration`
→ successive-thinning lower tail
→ iterated prefix-tree concentration
→ largest-prefix obstruction (`prop:largest-prefix`).

`one-column entropy inequalities + good-column bridge window + positive Lambda_1`
→ buffered cold witness (`lem:cold-witness`).

`cold witness + truncated tilted types + regular-cell estimates`
→ prefix type counts and cold-set geometry.

`iterated prefix concentration + relative endpoint decomposition`
→ uniform relative endpoint theorem
→ cold-prefix endpoint control.

`two good bridge columns + witness buffers + concentration`
→ bridge buffers
→ localization of every occurring cold full word in the random translate `H_{L_{a_s}}`.

`fixed-column factorial identity`
→ conditional factorial comparison and central-window comparison
→ two-category Poisson/occupancy approximation
→ first/second moment of `Z_theta`
→ cold collision count
→ many cold edges.

`uniform ascent concentration + component value-set bounded differences`
→ component-sorting concentration
→ Lalley component comparison
→ translate-scan Lalley test
→ cold-spot lower bound.

`largest-prefix case OR cold-witness case`
→ buffered reduced lower theorem.

This does not identify upper-edge anti-concentration as an input to the active lower localization theorem: that theorem uses its own relative endpoint theorem. A defect in upper endpoint anti-concentration therefore should not be silently propagated to all lower lemmas.

### Random-pile extension

The active TeX corollary supplies the upper extension. For every deterministic cut array in the typical event, the deterministic TV bound must be uniform. Convexity gives

`TV(mixture, uniform) <= P(atypical cuts) + sup_typical TV(deterministic law, uniform)`.

The inactive lower overview describes the different lower mechanism: take a union of cut-dependent rejection tests, and use a uniform-law false-positive bound strong enough to absorb the number of possible cut arrays. There are at most `(N+1)^(kK)` integer cut arrays, whose logarithm is `O((log N)^2)` when `K=O(log N)`. A stretched-exponential uniform false-positive bound suffices. Conditioning alone does **not** transfer TV convergence to 1 to a mixture. The present active TeX lower theorem is deterministic; an exact random lower theorem still needs its test family and uniform rate stated.

## 2. Exact common finite types for Lean statements

The following is a language-neutral specification, not Lean code.

* `N,k,K : natural`, with `N >= 2`, `k >= 2`; `K` may be zero for the finite collision/terminal identities.
* `n : {0,...,K-1} × {0,...,k-1} -> natural`, with `sum_l n(j,l)=N` for each `j`.
* `Column(j)` is the finite set of functions `f : {0,...,N-1} -> {0,...,k-1}` for which `#{a:f(a)=l}=n(j,l)` for every `l`.
* `Omega = product_j Column(j)`, equipped with its uniform probability law. Nonemptiness of every `Column(j)` and of `Omega` is proved from the count sums. This law equals the product of the uniform column laws.
* `row(S,a)` is the full word of row `a`. A prefix is a word `x` of length `M <= K`. Legal means `n(j,x[j])>0` for every `j<M`.
* `Y_x(S) = #{a : row(S,a) begins with x}`.
* `L_x(S) = #{a : prefix_M(row(S,a)) <lex x}` and `U_x(S)=L_x(S)+Y_x(S)`.
* `I_x(S) = {q : L_x(S) <= q < U_x(S)}`. This uses zero-based positions. It encodes source position `m` by `q=m-1`; source half-open endpoints are `iota_x=1+L_x`, `tau_x=1+U_x`. This is an explicit index encoding, not a change in the event.
* `sortedRows(S)` is the lexicographically sorted multiset of row words. Ties do not affect word values.
* `Edges_x(S)` is the set of `q` with `0 <= q < N-1` for which sorted words at `q,q+1` agree and have prefix `x`.
* `D_x = sum_{q=0}^{N-2} P(q in Edges_x)^2`.
* `Pairs_x(S) = #{(a,b) : 0 <= a < b < N, row(S,a)=row(S,b), row(S,a) begins with x}`.
* `lambda_x = product_{j<M} n(j,x[j])/N`.
* `q_j = sum_l (n(j,l)/N)^2`; `Q_tail(M)=product_{M<=j<K} q_j`.
* `r_j = sum_l n(j,l)(n(j,l)-1)/(N(N-1))`; `R_tail(M)=product_{M<=j<K} r_j`. Natural subtraction is used in `n(j,l)-1`; the whole expression is then coerced to nonnegative reals.
* Prefix history `F_M` is the finite partition generated by columns `j<M`.
* Internal information `UInfo_x` records the labelled set of rows with prefix `x`, and their continuation words after `M`. It is a finite-valued function on `Omega`. It determines `Y_x`, the internal sorted word list, and the internal relative edge set, but in general not `L_x`.
* Conditioning on a finite-valued statistic `Z=z` is a normalized restriction to that fiber. Statements on such fibers quantify only over fibers of positive probability. This is exactly the finite form of an almost-sure conditional statement, and introduces no statistical nondegeneracy assumption.

Ambient relative intervals require separate definitions: count rows in `B_w` whose extension is lexicographically before `x`. The source alternates between unconditional expected ambient size and conditioning on the realized ambient population; these laws must not be identified. The finite collision/terminal results below hold for global positions and also for intervals recentered by the ambient block's random left endpoint, because the proofs count each sample's internal edges before taking probabilities.

## 3. Source target signatures and freeze status

In this section `L=c_L^{r,b}(x)`, `F=c_F^{r,b}(x;y,z)`, `E=c_E(x)`, `v=y join z`. These abbreviations are not substitute assumptions. The full common source setting includes the fixed-column law, legal ambient prefix, defined admissibility/stopping rules, selected parameters and relevant almost-like/local-good hypotheses.

For an asymptotic statement of the form `quantity <= N^(exponent + O(delta)+o(1))`, an exact Lean formulation must provide a constant `C_loss` independent of `N`, the cut array, pair, prefix, and `delta`, followed by `for every eps>0 there exists N0 ... quantity <= N^(exponent+C_loss*delta+eps)`. `C_loss` may depend on parameters fixed before `delta`. A probability `exp(-N^(delta-o(1)))` similarly becomes `for every eps in (0,delta), eventually probability <= exp(-N^(delta-eps))`. The source does not provide a complete uniform error envelope or every necessary quantifier. This is a reason not to freeze an unjustified schema as a theorem.

### A. Per-edge stable localization

Source: `lem:ub-per-edge-stable-localization`, TeX 1436–1484; 2510 Lemma 4.10.

Definition for a fixed edge index `m`:

`Relevant(y,z,m) = {x in Stable(y,z) : P(m in I_x) >= exp(-N^delta)}`.

Required target components:

1. For every retained admissible pair and `1<=m<N`, `card Relevant(y,z,m) <= 2*K*k`.
2. For every `1<=m<N`, the probability that `m` is outside the union over all retained admissible pairs and their relevant stable blocks is at most `exp(-N^(delta-o(1)))`.
3. Pointwise in every matrix: if `(m,m+1)` is a shuffle edge and `m in I_x`, then both endpoints lie in `I_x` and the edge belongs to `Edges_x`.

Component 3 is an exact finite combinatorial lemma and can be frozen independently. Component 2 is not valid as literally written for an arbitrary ambient block and arbitrary `m` in `[N-1]`: `m` can lie outside the ambient interval. It also omits the polynomial loss from admissibility/profile truncation. An exact valid union bound is stated in section 6, with the omitted-coverage event exposed. That identity is not a replacement proof of the printed stretched-exponential conclusion.

### B. Number of relevant stable blocks

The count in A must be separate from the coverage union bound. Proposed dependency order:

* children inject into `parent × lastDigit`, with at most `k` children per parent;
* at each fixed parent depth, distinct parents define disjoint ordered cylinders;
* at each depth, at most two qualifying parents;
* sum over at most `K` depths;
* terminal and root-singleton cases have one element and are dispatched separately.

The two-parent assertion needs an endpoint deviation at half the middle parent's **expected interval length** with failure strictly less than the relevance threshold `exp(-N^delta)`. The article provides only `exp(-N^(delta-o(1)))`, which need not be smaller. Also the written endpoint window has an unspecified `O(delta)` exponent; it need not be below a parent gap of exactly `delta`. Thus the displayed estimate is not a sufficient quantified interface for this count. The old paper uses a concentration theorem with a free deviation/failure exponent and claims an `exp(-Omega(N^(2delta)))` comparison. That stronger intermediate estimate must be proved in the new setting, not assumed.

At `K=0`, a terminal stable family can have one element while `2Kk=0`. Any finite formalization must dispatch this case or derive `K>=1` from the eventual regime `T>0, N` sufficiently large. It must not silently use positivity of `K`.

### C. Endpoint windows and conditional atoms

Source: `lem:ub-ambient-concentration-anti-concentration`, TeX 1202–1434. The statement applies to **every** continuation `x` of a nonterminal retained fluctuation-regular pair, not just stable continuations.

Intended exact schema:

For each admissible nonterminal retained fluctuation-regular pair and each legal continuation `x`, there is an event `S_x`, measurable in the actual matrix space, with the stated uniform failure probability. On `S_x`, occupancy obeys the separate `L>=2delta` and `L<2delta` bounds, and

`abs(iota_x-E iota_x)+abs(tau_x-E tau_x) <= N^(max(F,delta)+C_loss*delta+eps)`.

For every positive-probability fiber of `UInfo_x`,

`max_j P(iota_x=j and S_x | UInfo_x) + max_j P(tau_x=j and S_x | UInfo_x) <= N^(-max(F,delta)+C_loss*delta+eps)`.

This signature is **blocked by a concrete counterexample**; see section 4. It cannot be frozen unchanged. The variance-transfer statement is also false on that example.

The proof splits into the cases `a>b`, `a<b`, `a=b` for fluctuation-maximizing column indices, plus reversal when the right fluctuation is the smaller one, plus low-`F`/high-`F` cases. Each revealing statistic must be explicitly defined as a finite function, and inclusion of `UInfo_x` in that information must be proved. Conditional means, selected-population sizes, and both complementary fractions must be computed on every positive-probability fiber. Cases with population `0` or `1`, zero successes, or fully selected populations cannot use a positive-variance theorem.

The endpoint-window proof also incorrectly bounds every left summand by the **minimum** of the two fluctuation scales. A possible proof must select the smaller side first, then obtain the other endpoint from the occupancy fluctuation and the appropriate fixed ambient total. For a random ambient population, the term coming from its total cannot be discarded.

### D. Large-block density

Source: first case of `lem:ub-edge-density-bounds`, TeX 1486–1495, 1543–1567; 2510 Lemma 4.15(i).

Quantify over nonterminal retained fluctuation-regular `(y,z)`, `x in Stable(y,z)`, `x not in Lambda(y,z)`, and the exact case condition `c_L(x)>=2delta`. Conclude

`D_x <= N^(4*c_L(x)-c_F(x;y,z)+2*c_E(x)+C_loss*delta+eps)`.

Dependencies: exact internal edge/collision bound; large-occupancy second moment; conditional endpoint-atom bound; endpoint window; stable inequality `c_L-c_F<delta`; conversion of products to `c_E`; explicit absorption of the exceptional-event contribution.

Status: **not freeze-ready**, because conditional endpoint atoms are false with the existing definitions. One must not put an `EndpointAntiConcentration` field into a context structure and call the target formalized.

### E. Small non-singleton density

Source: second case of the edge-density lemma, TeX 1496–1503, 1569–1583; 2510 Lemma 4.15(ii).

Same pair/prefix quantifiers as D; additionally

`c_L(x)<2delta`, `c_F(x)>=delta-(log N)^(-1/2)`, and `Stable(y,z) != {v}`.

Conclude `D_x <= N^(-c_F(x)+2*c_E(x)+C_loss*delta+eps)`.

Dependencies: small-occupancy estimate; collision bound; high-`F` conditional atom estimate; endpoint window; stable stopping. Status: **not freeze-ready** for the same upstream reason.

### F. Low fluctuation forces singleton

Source: third case of the edge-density lemma, TeX 1504–1506, 1585–1592; 2510 Lemma 4.15(iii).

Same pair/prefix quantifiers as D; assume the exact case conditions

`c_L(x)<2delta` and `c_F(x)<delta-(log N)^(-1/2)`.

Conclude both `x=v` and `Stable(y,z)={v}`.

This is a deterministic consequence of the stopping definition once an error-controlled inequality at `v` is available. The source's bound `c_L(v)<=2*c_F(v)+o(1)` by itself is insufficient: an arbitrary `o(1)` can dominate `(log N)^(-1/2)`. For whole-deck exact first moments, a genuine crossing gives the explicit error `log(1/chi)/log N`, which is sufficient. For an ambient exponent specified only through `E Y_w=N^(b+o(1))`, its normalization error is additional and has no stipulated rate. This ambiguity must be settled before freezing the displayed low-`F` threshold.

### G. Small singleton density

Source: fourth case of the edge-density lemma, TeX 1507–1513, 1594–1637; 2510 Lemma 4.15(iv).

Same pair/prefix quantifiers as D; assume `Stable(y,z)={v}` and `c_L(x)<2delta`. Conclude

`D_x <= N^(2*c_L(x)+2*c_E(x)+C_loss*delta+eps)`.

Dependencies: exact identity `x=v`; small-occupancy second moment retaining its mean factor; internal collision bound; conditional endpoint atoms at `max(c_F,delta)`; endpoint windows; elementary inequality from singleton stability. There are two distinct subcases `c_F>=delta` and `c_F<delta`, even though `max` packages the result. Status: **not freeze-ready** because of the upstream atom defect.

### H. Terminal singleton density

Source: `lem:ub-terminal-singleton-bound`, TeX 1640–1660.

Quantify over every terminal retained admissible pair, set `x=v`; derive `|x|=K` and `Stable={x}` from definitions. Printed conclusion:

`D_x <= N^(c_L(x)+c_E(x)+O(delta)+o(1))`.

This is **mathematically available without concentration**: `c_E(x)=0` and the exact finite bound is `D_x<=E Y_x=N*lambda_x`. Source proof invokes a small-mean estimate without stating a small-mean hypothesis, but that invocation is unnecessary. Section 5 gives the exact signature that should be frozen first; the exponent wrapper still needs the exact relation between ambient `b` and actual expected mass.

### I. Internal shuffle-graph edge estimate

Source: start of the edge-density proof, TeX 1517–1525; 2510 Lemma 4.14; 2103 Lemma 4.12 is the independent-row analogue.

For every prefix `x` of length `M<=K` and every integer `q` with `P(Y_x=q)>0`,

`E[card Edges_x | Y_x=q] <= choose(q,2)*R_tail(M) <= q^2*Q_tail(M)`.

The source asks only for the weaker final expression. The stronger collision-pair expression is a direct finite consequence, not an additional hypothesis. It applies to legal and zero-mass prefixes alike; legal status is only needed to take logarithms. In particular `q=0,1`, `M=K`, zero pile counts, and pile counts `1` are explicit cases, not excluded cases.

The same inequality holds conditioning on every positive-probability prefix-history fiber, replacing `q` by the determined occupancy. Future columns remain independent of that history. It does **not** assert the same expectation inequality after conditioning on arbitrary internal information, which already fixes the internal graph.

## 4. A finite obstruction to freezing the endpoint statements

Take any integer `a>=2`, `N=2a+1`, `k=3`, and `K>=2`. Let first-column counts be `(a,1,a)` and choose `0<chi<=a/N`, `chi<1/3`. Later columns can all be chi-good; they play no role in the computation below. The empty word is ambient, so `r=0,b=1`. Let `x=y=z=(1)`.

* The left large-pile boundary is `0`, and the right is `2`.
* Both boundary prefixes stop at their first genuine crossing. They are admissible (there are no exceptional boundary digits before the crossing), nonterminal, compatible, and retained.
* The left and right side-piece occupancies are both exactly `a` in every matrix.
* Therefore `c_L(x)=0` and `c_F(x;y,z)=(log_N a)/2`.
* Every continuation has expected size at most `1`; hence the stated fluctuation-regular comparison holds, even without an error.
* For every `delta>0`, the root stability inequality holds, so `Stable(y,z)={x}`.
* In every matrix, `I_x` is the single zero-based position `a`. Thus source endpoints are deterministically `iota_x=a+1` and `tau_x=a+2`.

For any event `S_x` and any positive-probability internal-information fiber,

`P(iota_x=a+1 and S_x | UInfo_x) = P(S_x | UInfo_x)`

and the analogous identity holds for the right endpoint. Integrating the claimed atom bound would force `2*P(S_x)` to tend to zero whenever its intended exponent tends to a negative constant. But the claimed good-event bound makes `P(S_x)` tend to one, while `c_F -> 1/2`. No uniform `O(delta)` error with a constant independent of delta repairs this.

In the article's case `a=b=first column`, the selected population has size `N-n(first,1)=2a` and `d_2=2a`. Thus the factor `1-d_2/(N-n(first,1))` in the alleged positive variance lower bound is exactly **zero**. This directly contradicts the ambient transfer conclusion about complementary fractions.

The mechanism is visible in the source comparison: 2510 Definition 4.3 and Lemmas 4.4–4.5 begin fluctuating side pieces at index **2**, keep the first column's contribution deterministic, and use a first chi-good shuffle. The new definition begins at `M_w+1` and treats a deterministic first-column total as a variance scale. Changing the new definition to start later would be a mathematical repair; it is not permitted as a silent implementation detail.

The finite example also shows that adding only the missing side-order case splits cannot repair the atom theorem. There is genuinely no random shift available for this stable block.

## 5. Exact finite statements available for freeze

These statements use only the finite definitions in section 2. All can be stated without a profile, an asymptotic error, good columns, concentration, or any extra statistical hypothesis.

### F1. Deterministic first-column interval

For every `N>=2`, `k>=2`, `K>=1`, every count array with column sums `N`, every digit `d<k`, and every matrix `S in Omega`, if `x=(d)`, then

`Y_x(S)=n(0,d)`,

`L_x(S)=sum_{l<d} n(0,l)`,

`U_x(S)=sum_{l<=d} n(0,l)`.

Consequently `I_x(S)` equals that deterministic half-open integer interval. This includes `n(0,d)=0` and either extreme digit.

### F2. Deterministic conditional endpoint atoms

For the same data, for **any** finite statistic `Z : Omega -> ZSpace`, any event `A subset Omega`, and every `z` with `P(Z=z)>0`, writing `l=sum_{l'<d}n(0,l')` and `u=sum_{l'<=d}n(0,l')`,

`P(L_x=l and A | Z=z)=P(A | Z=z)`,

`P(U_x=u and A | Z=z)=P(A | Z=z)`.

All other endpoint point masses intersected with `A` are zero. Thus each maximum endpoint atom equals `P(A|Z=z)`. Instantiating `Z=UInfo_x` proves the obstruction without assuming any property of the information.

### F3. Occupancy first moment

For every `N>=2`, `k>=2`, `K>=0`, every count array, and every prefix `x` of length `M<=K`,

`E Y_x = N * product_{j<M} n(j,x[j])/N`.

Also every row has the displayed prefix probability. If a selected pile is zero then both sides are zero; the empty product for `M=0` is one.

### F4. Adjacent edges versus collision pairs

For every matrix and prefix,

`card Edges_x <= Pairs_x` and `card Edges_x <= Y_x`.

One exact proof partitions the internal sorted word list into runs of equal full words. A run of length `h` contributes `h-1` when `h>0`, while it contributes `choose(h,2)` collision pairs and `h` rows. Cases `h=0,1,2` and larger `h` must be handled under natural subtraction. An alternative injection sends an adjacent equal-word pair in the sorted list to its two original labelled row indices, taken in increasing order; the sorting permutation is a bijection, so this injection is distinct across internal edges.

### F5. Two labelled rows, future collision probability

For every `0<=a<b<N`, every prefix length `M<=K`, and every positive-probability prefix-history fiber `h`,

`P(for every j>=M, S(a,j)=S(b,j) | F_M=h) = R_tail(M)`.

At one column, the probability that both distinct rows have digit `l` is `n(j,l)(n(j,l)-1)/(N(N-1))`. Sum over digits, then multiply over independent future columns. The tail-empty case has probability one. Piles of size zero or one contribute zero to that digit's two-row term.

### F6. Conditional collision count and internal edge estimate

For every prefix `x` and every positive-probability prefix-history fiber `h`, with determined occupancy `q=Y_x(h)`,

`E[Pairs_x | F_M=h] = choose(q,2)*R_tail(M)`,

`E[card Edges_x | F_M=h] <= choose(q,2)*R_tail(M)`.

Average over prefix-history fibers with occupancy `q` to obtain the same inequality conditional only on `Y_x=q` for every `q` with positive probability. There is no conditioning on future rows in this statement.

### F7. Without-replacement versus product collision factor

For each column, `0<=r_j<=q_j<=1`, hence

`0<=R_tail(M)<=Q_tail(M)<=1`.

Combining with F6 gives the exact source inequality

`E[card Edges_x | Y_x=q] <= q^2*Q_tail(M)`.

For legal `x` and `N>1`, the source tail exponent is defined by the same finite sum, so `Q_tail(M)=N^(c_E(x))` is an exact log/product identity; an `o(1)` loss is unnecessary at this step.

### F8. Squared edge probabilities and occupancy

For every prefix,

`D_x <= sum_q P(q in Edges_x) = E(card Edges_x) <= E Y_x = N*lambda_x`.

The first inequality uses only `0<=P(event)<=1`, including the probabilities zero and one. The equality is finite indicator summation.

### F9. Terminal singleton

For every full word `x` of length `K` and every matrix,

`card Edges_x = Y_x - 1` using natural subtraction.

Therefore `D_x <= N*lambda_x`, and `Q_tail(K)=1`, `c_E(x)=0`. If a terminal retained pair has join `x`, the stopping definition gives `Stable={x}` and hence this is its contribution. The graph-level assertion is valid even without any boundary pair.

### Necessary helper list for F1–F9

1. Finite count-array realizability and uniform column law.
2. Finite product-law marginal and independence identities.
3. Uniform column one-row symbol probability.
4. Uniform column two-distinct-row joint symbol probability, including counts below two.
5. Prefix membership decidability and the finite product row-prefix event.
6. Sorted-list permutation and lexicographic prefix contiguity.
7. Occupancy/endpoint identities and internal interval translation.
8. Counting labelled unordered pairs of a finite row subset.
9. Pointwise edge-to-pair injection or equal-word run decomposition.
10. Finite conditional expectation on a positive-probability fiber, finite linearity, and iterated averaging over a coarser statistic.
11. Probability nonnegativity, at most one, indicator expectation, and finite sums.
12. Natural-subtraction cases, `choose(q,2)<=q^2`, and the finite collision-factor inequalities.
13. Empty-prefix/empty-tail products and log/product identities for positive factors.

These are real proof obligations. They are not imported project facts or asserted mathlib names. A compiler and mathlib inventory must be checked before assigning specific Lean implementations.

## 6. Alternate decompositions that preserve the source data

### Exact localization bookkeeping

For any finite family `A` of prefix blocks and any `tau>0`, define `R={x in A : P(m in I_x)>=tau}`. Then

`P(m in union_{x in A} I_x and m not in union_{x in R} I_x) <= card(A)*tau`.

Consequently

`P(m not in union_{x in R} I_x) <= P(m not in union_{x in A} I_x) + card(A)*tau`.

This follows from a finite union bound and preserves exactly the prescribed relevance threshold. It exposes the ambient/truncation coverage term. Deriving a small bound for that term is an upstream task; omitting it would change the statement. Equal-full-word adjacency supplies the exact edge-containment implication from A.3.

### Exact conditional translation identity

On a positive-probability fiber `UInfo_x=u`, let `T(u)` be the fixed set of internal edge offsets. For every position `m` and event `A`,

`P(m in Edges_x and A | UInfo_x=u)`

`= sum_{r in T(u)} P(L_x+r=m and A | UInfo_x=u)`

`<= card(T(u)) * max_j P(L_x=j and A | UInfo_x=u)`.

The events in the sum are disjoint because a fixed `m` and distinct offsets require distinct shifts. This isolates the valid combinatorial step without assuming the false fluctuation estimate. It can be proved even in the first-column deterministic case.

### Terminal and internal graph estimates

F3–F9 directly preserve the source hypotheses and definitions and avoid the problematic concentration route. They provide genuine components of the assigned task. They do not imply the three nonterminal density exponents by themselves.

### What would constitute a change requiring an explicit new contract

* Starting fluctuations after the first ambient column, as in the old fixed-column proof, changes `c_F` and potentially the stable partition.
* Conditioning on a first ambient column and restarting the process changes the ambient conditioning law and requires proving inherited tail hypotheses.
* Adding a lower bound on a residual hypergeometric variance or on both complementary fractions adds an assumption unless those quantities are proved from the existing hypotheses.
* Declaring an arbitrary endpoint-atom bound as a field of a Lean context adds an unproved analytic input.
* Replacing `b` by the exact finite exponent `log_N E Y_w`, or imposing an `O(1/log N)` approximation to it, changes the source's ambient data unless adopted explicitly before freeze.
* Replacing the localization conclusion by a retained-event statement or adding its polynomial truncation error is a corrected statement, not a proof of the original displayed conclusion.

The preserved-data decompositions above support finite progress. They cannot justify freezing all requested analytic estimates unchanged.

## 7. Recommended freeze outcome

Freeze the finite definitions in section 2 and F1–F9 only after comparison with the independent reconstruction and hidden-case reports. Also freeze the exact edge-containment, relevance-union, and conditional-translation identities if they are included in the implementation plan. Preserve the original analytic target signatures in section 3 as **unresolved source targets**, not declarations with unproved bodies.

Before any analytic target is frozen, resolve the deterministic first-column obstruction, the ambient law/normalization ambiguity, the missing coverage loss, and the quantitative two-parent separation estimate. A change to any of those definitions or assumptions must remain visible as a new mathematical contract. No combination of `sorry`, a new axiom, an assumed endpoint estimate, or a silently stronger good-event context can meet the requested formalization contract.
