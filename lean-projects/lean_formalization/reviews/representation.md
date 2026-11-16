# Independent Lean representation and contract review

This report independently reads the three authorized sources. It is a proposed
pre-freeze design, not a claim that any Lean theorem is implemented. No `.lean`
file or executable Lean snippet was written for this review. Source references
are the unified TeX definition/lemma labels, 2510.22783v1 §§2.1, 2.4, 4.1–4.3,
and 2103.05068v3 §§4.1.2–4.1.3, 4.4.

## Findings that affect a faithful freeze

1. The unified TeX defines `c_L` twice. The earlier upper-margin section sums
   from `floor(r log N)`; Definition `ambient-block-size-exponent` sums from
   `M_w`. An `o(log N)` difference in the endpoints need not have `o(log N)`
   cost: a legal individual digit can cost `log N`. Freeze the detailed
   `M_w` definition. Do not assert that these two source definitions agree.
2. The new coarse profile stores exceptional *locations*, whereas old
   Definition 4.7 stores exceptional `(location, digit)` pairs. Therefore
   `Q_x` (the exceptional cost) and `c_L(x)` are not determined by the new
   profile. Keep the literal coarse profile. A separately defined labelled
   refinement maps onto coarse profiles and yields an extra `k^|Q|` factor
   when counting words in a coarse class. Never silently substitute the old
   profile definition.
3. `c_F` has value negative infinity if a side fluctuation vanishes. A global
   real-valued definition using `Real.log 0` is not faithful. Use an
   extended-real definition, or define its real-valued restriction only on
   pairs for which both side maxima are proved positive. Terminal pairs
   must remain available even when this positivity fails.
4. A family of probability measures indexed by time does not itself provide
   measurability of the time functions integrated in `A` and `B`. Full
   integral replacement needs a measurable kernel or equivalent time
   measurability/integrability. This is not explicitly supplied in the
   authorized source. Finite empirical comparison results below avoid the
   issue; their integral corollaries remain unfrozen pending a decision.
5. Exact finite approximation errors must expose the number `d` of simplex
   cells. Old Lemma 4.8 explicitly produces `O(phi z)`. A new displayed
   `O(rho + phi)` may have constants depending on the already fixed `chi`,
   hence on `d(chi)`, but it is not an absolute bound uniform in `chi`.
6. The exceptional-profile mass display in the new bad-profile proof is a
   probability-mass bound. Expected row count needs the factor `N` (or the
   ambient expected row count). This factor does not spoil the target
   conclusion, because its negative exponent tends to infinity as `chi`
   tends to zero. Keep that factor in every finite statement.
7. The entropy claim with `theta` uniform on `[3,4]` must explicitly use a
   bound for the one-column cost, for example `psi_p(theta) <= 3 log k`.
8. The source's real `r` is an asymptotic ambient birth time, while the exact
   birth time is `M_w / log N`. It need not satisfy `r <= t_v` for every
   finite `N`. Keep finite estimates based on exact times; the passage to
   asymptotic `r` incurs a bounded-observable endpoint error. This is harmless
   for `a` and `psi`, but not for arbitrary selected digit costs.

## Data representations

Use natural counts and finite sets as the primary data. Normalize only when
forming the numerical exponents.

- `Alphabet` is `Fin k`, with `2 <= k`. Columns are `Fin K`; the corresponding
  paper time is `j + 1`. This convention must be fixed globally so every tail
  and prefix interval has the same endpoint convention.
- `Cuts` contains natural pile counts `n(j,l)` and the equations
  `sum_l n(j,l) = N`. Set `p(j,l) = n(j,l) / N` in the reals. An alternative
  finite helper layer takes arbitrary nonnegative probability vectors;
  the integer-cut specialization is then proved, not assumed.
- A prefix consists of a natural length `M <= K` and a map `Fin M -> Fin k`.
  Legality is positivity of every selected pile count. Prefix extension is
  agreement after transporting indices along the length inequality. A full
  word is a map `Fin K -> Fin k`.
- Define deterministic `prefixMass(x) = N * product_{j < M_x} p(j,x_j)`.
  This is not by definition the expectation of a random interval. The
  separate previously needed shuffle lemma identifies it with that
  expectation. Product-law word weights are sufficient for all finite
  truncation/counting estimates.
- Set `L = log N`, working with `N >= 2`; equivalently general finite helpers
  use an arbitrary positive real scale `L`. Since the final limit is
  `N -> infinity`, this finite restriction does not change an asymptotic
  theorem. It must nevertheless appear in its finite contract.
- For an ambient prefix `w` and real `b`, set
  `cL(w,b,x) = b - sum_{M_w <= j < M_x} log(1 / p(j,x_j)) / L`.
  Define `ambientError = log(prefixMass(w)) / L - b`. The finite relation
  `log(prefixMass(x))/L = cL(w,b,x) + ambientError` is exact. No separate
  error hypothesis is needed to define or prove it.
- A regular simplex partition has a finite cell type, a unique cell map,
  a representative vector for each cell, and the source's four regularity
  properties with an explicit constant `Creg`. The Borel sets and measures
  are needed only in the later analytic layer. Do not turn existence of a
  partition into an axiom: either take a given source-admissible partition
  as data, or separately prove its construction.
- The space-time cell map is the pair of a time-cell index and simplex-cell
  index. Time cells are disjoint with the final endpoint included, as in the
  source. No continuity in time is required for finite profile counts.
- The profile stores raw counts `n(q,i,l)` as naturals and an exceptional
  finite set `Q`. Its normalized counts are `n(q,i,l)/L`. It does **not**
  store exceptional digits. A labelled refinement additionally stores a
  function `Q -> Fin k`.
- Compute `S` using good positions, or histogram bins with positive count.
  This avoids writing the source's potentially undefined expression
  `0 * log(1 / 0)` for zero representative coordinates. A regrouping theorem
  proves the two valid formulas equal.
- Compute entropy as a finite sum over positive-count bins. Equivalently,
  use `C log C - sum_l c_l log c_l` with the mathematical convention
  `0 log 0 = 0`; prove equivalence before switching formulas.
- `psi(p,theta) = -log(sum_l p_l^theta)` uses real powers, not natural
  powers. All logarithm/rpow identities require positive arguments. The
  range `[2,4]` guarantees positive exponents; nonempty support follows from
  the simplex equations even when some coordinates are zero.

## Proposed finite theorem contracts

Each numbered item is an independently reviewable contract. Splitting one
item into several implementation lemmas requires preserving the hypotheses
and proving the intermediate claims. These are candidate contracts for
comparison with the other two reports, not an already frozen API.

### F01. Probability-vector and legality consequences

For a nonnegative finite probability vector, every coordinate is at most
one, at least one is positive, and its maximum lies in `[1/k,1]`. For legal
prefixes, `prefixMass > 0`; for every prefix, `0 <= prefixMass <= N`.

Dependencies: finite sums/products and the simplex equations only. No
shuffle randomness or approximation hypotheses.

### F02. Finite product marginalization

For coordinatewise probability vectors, summing the full-word product weight
over all extensions of a prefix gives the prefix product. More generally,
requiring a set of positions `A` to lie in coordinatewise sets `E_j` gives
total weight `product_{j in A} sum_{l in E_j} p(j,l)`.

This is the independent-column fact needed for tail bounds. It is a theorem
about the product of the one-row marginal laws and does not assert that
different rows of a fixed-column shuffle are independent.

### F03. Exact logarithmic prefix identities

For legal `w <= v <= x` and `L = log N > 0`,

`cL(w,b,x) = cL(w,b,v) - sum_{M_v <= j < M_x} cost(j,x_j) / L`,

`log(prefixMass(x))/L = cL(w,b,x) + ambientError`,

and `cL(w,b,x) <= cL(w,b,v)`.

Every cost is nonnegative. The empty extension has zero cost. The parameter
`b` is arbitrary real data, and no asymptotic ambient hypothesis is used.

### F04. Regular representatives and good/exceptional digits

For a supplied regular cell, `0 < chi < 1/k`, and its member `p`,

- if its representative coordinate exceeds `2 chi`, the actual coordinate
  exceeds `chi` and the log-cost difference has absolute value at most
  `Creg chi`;
- otherwise the actual coordinate is at most `3 chi`;
- the maximum-coordinate log cost and every `psi(.,theta)` for
  `theta in [2,4]` differ from their representative values by at most
  `Creg chi`.

These are direct eliminations of the source's regular-partition structure.
There is no `o(1)` in the exceptional-coordinate inequality.

### F05. Profile count partition and cost regrouping

For positions `J = {M_v,...,M_x-1}`, let `G` and `Q` be the good and
exceptional positions. Then they form a disjoint partition of `J`;
`sum_{q,i,l} n(q,i,l) = |G|`; and

`sum_{j in G} representativeCost(j,x_j) / L = S`.

For each cell, total count equals the number of its good positions. Positive
histogram counts imply that the representative coordinate is positive.
Also `M_x - M_v = sum counts + |Q|`, so the endpoint is determined by the
coarse profile and the boundary prefix.

### F06. Representative-replacement error and `c_L` decomposition

Define the signed residual

`E = sum_{j in G} (actualCost(j,x_j)-representativeCost(j,x_j)) / L`.

Then exactly

`cL(w,b,x) = cL(w,b,v) - S - Qcost - E`,

`|E| <= Creg chi |G| / L`, and `Qcost >= 0`.

If `K <= T L`, the last error is at most `T Creg chi`. No `Delta`, `rho`,
`phi`, integral, or stable stopping condition is needed.

### F07. Maximal-pile domination

For legal `w <= v`,

`cL(w,b,v) <= b - sum_{M_w <= j < M_v} a(p_j) / L`.

Also `0 <= a(p) <= log k`. For `theta in [2,4]`,
`0 <= psi(p,theta) <= (theta-1) log k <= 3 log k`.

The first statement is finite pointwise log monotonicity; the bounds for
`psi` use the simplex equations and the convexity/power-mean inequality.
They must be proved or imported as trusted mathlib theorems, not bundled
as new properties assumed of the shuffle.

### F08. Side-piece marginalization, positivity, and fluctuation comparison

Define the deterministic left side mass at `M_w <= i < M_x` by

`leftMass(x,i) = N * product_{j<i} p(j,x_j) * sum_{l<x_i} p(i,l)`.

The right side is analogous. F02 identifies these with the product-weight
mass of the source's `P` and `Q` pieces, which leave all later digits free.
Therefore these masses, and their maxima through `M_v-1`, depend only on
the boundary prefix `v`, not on its continuation.

At a genuine left boundary crossing the left coordinate sum is at least
`chi`; hence `leftMass(x,i) >= chi prefixMass(x)`. The analogous right
claim holds. For a nonterminal boundary pair both genuine crossings exist,
so both maxima are positive. If `F` is their minimum after square root and
`cF = log F / L`, then exactly

`cF >= (cL(w,b,x)+ambientError)/2 + log chi/(2L)`.

The paper's `o(1)` statement follows only after separately using
`ambientError -> 0` and fixed `chi`. This proof establishes regularity;
it must not assume the definition of fluctuation-regularity as its premise.

### F09. The last good digit and the parent-crossing bound

If `v <= parent(x)` and `x` adds a single digit, then

`0 <= S(x)-S(parent(x)) <= log(1/(2 chi))/L`,

and the difference is zero when the last digit is exceptional. If the
source's parent-crossing condition
`cL(parent(x))-cF >= delta` holds, F06 gives

`S(x) <= cL(v)-cF-delta + Creg chi K/L + log(1/(2chi))/L`.

The first-crossing stable case supplies `v <= parent(x)`; it is not valid
to apply this formula automatically to singleton stable blocks.

### F10. Finite entropy/KL inequality with zero coordinates

Let `c_l >= 0`, `C = sum c_l`, `w_l >= 0`, `W = sum w_l > 0`, and require
only `c_l > 0 -> w_l > 0`. With zero-count summands omitted,

`sum_l c_l log(C/c_l) <= sum_l c_l log(W/w_l)`.

When `C=0`, both sides are zero. When `C>0`, normalize `c/C` and `w/W`
and apply finite KL nonnegativity. A proof using `log t <= t-1` needs only
the positive support of `c`; the omitted `w` support contributes a
nonpositive remainder. There is no full-support assumption on `w`.

### F11. Profile entropy inequality

Apply F10 in each cell with `w_l = representative_l^theta`, where
`theta in [3,4]`. Good-digit support proves the needed positivity. Then

`H <= theta S - sum_{q,i} cTotal(q,i) psi(rep_i,theta)`.

This exact finite inequality uses the whole simplex support in the
normalizing sum; it incurs no small-coordinate replacement error.

### F12. Generic finite cell replacement

Let `J` be a finite position set, `cell : J -> I`, actual values `f_j`,
representatives `r_i`, and target cell weights `m_i`. Write
`n_i = |{j : cell j=i}|`. If `L>0`, `|f_j-r_(cell j)| <= e`, and
`|n_i/L-m_i| <= d_i`, then

`|sum_j f_j/L - sum_i m_i r_i| <= e |J|/L + sum_i d_i |r_i|`.

The common bound `d_i <= D`, `|r_i| <= B` yields
`e |J|/L + |I| B D`. An additional target `F` with a separately proved
bound `|F-sum_i m_i r_i| <= eTarget` gives the same error plus `eTarget`.
The last bound is not assumed to be an integral theorem.

### F13. Finite blocking discrepancy

For full blocks indexed by a finite set `A`, take nonnegative lengths
`ell_i` with `sum ell_i <= T`; actual counts `n_i`; and target masses `m_i`.
Suppose `|n_i/L-m_i| <= phi ell_i + 2/L`. Add boundary count `nBoundary`
and boundary target mass `mBoundary` satisfying

`nBoundary/L <= 2 rho + 2/L`, `0 <= mBoundary <= 2 rho`.

Then

`|(sum n_i+nBoundary)/L - (sum m_i+mBoundary)|`
`<= phi T + 4rho + (2|A|+2)/L`.

This is a finite triangle-inequality theorem. If the original almost-like
data use closed grid blocks, deleting their left endpoints changes each
column count by at most one and hence turns `1/L` into `2/L`. Finite
additive cell masses may be supplied as nonnegative weights on the common
refinement of grid endpoints and the two target interval endpoints, with
the sum of cell weights in each atom equal to the atom length. Additivity
then follows from finite sums; it is not a new analytic axiom.

### F14. Lattice endpoint and boundary-count estimates

For `L>0` and `a<=b`, the number of natural column times `j/L` in `(a,b]`
is at most `(b-a)L+1`. Intersecting with `1 <= j <= K` only decreases it.
An individual endpoint contains at most one column. For the two leftover
pieces of a uniform `rho` mesh, total length is at most `2rho`, so their
normalized count is at most `2rho+2/L`. The number of full grid blocks is
at most `ceil(T/rho)`.

Combining F13/F14 gives the safe interval discrepancy
`4rho + phi T + (2ceil(T/rho)+2)/L` for half-open target intervals.
Allowing up to two extra endpoints gives the common safe remainder
`4rho + phi T + (2ceil(T/rho)+4)/L`.

### F15. Finite `c_E` and maximal-pile representative estimates

Use F12 for the tail positions after `x`, with `f_j=psi(p_j,2)` and
`r_i=psi(rep_i,2)`. Since `cE=-sum f_j/L`, the finite approximation to
`-sum_i m_i psi(rep_i,2)` has error

`Creg chi |tail|/L + sum_i d_i |psi(rep_i,2)|`.

Use F12 with `a(p_j)` between `w` and `v`, then F07, for the maximal-pile
upper bound. These remain meaningful for arbitrary finite target cell
weights. Identifying the target weighted sums with `B_2` or `A` is the
separate analytic replacement problem noted above.

### F16. Removing exceptional counts from the entropy cost

Let `allCount(q,i)` be the total normalized number of positions in a cell,
and `excCount(q,i)` the exceptional normalized number. Then exactly
`cTotal = allCount-excCount` and `sum excCount = R`.
If `0 <= psi(rep_i,theta) <= B`,

`sum cTotal psi(rep_i,theta) >= sum allCount psi(rep_i,theta) - B R`.

Combine F11, F12, and `R <= alpha` to obtain the finite entropy estimate
with error at most the cell replacement error plus `B alpha`.

### F17. Sparse subset and sparse labelled-assignment count

For `K,k,h` natural, define

`Sparse(K,k,h) = sum_{q=0}^{min(h,K)} choose(K,q) k^q`.

This is exactly the number of partial `k`-valued assignments on `K`
positions with domain size at most `h`. The corresponding subset count
is `Sparse(K,1,h)`. For `0<z<=1`,

`Sparse(K,k,h) <= z^(-h) (1+kz)^K`.

The proof multiplies each summand by `z^q >= z^h` and uses the binomial
theorem. It works also for `h>K` and `h=0`.

### F18. Product-weight small-digit tail

For each position let `E_j` be a digit set with
`b_j=sum_{l in E_j} p(j,l) <= beta`. For natural `q0` and real `z>=1`,

`weight{word : #bad positions >= q0}`
`<= z^(-q0) product_j (1+(z-1)b_j)`
`<= z^(-q0) (1+(z-1)beta)^K`.

Alternatively, finite subset counting gives
`weight{#bad >= q0} <= choose(K,q0) beta^q0` for `q0<=K`, and zero for
`q0>K`. The tail-sum bound from the source follows as a weaker result.

For small individual pile masses `tau`, use `beta=k tau` (there is no
requirement that this upper bound itself be at most one). Multiply the
word-weight bound by `N`, or by `prefixMass(w)` when conditioning on the
ambient prefix, to bound expected row mass.

### F19. The elementary discarded-edge reduction

For finitely many edge probabilities `0<=p_e<=1`,
`sum_e p_e^2 <= sum_e p_e`. If a random edge family has at most as many
edges as rows in the corresponding word family, finite expectation and
sum interchange give `sum_e p_e <= expectedRowCount`.

The equality between the squared-probability sum and expected common-edge
count for independent copies is a separate standard independence lemma.
No independence of rows inside a shuffle is used.

### F20. Boundary encoding and admissibility truncation

An admissible left boundary prefix can be encoded by:

- its length, at most `K+1` choices;
- an optional crossing digit, at most `k+1` choices;
- its at most `hBoundary` strict-left deviations, a partial labelled
  assignment counted by `Sparse(K,k,hBoundary)`.

Every nondeviation before the crossing is the prescribed boundary digit,
so this encoding is injective. The right version is identical. Thus each
boundary family has cardinality at most
`(K+1)(k+1) Sparse(K,k,hBoundary)`.

If the selected left boundary violates the threshold, the full word has
more than `hBoundary` positions in a pile of mass less than `chi`.
Consequently F18, with `tau=chi`, bounds the weight of *the union* of
discarded cylinders. The same holds on the right. There is no additional
factor for the number of prefixes or boundary pairs.

### F21. Exceptional-profile truncation

If the stable prefix's post-boundary exceptional count exceeds `hExc`, the
full word has more than `hExc` exceptional positions over all columns.
Each actual exceptional pile mass is at most `3chi` by F04. Hence F18
with `tau=3chi` bounds the union's weight; F19 turns `N` times this weight
into the required discarded-edge bound. This argument does not require
profiles with differing exceptional costs to share one value of `c_L`.

### F22. Number of retained coarse profile classes

Let `D=R d k` be the number of histogram coordinates and
`B=(K+1)(k+1) Sparse(K,k,hBoundary)`. Each coordinate is between zero and
`K`, so the number of boundary-pair/coarse-profile classes is at most

`B^2 (K+1)^D Sparse(K,1,hExc)`.

For the labelled refinement the last factor is
`Sparse(K,k,hExc)`. Taking the image under the forgetting map bounds the
coarse classes as well. Neither count claims that `c_L` is constant within
a coarse class.

### F23. Size of a fixed coarse profile class

For a fixed compatible boundary pair and coarse profile, the number of
prefix words is at most

`k^|Q| product_{q,i} multinomial({n(q,i,l)}_l)`.

For the labelled refinement the `k^|Q|` factor is absent. A separate finite
multinomial entropy inequality gives

`multinomial(n) <= exp(sum_{l:n_l>0} n_l log(nTotal/n_l))`.

Its proof uses the multinomial theorem at the probability vector
`n_l/nTotal`; the `nTotal=0` case is one. Therefore the coarse class has
size at most `exp(L H + |Q| log k)`, or equivalently
`N^(H+R log k)` when `L=log N`. This extra term tends to zero after the
exceptional truncation, but must remain explicit in the finite contract.

## Quantifier order and asymptotic consequences

Fix `k`, a nonnegative finite `T`, and the desired tail exponent `C0` or
class-count exponent `epsilon>0`. Choose the boundary constant sufficiently
large depending on `C0`. Choose `chi` small, and only then fix its finite
regular partition and the finite time partition. Choose the other mesh
parameters afterwards. Only then choose the lower cutoff `N0`. Uniformity
is over all cuts, legal prefixes, boundary pairs, and profile classes with
these fixed parameters.

For explicit tail asymptotics, write `ell=log(1/chi)` and choose in F18
`z=1/(chi sqrt(ell))`, for sufficiently large `ell` so `z>=1`.

- For boundary threshold `Cboundary L/ell`, the logarithmic probability
  upper bound divided by `L` is at most
  `-Cboundary + Cboundary log(ell)/(2ell)`
  `+ T log(1+k/sqrt(ell))`.
  Multiplying by `N` adds one to this exponent. The error tends to zero.
- For exceptional threshold `L/sqrt(ell)`, using `tau=3chi`, the exponent
  for expected row count is at most
  `1-sqrt(ell)+log(ell)/(2sqrt(ell))`
  `+T log(1+3k/sqrt(ell))`, which tends to negative infinity.
- For class counting, F17 with `z` tending to zero along with
  `hBoundary/L ~ Cboundary/ell` and `hExc/L ~ 1/sqrt(ell)` shows that
  each sparse-data factor has arbitrarily small exponent. For fixed
  partitions, the powers of `K+1` contribute exponent tending to zero
  as `N` tends to infinity.

Floors/ceilings are handled by choosing `q0=floor(threshold)+1` for strict
discard events and `h=floor(threshold)` for retained classes. This avoids
changing `>` to `>=` silently. Threshold integer errors have favorable
signs for the tail bound and do not affect the class-count limit.

## Necessary prior project interface; availability not asserted

The source restriction and initial repository inventory did not identify a
pre-existing Lean formalization of these objects. Mathlib tooling now
reported by the coordinator is not evidence that project lemmas exist.
The genuinely required prior interface for connecting this finite batch to
the full shuffle proof is:

1. Legal words/prefixes, extension, cylinder sets, lexicographic order, and
   the unique first boundary stopping prefixes.
2. The fixed-column shuffle probability space, its one-row product
   marginals, and expected cylinder-count/product-mass equality.
3. The shuffle graph, graph restriction to cylinder families, and the
   elementary edge-count/row-count inequality.
4. Stable-prefix stopping and the partition of each retained boundary
   cylinder, including terminal pairs.
5. For the analytic layer only: a measurable time profile, regular Borel
   cells, integration of their masses and bounded one-column costs, and
   almost-like grid cell estimates.
6. For the asymptotic layer: sequences of cut data indexed by `N`, ambient
   exponent convergence, and the explicit nested quantifiers above.

F01–F23 can supply several of these prerequisites rather than import them,
but none may be replaced by an unproved project declaration. The finite
batch requires only trusted finite sums/products, logs, powers, arithmetic,
binomial/multinomial identities, finite set cardinalities, and real
inequalities. It does not require `axiom`, `sorry`, `admit`, or extra
probabilistic assumptions.

## Review of coordinator's `FINITE_CONTRACT_CANDIDATE.md` (F01–F20)

The numbering in this section is the coordinator's numbering, distinct from
the more expanded proposed decomposition above. I reviewed every candidate
definition and every F01–F20 statement against the independent reading.

### Definition review

- `cost=-log` is a sound real-valued primitive. Every identification with
  `log(1/p)` is restricted to positive `p`. It does not implement
  extended-real entropy or extended-real `c_F` at zero.
- `L>0`, actual legality `0<p<=1`, the strict good condition `2chi<q`, and
  exceptional set as its complement are correct. Selected representative
  masses may be treated as arbitrary real helper data; actual simplex
  representatives satisfy `0<=q<=1` as a derived/source data property.
  No candidate theorem currently needs an additional full-support condition.
- The regularity predicate exactly supplies the two digit cases used here.
  Its error `epsilon` is explicit; an instantiation supplies `Creg chi`.
- Actual/good/exceptional sums, normalization, and disjoint finite extension
  positions give exact identities. They avoid the competing `floor(r log N)`
  definition and require no integral assumption.
- Cell replacement with arbitrary target weights is a useful genuine finite
  lemma. The differences `delta_i` are explicitly premises of that finite
  lemma, not silently asserted from almost-likeness. Reusing the conclusion
  as an integral estimate still requires a separate bridge.
- Blocking is sound after the target remainder domination below is added.
- Nonnegative prefix multipliers and later factors in `[0,1]` give the
  intended finite side comparison. Positivity for logarithms belongs to F11.
- Entropy, restricted cross-entropy, full tilted normalization, the
  zero-count convention, and the positive-support condition are faithful.
- `lowCount`/`tailWeight` and strict thresholds represented by `floor+1` are
  correct. Cast the natural digit count `k` to the reals in inequalities.
- Sparse-pattern and histogram records are appropriate. Amend “crossing
  digit” to “last digit” as explained in F19, so terminal records are total.

### Statement-by-statement decision

| Candidate | Decision and precise qualification |
|---|---|
| F01 | Approve. Positivity of `q` in the last inequality follows from `0<p<=q`; no upper bound on `q` is needed for log monotonicity. |
| F02 | Approve. It is elimination of the frozen regularity predicate, retaining strictness for good mass. |
| F03 | Approve. The existence of a uniform absolute-error bound automatically forces a nonnegative bound when the set is nonempty. No hidden extra positivity premise is needed. |
| F04 | Approve. `Q>=0` follows from actual legality and positive `L`. |
| F05 | Approve. Disjointness and exactly the actual prefix/extension index sets are essential. |
| F06 | Approve. All errors and cell cardinality factors are explicit. This is not yet an integral theorem. |
| F07 | **Amend.** Explicitly require `0<=targetRemainder<=2rho`, or target mass bounded by the stated remainder length, as well as nonnegative empirical remainder mass. Otherwise a length bound alone says nothing about an arbitrary target mass and the conclusion is false. With this premise, the stated constant is valid. |
| F08 | Approve. This is an absolute-value negation identity followed by F06. |
| F09 | Approve. Maximal masses are positive because they dominate positive selected masses. The one-sided error follows from F06. |
| F10 | Approve with the global `chi>0` and prefix nonnegativity visibly in scope. It compares mass products only and does not prove the source side expectation formula. |
| F11 | Approve. It is exactly the finite log comparison for positive side masses; expressing `log(sqrt U)/L` as `log U/(2L)` is a proved identity. It does not define `c_F` for zero fluctuations. |
| F12 | Approve. The stronger conclusion retaining `-delta` is also true, but the displayed weaker bound already suffices and is the statement to freeze. There is no need to add assumptions `S_parent>=0`, `e>=0`, or `d>=0`. |
| F13 | Approve, spelling out “probability vector” as coordinate nonnegativity and sum one. Support-only positivity of `w` is sufficient. |
| F14 | Approve. It is valid for all `theta>0` under the displayed support and normalization conditions, including zero total `c`. Taking `[3,4]` later is an instantiation. |
| F15 | Approve. Freeze the exact removal identity `allCost-goodCost=exceptionalCost` and `0<=exceptionalCost<=M|E|/L`; then the stated combination is unambiguous. All integrals remain excluded. |
| F16 | Approve. `z>=1` implies positive denominator, including when `h>K`; the tail is then zero. |
| F17 | Approve. Natural `k` may be zero, and the empty pattern contributes the usual `0^0=1` binomial term. |
| F18 | Approve the product-weight and scalar inequalities, with coordinate nonnegativity, `a>=0`, and `z>=1` explicit. **Wording amendment:** multiplication by `N` gives an inequality for `N` times word weight. Calling that the actual shuffle expected row mass requires the separately excluded one-row marginal/expectation bridge; it is not a conclusion established by this finite batch alone. The edge-probability inequality is unconditional finite algebra. |
| F19 | **Amend descriptor definition, then approve the factor `k`.** Store the last digit at the stopping length, even for a terminal no-crossing prefix. Store deviations strictly before that last position. If the prefix has no new position beyond the fixed ambient prefix, use a fixed default digit, available since source `k>=2`. Then terminal versus crossing status is recoverable from the last digit and known boundary, and the claimed `k(K+1)` bound is valid without an optional flag. The source-boundary-to-descriptor map must be proved injective before claiming this counts source boundary prefixes. |
| F20 | Approve after making its finite-cardinality form explicit: the coarse fibre is the disjoint union over exceptional labelings of the labelled fibres, hence its cardinal is at most `k^|E|` times the maximum labelled-fibre cardinal (maximum of an empty family defined as zero). It need not inject into one particular labelled fibre. The simple one-position example with representative/actual probabilities `(1/10,2/10,7/10)` and `chi=1/10` has two exceptional words with the same counts and exceptional set and different costs. |

I approve the finite mathematical content subject to the explicitly marked
F07/F18/F19 wording/definition changes and the precision clarifications for
F15/F20. This is approval to freeze a **partial finite helper batch**. It is
not approval to claim that the full assigned source lemmas, the measurable
time-profile bridge, or the shuffle-model expectation identity are proved.
