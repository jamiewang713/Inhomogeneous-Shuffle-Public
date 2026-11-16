# Independent mathematical reconstruction

This report uses only `time_inhomogeneous_riffle_shuffle_unified_article.tex`,
`2103.05068v3.pdf`, and `2510.22783v1.pdf` as mathematical sources. The two PDFs
were read through the supplied derived text. Local mathlib files were inspected
only to assess formalization APIs. This report contains no Lean declarations.

## Assessment

The largest **full-word** obstruction is sound in the fixed-column,
time-inhomogeneous model. It needs no asymptotic profile hypothesis at its finite
core. The full cold-spot theorem should not be frozen from the current sketch:
several displayed intermediate arguments are false or incomplete. A finite
implementation should distinguish concrete combinatorial/probabilistic theorems
from elementary conditional test-composition interfaces.

The homogeneous proof does not establish the current inhomogeneous theorem merely
by replacing constants with integrals. Its rare-word regime uses a strictly
negative full-word mean exponent, while the proposed inhomogeneous witness allows
a small positive exponent. New occupancy work is therefore essential.

## Global proof structure and dependency map

1. Fixed-column random matrix, lexicographically sorted row strings, stable
   inverse-shuffle permutation, and shuffle graph.
2. Upper branch: regular time/profile cells; finite word costs and types;
   hypergeometric prefix control; endpoint anti-concentration; first moment of
   shared graph edges in ambient blocks; recursive margins on all tails;
   exponential moment and total-variation upper bound. Random-cut upper bounds
   follow by averaging deterministic bounds on a typical event.
3. Largest-word lower branch: select a maximal pile in every column; exact mean
   and pair moments of that full word; occupancy lower tail; stable sorting turns
   its copies into a contiguous increasing run; uniform increasing-run count;
   total-variation event test. This test can be shared by all random cut sequences
   if its run threshold is uniform.
4. Cold lower branch: scalar witness from the positive reduced margin; ambient
   maximal prefix; time/profile-cell tilted prefix type; deterministic relative
   cold intervals; bridge with two good columns; endpoint concentration relative
   to the ambient block; localization of full cold words; occupancy indicators
   and a second moment; cold edge count; ascent test; translate scan; TV test.
5. Random-cut cold branch: index the deterministic tests by typical environments;
   union them; retain mixture success; control the sum of their uniform false
   positives. Pointwise deterministic TV separation alone does not suffice.

The finite dependency chain proposed here is:

```
uniform column symmetry + independent columns
  -> one-row / two-row prescribed-word probabilities
  -> occupancy first / second factorial moments
  -> variance <= mean
  -> finite occupancy lower tail

Tuple.sort monotonicity + stable ties
  -> exact sorted fiber interval
  -> multiplicity forces contiguous increasing run

uniform permutation relative-order count
  -> fixed interval probability 1/m!
  -> run-test false positive <= (N-m+1)/m!

occupancy tail + run implication + false-positive bound
  -> finite deterministic largest-word TV lower bound
  -> weighted union-test lemma for random environments

time-cell digit counts -> exact representative product -> finite log cost

exact sorted fiber interval + localization predicate
  -> distinct repeated cold words supply distinct cold edges
  -> those equal-key edges are ascents of the stable sort
```

## Concrete finite probability model

Fix integers `N >= 2`, `K >= 0`, and `k >= 1`. For each time `t : Fin K`,
choose a deterministic base column `c_t : Fin N -> Fin k`. Define pile counts
by the fiber cardinalities

`n_t(a) = #{i : c_t(i) = a}`.

Thus nonnegative integral pile sizes and total size `N` are definitional, and no
separate consistency hypothesis is needed. Sample one independent uniform
permutation `pi_t` of `Fin N` per column, and put

`zeta(i,t) = c_t(pi_t(i))`.

This construction is uniform over fixed-count assignments because every
assignment has the same product of within-pile factorials as its number of
permutation preimages. It directly realizes the source's fixed-column model.

For any word `w : Fin K -> Fin k`, define

`p_t = n_t(w_t)/N`, `lambda_w = product_t p_t`,
`C_w = #{i : forall t, zeta(i,t)=w_t}`, and `mu_w = N lambda_w`.

All fractions and expectations below are real. The exact finite statements are:

* One-row probability: `P(zeta(i,.)=w) = lambda_w`.
* For distinct rows `i != j`, the joint probability is
  `product_t [n_t(w_t)(n_t(w_t)-1)/(N(N-1))]`, interpreting the numerator as
  the natural falling factorial before coercion.
* `E C_w = mu_w`.
* `E [C_w(C_w-1)] = N(N-1) product_t [n_t(w_t)(n_t(w_t)-1)/(N(N-1))]`.
* `Var(C_w) <= mu_w`, since each pair factor is at most `(n_t(w_t)/N)^2`.
* If `m : Nat` and `(m : Real) < mu_w`, then
  `P(C_w >= m) >= 1 - mu_w/(mu_w-m)^2`.

The symmetry/double-counting route avoids building a hypergeometric distribution:
all row inclusion expectations in one uniform column are equal, and their sum is
the deterministic pile size. The analogous ordered distinct-pair sum is the
deterministic falling factorial of the pile size. Independence of columns then
factors the prescribed-word probabilities. Mathlib has finite uniform PMFs and
finite subset counting, but no probability distribution named hypergeometric in
the inspected version.

## Proposed sorting, digit-profile, and cold combinatorial module

The following are proposed statements for freeze, not yet implemented.

For a linearly ordered key type `W`, `f : Fin N -> W`, define

* `sigma_f = Tuple.sort f`;
* `C_f(w) = #{i : f(i)=w}`;
* `L_f(w) = #{i : f(i)<w}`;
* `HasIncreasingRun(sigma,m)` means there is `a : Nat` with `a+m <= N`, and
  for every `i,j : Fin N`, if `a <= i.val`, `j.val < a+m`, and `i<j`, then
  `sigma(i)<sigma(j)`.

Statements:

1. **Sorted equal-key convexity.** If `i <= j <= l` and
   `f(sigma_f(i))=f(sigma_f(l))`, then `f(sigma_f(j))=f(sigma_f(i))`.
2. **Stable tie increase.** If `i<j` and the sorted keys at `i,j` agree, then
   `sigma_f(i)<sigma_f(j)`.
3. **Exact fiber interval.** `f(sigma_f(i))=w` iff
   `L_f(w) <= i.val < L_f(w)+C_f(w)`.
4. **Full-word run.** If `1 <= m <= C_f(w)`, then
   `HasIncreasingRun(sigma_f,m)`.
5. **Cell digit-count partition.** For finite time, cell, and digit types, with
   `cell(t)` and `w(t)`, put `n(c,d)=#{t:cell(t)=c and w(t)=d}`. Then
   `sum_d n(c,d)=#{t:cell(t)=c}` and `sum_c sum_d n(c,d)=#times`.
6. **Exact representative product.** For arbitrary real representatives `r(c,d)`,
   `product_t r(cell(t),w(t)) = product_c product_d r(c,d)^n(c,d)`.
7. **Legal-word log product.** If every selected `p_t(w_t)>0`, then
   `log(product_t p_t(w_t))=sum_t log(p_t(w_t))`. The support hypothesis is
   necessary only for this logarithmic version; the raw product permits zeros.
8. **Largest-word product dominance.** If every `p_t(d)>=0` and
   `p_t(d)<=p_t(star(t))` for every time and digit, then every word has mass at
   most `product_t p_t(star(t))`.
9. **Cold exponent identity.** With definitions
   `H=theta J-B`, `H2=2 J2-B2`, `h=beta-J+H`,
   `Gamma=2 beta-2 J-2 J2+H+H2`,
   `F=(theta+3)beta/2-B-2 B2`, prove without assumptions
   `2 Gamma-h-F=(theta-3)(J-beta/2)`.
10. **Localized collisions supply edges.** For a finite word set `S` and
    `Hsubset : Finset (Fin N)`, assume that every sorted occurrence of a key in
    `S` belongs to `Hsubset`. Then the number of `w in S` with `C_f(w)>=2` is at
    most the number of adjacent equal-key pairs whose endpoints belong to
    `Hsubset`. Use the first two positions in each exact fiber; distinct fibers
    give distinct edges. This is an explicit deterministic transfer lemma and
    does not assert or assume the probabilistic localization theorem.
11. **Equal-key edges are ascents.** Every adjacent equal-key pair is an ascent
    of `sigma_f`, by stable tie increase. Thus the localized equal-edge set is a
    subset of the corresponding ascent set.

Instantiating `W` with the lexicographically ordered full word type makes
`sigma_f` the concrete stable inverse shuffle; equal **prefixes** alone are
insufficient for the run theorem.

## Hypothesis tests and random environments

For finite probability laws `P,Q` and a test `A`,

`P(A)>=1-alpha` and `Q(A)<=beta` imply `TV(P,Q)>=1-alpha-beta`.

Combining the concrete fixed-column model with sorting and uniform permutation
counting gives the finite endpoint

`TV(P_shuffle,U_N) >= 1 - mu/(mu-m)^2 - (N-m+1)/m!`

under `N>=2`, `1<=m<=N`, and `m<mu`, for any selected full word of mean `mu`.
Selecting per-column maxima maximizes this mean.

For a finite environment index set `E`, weights `a_e>=0` summing to one, laws
`P_e`, a typical subset `T`, and tests `A_e`, let `P=sum_e a_e P_e`. If for
`e in T`, `P_e(A_e)>=1-alpha_e` and `Q(A_e)<=beta_e`, then the single test
`A=union_{e in T} A_e` gives

`TV(P,Q) >= sum_{e in T} a_e(1-alpha_e) - sum_{e in T} beta_e`.

Uniformity of success errors, a high-probability typical set, and a sufficiently
small summed false-positive bound are necessary to pass to asymptotic random-cut
statements. These cannot be replaced by averaging deterministic TV lower bounds.

## Mathematical defects and missing work in the cold branch

1. **False block bounded-difference lemma.** `lem:block-bd` fixes all other
   relevant blocks and allows changes only against a reservoir. If the reservoir
   is empty, fixing the other blocks determines the remaining block, so its
   hypothesis holds with every `L_j=0` for arbitrary nonconstant functions.
   The conclusion cannot follow. The claimed Doob coupling does not preserve all
   other relevant blocks when no reservoir values are available.
2. **Repair for ascent concentration.** Retain deterministic internal graph
   edges. Boundary comparisons depend on two adjacent entire graph components.
   Split boundary comparisons by parity of the graph-component index. Within
   each class the pairs of components are disjoint, so their relative-order
   patterns under a uniform permutation are independent. Hoeffding then yields
   the desired concentration with at most `|E(H)|` indicators. This requires a
   new proof of the disjoint-block relative-order independence, not the false
   block lemma.
3. **False displayed Bonferroni coefficient.** The assertion
   `P(X>=2) >= E(X)_2/2-E(X)_3/6` fails at deterministic `X=3`: its right side is
   `2`. A valid elementary lower bound is
   `1_{n>=2} >= (n)_2/2-(n)_3/3`, and the homogeneous paper uses a different
   explicitly bounded pair-event inclusion-exclusion. Every affected later
   estimate must be reproved with valid constants.
4. **Central-window truncation is unjustified as written.** The truncated
   factorial polynomial agrees with the indicator on `X+Y<=R`, but can be very
   large off that event. A small probability of `X+Y>R` does not bound its
   expectation there. One needs genuine Bonferroni remainder control, or a
   weighted factorial-moment tail estimate. Also the displayed hypothesis
   `epsilon_N N^(2L*)=o(N^(-4a0))` alone does not absorb the extra
   `(1+mu)(1+nu)=O(log(N)^2)` factor in the given coefficient estimate.
5. **Fixed-mesh representative error.** The regular partition only guarantees
   logarithms differ by `O(chi)` per selected column. At fixed `chi` this is an
   `O(chi)` exponent error, not `o(1)` as `N` tends to infinity. The lower type
   statements need explicit error parameters, or a justified diagonal scheme.
6. **Clipped components in ascent expectation.** A clipped intersection can
   contain arbitrarily many internal ascents, so discarding its entire
   contribution is not `O(|boundary H|)`. Repair by retaining all internal
   edges and discarding only component-boundary comparisons adjacent to clipped
   components; there are `O(|boundary H|)` such comparisons.
7. **Small endpoint issues.** The right relative endpoint decomposition needs
   either left pieces plus the prefix count, or ambient count minus right
   pieces; its displayed explanation omits that ambient fluctuation. Reserving
   a terminal bridge must preserve `s<=u`, which needs an explicit bound on the
   witness's available interval length. Strict interval conventions also need
   attention at integer endpoints.
8. **Genuinely new inhomogeneous work.** The witness selection and balancing,
   ambient relative translation, finite costs on ordered time cells, bridge
   losses, and occupancy for means up to a positive power of `N` are all new.
   The homogeneous rare-mean estimates do not establish these statements.

These issues do not invalidate the finite largest-word obstruction. They do
prevent advertising a formal proof of the complete cold or matching-cutoff
theorem until their corrected statements and proofs receive separate reviews.
