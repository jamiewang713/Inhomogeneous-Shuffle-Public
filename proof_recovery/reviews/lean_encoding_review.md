# Independent Lean encoding review

## Scope and status

I read only the three authorized mathematical sources: `time_inhomogeneous_riffle_shuffle_unified_article.tex` and fresh text extracted from `2103.05068v3.pdf` and `2510.22783v1.pdf`. No existing review, project Lean source, or other mathematical source was read. No Lean code was written, no theorem statement was frozen by this review, and no compiler result is claimed.

The user has not supplied a Lean declaration name, goal state, or compiler error. No blocked declaration can therefore be identified honestly. The finite statements below are candidate interfaces, not an invented target.

The TeX block at lines 2562–2785 is enclosed in `comment`. Its lower-bound blueprint and random lower extension are inactive. The active lower proof starts at line 2788 and ends with `thm:buffered-reduced-lower-bound` at lines 5197–5207. In particular, the inactive near-critical cold-spot definition must not replace the active buffered witness.

## Relevant source interfaces

- `2510.22783v1.pdf`, Proposition 2.2, PDF page 8, proves the fixed-column graph representation by induction on the number of columns; the assertion is equality of total-variation distances, with an explicit inverse-permutation convention in its proof. The active TeX `lem:ub-graph-representation` (402–408) packages the inverse law directly. That orientation must be fixed once.
- `2103.05068v3.pdf`, Lemmas 3.1 and 3.3, PDF pages 10–11, provide the graph-component factorial estimate and sparsity reduction. These are finite deterministic combinatorial inputs, independent of the asymptotic profile.
- `2103.05068v3.pdf`, Proposition 6.1, PDF page 37, invokes Lalley's cold-set criterion. It does not contain a proved block-value bounded-differences lemma matching the new manuscript's `lem:block-bd`.
- `2510.22783v1.pdf`, Lemmas 6.3–6.6, PDF pages 52–53, isolate the cold-set criterion and the many-to-one union bound for random pile sizes. Their proof architecture cannot make a false new concentration lemma true.

## Source contract that must be resolved before any freeze

### Exact finite objects

The finite model consists of natural numbers N, k, K; k at least 2; natural counts n(j,a) summing to N for each column; a uniform distribution on column assignments with those counts; independent columns; an independent uniform permutation when using graph sorting. Row labels, sorted ranks, and integer coordinates of H are three distinct types and should remain distinct.

A useful primary encoding is a finite sample space of count-constrained functions, with probability and expectation as finite sums. Uniform column assignment is a subtype of functions from N labels to k digits whose histogram equals n. Full strings are functions on K positions. Prefixes may be bounded lists, with the legal predicate requiring each selected count to be positive. Zero counts remain allowed in the model.

An equivalent abstract encoding is the pushforward of a uniform permutation of a canonical multiset. This avoids counting assignments repeatedly but needs a proved equal-fiber-size statement. Equivalence to the first encoding is a theorem obligation, not an assumption.

### Asymptotic and measure-theoretic objects

The manuscript leaves several interfaces schematic:

1. A family of probability measures mu(t) alone does not specify measurability in t. Time integrals in (163) and all integrated inequalities require an explicitly justified measurable/integrable profile interface. Silently assuming continuity or a measurable kernel would strengthen the source contract.
2. The choices of small parameters at lines 477–488, uniform little-o terms, and "almost-like on every compact interval" need exact quantifier order. A single fixed positive profile tolerance is not identical to an approximation with arbitrarily small tolerances.
3. `accessible` in `def:recursive-first-moment-margin` (366–373), the regular event and exploration sigma-fields (1923–1982), and the 2k directional explorations are semantic descriptions, not complete algorithms or mathematical predicates. Their missing constructions are upstream dependencies of the exponential-moment proof.
4. The convention log_N(0) = minus infinity in lines 626–628 cannot be implemented with the real logarithm at zero. Retained nonterminal pairs have finite fluctuation cost; terminal cases need a separate branch. An optional real-valued fluctuation exponent can encode this faithfully without pretending that the real logarithm yields minus infinity.
5. Expressions involving N/log N must handle N=0 or 1 explicitly. Eventual asymptotic proofs can discard finitely many N; finite statements must not acquire N>1 as an unannounced hypothesis.
6. `lem:successive-thinning-tail` allows M=0 and conditioned residual size N-r=0. These are trivial probability cases that need branches; excluding them would change the statement.
7. The active random upper extension is `cor:random-time-profile-upper-bound` (1999–2012). A matching random lower theorem is only in the commented overview. A new active extension needs its own explicit statement and uniform deterministic test estimates.

## A confirmed mathematical obstruction

`lem:block-bd` (4951–4977) is false with its stated hypotheses. It allows an empty reservoir.

Take N=2, m=2, both relevant blocks of size 1, and reservoir size 0. The uniformly random partition has exactly two outcomes. Define f(V1,V2) to be 1 if 1 belongs to V1 and 0 otherwise. Fixing V2 fixes V1 uniquely, and fixing V1 fixes V2 uniquely. Therefore each stated coordinate oscillation condition holds with L1=L2=1/10: no alternative coordinate value is possible while fixing the other relevant block. Yet E f=1/2 and

    P(|f-E f| >= 1/2) = 1,
    2 exp(-2 (1/2)^2 / ((1/10)^2+(1/10)^2)) = 2 exp(-25) < 1.

This is a contradiction, with a positive denominator. The proof's purported coupling can change later relevant blocks, whereas the hypothesis controls only changes compensating in V0 with all other relevant blocks fixed. Those are different operations.

Its downstream path is:

    lem:block-bd
      -> lem:permutation-bd
      -> lem:lalley-comparison
      -> lem:lalley
      -> prop:cold-lower
      -> thm:buffered-reduced-lower-bound.

This is a mathematical obstruction. Proving `lem:block-bd` literally cannot be repaired by changing Lean encodings or finding another API. A stronger coupling hypothesis would change its assumptions and is forbidden after a freeze. The specific component concentration statement may have an independent proof under its original hypotheses, described below, but that does not prove the false general lemma.

There is also a false displayed Bonferroni step at lines 4574–4575 and again 4686–4691: one half of E(X)_2 minus one sixth of E(X)_3 need not be a lower bound on P(X>=2). At X=3 the pointwise left side is 2 and the indicator is 1. The valid two-term lower bound has coefficient one third on (X)_3. The manuscript's own central-window coefficients at line 4483, (-1)^r(r-1)/r!, agree with one third at r=3. This is a defective proof step; it does not by itself refute the occupancy conclusion.

## Two genuinely different routes for the component concentration statement

These are proposed routes for `lem:permutation-bd` (4979–5024), not tested Lean proofs and not an identification of the user's unknown blocked theorem. Both keep its original inputs: a deterministic path subgraph G, deterministic H, a reference M at least |H|, and a uniform permutation. Neither needs `lem:block-bd`.

### Direct finite counting route

1. Enumerate G-components from left to right as nonempty consecutive blocks. Sorting a block makes its internal edges deterministic ascents.
2. A boundary edge between adjacent blocks C,D is an ascent exactly when every value on C is less than every value on D. Its probability is 1/binomial(|C|+|D|,|C|).
3. Partition the relevant boundary edges by parity of the left component index, not parity of the vertex label. Within each family, the unions C union D are pairwise disjoint.
4. Prove by permutation counting that the induced relative orders on disjoint deterministic vertex sets are independent and uniform. An exact counting interface is: prescribing one relative order on each disjoint set A_i admits N! / product_i |A_i|! global permutations. Summing this count over acceptable local orders gives independence of the boundary indicators.
5. Apply the concentration theorem for sums of independent [0,1]-valued variables separately to the two parity families and a union bound. If b is the number of relevant boundary edges, this gives a bound at scale b; since b <= |E(H)| <= |H| <= M, it gives the claimed scale M.

All structural steps are finite-set/cardinality statements. Degenerate families b=0 are constant and must be handled separately. Constants can be reduced at the final scalar inequality; no additional hypothesis on the sizes of G-components is necessary.

### Abstract independent-key route

1. Generate independent atomless real keys indexed by vertices. Their rank permutation is uniform, proved from exchangeability and almost-sure distinctness.
2. Ranking preserves every strict comparison. Sorting values inside a component commutes with ranking for the comparisons being counted.
3. View the key vector of each G-component as one independent random object. A boundary ascent depends only on the adjacent two component vectors, through max(left)<min(right).
4. Apply a general helper theorem for a sum of bounded functions supported on edges of a bipartite path whose vertex variables are independent. Its two edge-color classes consist of independent summands; the helper's proof gives the same concentration scale.

The helper is stronger than this application but its independence input is proved from the key construction. It is not an axiom or an extra hypothesis on the original uniform permutation. This route trades finite permutation counting for product-measure, atomlessness, ranking, and independence APIs.

## Other finite theorem interfaces worth isolating

### Stable partition: lines 788–826

Direct route: for each full legal continuation, take the least depth at which the nonincreasing cost falls strictly below the fixed threshold; use depth K if there is none. Prove uniqueness, then identify the image with Gamma union Lambda, including the explicit singleton root and terminal branches. Partitioning is the fiber partition of this total stop map.

Abstract route: first prove a finite rooted-tree stopping-cut theorem. Inputs are bounded height, unique ancestors, a monotone stopping predicate along each branch, and terminal fallback. The cut is an antichain meeting each leaf path exactly once; cylinders over it partition the leaf set. Instantiate with legal prefixes and prove cost monotonicity from 0<n(j,a)<=N. The monotonicity is derived, not newly assumed in the application.

The Option-valued fluctuation convention above prevents real/extended-real coercions from obscuring this finite theorem. Contiguity in lexicographic order is a separate sorting lemma, unnecessary to prove the cylinder partition itself.

### Exact fixed-column factorial moments: lines 4340–4398

Direct route: count completions of prescribed distinct row labels. With R labels requesting m_a occurrences of each digit, probability is product_a (n_a)_(m_a)/(N)_R; impossible requests contribute zero. Independence of columns gives the product of these ratios. Expanding falling factorials of word counts as sums over injective row choices then gives the exact joint moment identity.

Abstract route: represent a fixed-count column as a random permutation of a canonical multiset, prove the sampling-without-replacement law for its restriction to an injection of row labels, and establish a general factorial-moment theorem for mutually exclusive categories. Instantiate the categories as distinct full words.

Keep the exact identities separate from the asymptotic approximation 1+O(K R^2/N), which adds positivity/size estimates already present in `lem:fixed-column-factorial`.

### Thinning transform: lines 3018–3167

Direct route: prove the one-step transform by a finite elementary-symmetric-polynomial inequality. The average product of x sampled entries from a vector containing m entries s and M-m entries 1 is at most the x-th power of its mean. This is precisely E(s^H) <= (1-q+qs)^x, including s in (0,1]. The scalar product inequality can be proved by finite smoothing or an established trusted theorem.

Abstract route: a kernel-level generating-function bound composes backwards. Set z_m=1/2 and z_(t-1)=1-q_t+q_t z_t. Then z_0=1-(product q_t)/2 and E(z_m^X_m)<=z_0^M. Markov's inequality yields the stated Chernoff constant. This avoids the recursive logarithms in the source proof. Conditional residual models are handled by a proved product-fiber factorization; admissibility and the residual counts in (3037) remain exact.

## API/encoding diagnosis boundary

Known mathematical failure: `lem:block-bd`, with the explicit two-point counterexample above. Known false proof step: the factorial Bonferroni coefficient. Known unspecified source dependencies: measurable time profile, exact parameter quantifiers, regular event, and exploration/accessibility construction.

Potential encoding difficulty: dependent prefix lengths; separating labelled rows from ranks; actual versus formal negative infinity; finite conditional probability versus conditional expectation; component index parity. Each has an equivalent representation strategy above.

Unknown API status: no current target, imports, toolchain, trusted lemma inventory, or compiler message has been supplied. It would be misleading to declare a mathlib theorem missing or to report either Lean strategy tested. Under the user's stop rule, compare the independent reports, record the literal source contract, and stop at the demonstrated mathematical obstruction rather than adding assumptions or writing an affirmative placeholder proof.
