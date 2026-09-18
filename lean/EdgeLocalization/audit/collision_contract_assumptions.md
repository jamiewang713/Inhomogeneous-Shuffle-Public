# Independent assumptions audit for an additive collision contract

This is a pre-freeze mathematical audit, not an implementation or a replacement for any v1 statement. I read `audit/frozen_contract.md`, revisited the original TeX's model, graph, ambient, and density passages, and checked the corresponding fixed-column construction and pair calculation in the two permitted older papers. The preceding independent whole-file reread remains the source interpretation audit. No Lean file, source statement, or v1 contract was changed.

## Verdict and source boundary

The exact internal collision route is valid under the source's original deterministic-count law. It needs neither an endpoint estimate nor a concentration, stable-block, good-column, or first-moment-margin hypothesis. Its only finite model requirements are the specified integer column counts and their sums, a fixed bounded prefix, and the actual uniform law on all matrices with those counts.

The relevant source passages are:

- TeX lines 95–113: deterministic nonnegative integer pile counts summing to N; the probability refers to the associated shuffle matrix.
- TeX lines 388–392 and 449–451: uniform matrices with prescribed column counts, equivalently sampling each column as a uniform arrangement of its multiset.
- TeX lines 460–472: the graph uses equal adjacent rows after lexicographic sorting, and a prefix block counts edges whose two rows have that prefix.
- TeX lines 1515–1523: the proposed internal-edge estimate uses the fixed-count tail pair factor. The present argument proves its unconditioned finite content directly, avoiding the later endpoint argument.
- TeX lines 2917–2923: the lower half explicitly states independence of the fixed-count columns.
- `2510.22783v1.pdf`, Section 2.2, printed p. 7: the same uniform prescribed-count matrix and lexicographically sorted graph. Lemma 4.14, printed p. 27: the tail factor is the product of sums of n_l(n_l−1)/(N(N−1)).
- `2103.05068v3.pdf`, Lemma 4.12, printed p. 24: the analogous edge-to-pre-sorted-pair argument in the independent-digit model. Its independent-row premise must not be imported into the fixed-count model.

The additive result is a different intermediate theorem from the blocked printed −cF density bound. Its direct finite statement does not claim the exponent translation, small-class summation, or conditional exploration theorem has also been formalized.

## Audited choice of probability model

### Preferred direct model

For natural N and k, and n : Fin k → ℕ with sum_l n(l)=N, define

```
FixedColumn(n) = {c : Fin N → Fin k // for every l, #{i : c(i)=l}=n(l)}.
```

This is exactly the source's finite sample space for one column. Give it uniform weight `1 / card(FixedColumn(n))`. The positive cardinality and normalization are to be proved, not supplied as probability assumptions.

The proposed nonemptiness construction is sound: the disjoint union `Σ l : Fin k, Fin(n(l))` has cardinality N; an equivalence with Fin N followed by the first projection supplies a column with the prescribed histogram. Its digit-fiber cardinalities must be checked. No extra choice of a feasible column needs to appear as an assumed field once this construction is proved.

For K columns with counts n_j, the full sample space is the dependent finite product `Π j : Fin K, FixedColumn(n_j)`. Its uniform law is the source's uniform matrix law. Alternatively, the product of the separately constructed uniform column laws gives the same law; prove this equality or its rectangular-event factorization. The counts may vary arbitrarily with j, including repeated count vectors. Different column coordinates remain independent even when their count vectors agree.

Row reindexing by any permutation of Fin N acts bijectively on FixedColumn(n). Histogram preservation, preservation of the uniform law, and one/two-label exchangeability must all be derived from this action. None belongs in the model as an assumed exact-law field.

### Other model options

Uniformly permuting each of several deterministic columns independently is also valid. Repeated entries do not invalidate it, but identifying its pushforward with the uniform assignment law requires a proof that every arrangement has the same number of preimages, or an equivalent transitivity argument. Direct uniform FixedColumn avoids this unnecessary bridge.

A single shared row permutation applied to all deterministic columns is not the source law: it generally correlates different columns. Independent row strings with probabilities n_j(l)/N are also not the source law: they do not retain the deterministic column counts. The two-row falling-factorial correction is essential.

## Exact finite definitions to freeze additively

The following are proposed mathematical data boundaries. Their final Lean spelling should be compared with the other independent reports before the new freeze.

1. Natural N, k, K, count arrays n_j(l), and proofs `sum_l n_j(l)=N`. These are pile feasibility identities from the source. Bounds `0≤n_j(l)≤N` and nonempty column sample spaces are consequences to prove.
2. The direct column and matrix sample spaces and their constructed uniform `FiniteLaw` values. Use the existing v1 definition of finite law unchanged.
3. A deterministic prefix x of length M≤K, with digits in Fin k. Positivity of its pile counts is unnecessary: a zero-count prescribed digit simply gives probability zero. If a List ℕ is used instead, its length bound and each digit's range must be represented explicitly, or invalid prefixes must receive an explicit zero case. A product over a clipped prefix does not correctly handle a word longer than K.
4. A full row is the ordered list of all K column entries, encoded as natural digits for compatibility with v1. Only indices below N are inspected. State an exact encoding bridge for equality and prefix membership; specify any extension of the row function beyond N once.
5. Original-row occupancy and unordered collision pairs use the existing v1 predicates. Define a lexicographically sorted deck from these actual rows and prove it is a reordering of them. Alternatively, prove the needed inequality for every row permutation, then instantiate it with a proved sorting permutation.
6. For N≥2, put

```
p_j(l) = n_j(l)/N,
a_j(l) = n_j(l)(n_j(l)−1)/(N(N−1)),
lambda_x = product_{j<M} p_j(x_j),
mu_x = N lambda_x,
A_x = product_{j<M} a_j(x_j),
q_x = product_{M≤j<K} sum_l a_j(l).
```

Here finite products over an empty set are 1. If these arithmetic definitions are made for all N using Lean's total division, record explicitly that the probability interpretation of a_j concerns distinct row labels, which can exist only for N≥2. The N=0 and N=1 graph conclusions are proved separately before cancellation. Either this total convention or an N≥2 domain is coherent; it must be chosen before coding.

The products are indexed by absolute shuffle time. A fixed ambient prefix is already part of x in this unconditional calculation. No ambient expected size is substituted for the sampling population N.

## Minimal proof-obligation inventory

These are exact mathematical boundaries, not assumed interfaces. Arithmetic rewrites can stay inside their corresponding proofs; if additional named project lemmas are planned, include their actual statements in the additive freeze before implementation.

| Item | Statement and domain | Dependencies and case notes |
|---|---|---|
| C01 Feasible column | For every n with sum n=N, FixedColumn(n) is nonempty. | Construct via the finite disjoint union; includes N=0 and k=0 when feasible. |
| C02 Uniform finite law | A nonempty finite sample space has uniform weights summing to 1; each event has probability its cardinality divided by the sample-space cardinality. | General finite arithmetic; apply C01 rather than assuming column nonemptiness. |
| C03 Uniform reindexing | A bijection of a nonempty finite sample space preserves its uniform event probabilities and expectations. | Finite change of variables, C02. |
| C04 Column row action | Reindexing a column by any permutation of Fin N preserves every histogram and is an equivalence of FixedColumn(n). | Pointwise finite count bijection, then C03. |
| C05 Histogram sums | For a fixed column and digit l, the sum over row labels of `1_{c(i)=l}` is n(l), and the sum over ordered distinct labels of `1_{c(i)=l=c(j)}` is n(l)(n(l)−1). | Histogram definition and finite counting. No n(l)≥2 hypothesis. |
| C06 One-label probability | For each i : Fin N and digit l, P(c(i)=l)=p(l). | C04 gives identical marginals across labels; C05 and normalization identify the value. The existence of i forces N>0. |
| C07 Two-label probability | For distinct i,j : Fin N and digit l, P(c(i)=l and c(j)=l)=a(l). | C04 gives invariance on ordered distinct label pairs; C05 identifies the common value. Distinct labels force N≥2. |
| C08 One-column pair collision | For distinct i,j, P(c(i)=c(j))=sum_l a(l). | The same-digit events in C07 form a disjoint finite partition. |
| C09 Independent column law | The uniform matrix law is the product of the uniform column laws; for predicates H_j on columns, P(for every j, H_j(column_j))=product_j P(H_j). | Finite product cardinality or direct factorization of finite sums. Includes K=0. |
| C10 Row encoding | Encoded row equality is coordinatewise equality, and x prefixes an encoded row exactly when its first M coordinates are x. | M≤K and digit encoding; no probabilistic hypothesis. |
| C11 Prefix marginal | For each original label i, P(x prefixes row_i)=lambda_x. | C06, C09, C10. Includes M=0 and zero-count digits. |
| C12 Prefix-pair collision | For distinct original labels i,j, P(row_i=row_j and x prefixes row_i)=A_x q_x. | C07 on prefix coordinates, C08 on tail coordinates, C09, C10. No division by prefix probability. |
| C13 Occupancy mean | E(occupancy count)=N lambda_x=mu_x. | C11 and v1 F12. N=0 is an empty sum. |
| C14 Pair count | The number of unordered distinct label pairs is choose(N,2). | Exact finite counting, including N=0/1. |
| C15 Exact collision mean | E(collision-pair count)=choose(N,2) A_x q_x. | C12, C14 and finite sum interchange. For N=0/1 both counts are zero; handle before any division. |
| C16 Reordering invariance | Occupancy cardinality and collision-pair cardinality are unchanged by a permutation of the rows. | Pointwise bijections. For unordered pairs, normalize the image order or use unordered-pair objects; the raw map (i,j)↦(σi,σj) does not preserve i<j. |
| C17 Actual sorting bridge | The chosen lexicographic sorting produces N rows and a permutation of the original rows. | Prove using the sorting implementation and its trusted permutation/order theorems. Repeated words and arbitrary tie order are allowed. |
| C18 Column comparison | For 0≤n(l)≤N and N≥2, 0≤a(l)≤p(l)^2. Consequently 0≤q_x≤product_tail sum_l p_j(l)^2 and 0≤A_x≤lambda_x^2. | Exact rational arithmetic and monotonicity of nonnegative finite products. Include n=0 and n=1 separately where casts of natural subtraction require it. |
| C19 Density versus squared mean | For every v1 finite law and every random deck, edgeDensity≤(E edgeCount)^2. | Nonnegative edge probabilities give sum p_i²≤(sum p_i)²; v1 F12 identifies the sum. This is new relative to F22 and holds for every N. |
| C20 Expected sorted edges | For N≥2, E(sorted internal edgeCount)≤choose(N,2) A_x q_x≤((N−1)/(2N)) mu_x² q_x≤mu_x² q_x/2. | v1 F21/F24, C15–C18. Nonnegative factors justify all products. |
| C21 Exact density bound | For N≥2, sorted internal edgeDensity≤mu_x^4 q_x²/4. | C19, C20, and nonnegativity before squaring. |
| C22 Empty/single-row completion | For N=0 and N=1, all internal edge counts and densities and all distinct collision-pair counts are zero. | v1 F17/F18 for edges, direct empty-pair proof, finite-law expectation of zero. This closes the finite deck domain. |

C06/C07 can be obtained by averaging the fixed histogram sums over the uniform law; they need no factorial formula for the number of all column assignments. To prove the two-label exchangeability used in C07, construct a row permutation carrying one ordered distinct pair to another. Do not silently use a transposition that sends only one label correctly while disturbing the other.

C15 is an equality for the unordered collision count, not for the adjacent-edge count. A repeated full word appearing r times contributes choose(r,2) collision pairs and at most r−1 adjacent edges. Equality between these two statistics fails at r≥3.

## Explicit hidden-case checklist

- **N=0.** Each feasible count is zero, the column is the unique empty function, and the matrix law remains inhabited. No label evaluation theorem is instantiated. Graph and collision counts are zero.
- **N=1.** Columns are deterministic assignments, there is no pair of distinct labels, and all graph counts are zero. The real expression N(N−1) must not be cancelled.
- **K=0.** The product sample space is a singleton even if N>0. Every full row is the empty word. For the empty prefix, occupancy=N, collision count=choose(N,2), and edge count=N−1 for N≥1. In particular q_x=1 for the empty tail, not 0.
- **k=0.** Feasibility forces N=0 whenever a column is present. When K=0 no column feasibility condition constrains N. The direct product model still exists. One can retain the source's k≥2 as explicit model data, but it is not needed by the finite calculations and must not be introduced merely to avoid these cases.
- **M=0 or M=K.** The prefix product or tail product respectively is 1. Full-word prefixes are valid terminal cylinders; no stochastic tail is needed for the pair-count argument.
- **Zero-count prefix digit.** Prefix occupancy and pair probabilities are zero. This does not require a legal-word positivity hypothesis. Avoid ratios conditional on such an event.
- **Pile size one.** Its prescribed same-digit two-label probability is zero. Falling factorials must be exact; replacing them by the independent-row square would destroy this case.
- **Deterministic full pile.** A column with one pile N and all others zero is allowed. Its pair collision factor is 1 for N≥2. No goodness or nondegeneracy assumption is warranted.
- **Zero tail factor.** If a tail column has no two rows with the same digit, full-word collisions and internal edges are impossible. Squaring or multiplying zero causes no exceptional case in the final bound.
- **Overlong or out-of-alphabet prefix.** Either exclude it by the prefix representation, or prove its occupancy is zero in a separate case. It must not be approximated by the in-range coordinates.
- **Ties in sorting.** Any order among equal full words gives the same sorted word list and collision count. No distinctness-of-rows hypothesis is allowed.
- **Outcome-dependent sorting.** C16 is pointwise in each row permutation, so the sorting permutation may depend on the whole matrix. It need not be independent of the matrix.
- **Ordered versus unordered normalization.** C07 counts ordered distinct row labels with denominator N(N−1); C15 sums only i<j, producing choose(N,2), and C20 obtains the factor 1/2. A factor of two must not be lost at this interface.
- **Natural subtraction and casts.** `((n*(n−1):ℕ):ℝ)` is visibly nonnegative; `(n:ℝ)*((n:ℝ)−1)` agrees after checking n=0 as necessary. A bare cast identity for n−1 cannot be used at n=0.
- **Row positions outside N.** v1 only inspects positions below N. A padding definition for encoded rows is harmless only if every bridge checks this bound.

## Sorting, recentering, and conditioning are different interfaces

The collision count is invariant under all row permutations. The adjacent-edge set and its density generally are not. The proof uses an upper bound by a permutation-invariant statistic, not invariance of the edge events themselves.

If edges are recentered at a random ambient left endpoint, call their density D_x^rel. The finite inequality D_x^rel≤(E e_x)² still holds because recentering preserves the edge count and uses a fixed finite ambient indexing range large enough to contain every shifted edge. This does not prove D_x^rel=D_x for global positions and does not preserve the number of shared edges after independently translating two random copies. An implementation of only global positions must not be described as having constructed this additional coordinate bridge.

No conditional exploration result is needed for C01–C22. The following precise optional conditional extension is sound if separately frozen and proved from the product law:

```
Let Q_x be the prefix occupancy and C_x the full-word collision-pair count.
For every q : ℕ,
E[C_x * 1_{Q_x=q}] = choose(q,2) q_x P(Q_x=q).
```

More generally, the same identity with the appropriate prefix-measurable multiplier follows after fixing every column through M and counting the resulting deterministic membership set. This formulation does not divide by a possibly zero event probability, handles q=0/1 and q>N, and gives the source's internal conditional edge bound when an actual positive-probability occupancy event is conditioned upon.

When only the initial columns are revealed, future columns are still uniform with their original counts on the whole population N. Even if the selected prefix membership set has q rows, two-label sampling denominators remain N(N−1); there is no independent fixed-count law on a population q unless an additional residual-count reveal has been explicitly analyzed. Arbitrary exploration events can couple columns and do not inherit the product law from C09. A future residual-population theorem must construct that conditional law with its actual remaining labels and counts.

## Additive-freeze acceptance conditions

The direct FixedColumn design is approved as a mathematically faithful basis for an additive contract, subject to independent comparison of its concrete declarations. Keep every existing D1–D8 and F01–F33 byte-identical. Add the new sample-space definitions, proved law constructors, exact probability statements, sorting bridge, and density bound in a separately identified contract extension.

Do not assume uniformity through histogram/exchangeability fields, a pair-collision interface, a sorting witness that is never constructed, or an unexplained conditional-model hypothesis. Each item above has a direct finite proof. No concentration assumption, extra axiom, or unproved placeholder is required. The sharper −cF estimate and the outstanding large-block/localization/exploration claims remain outside this additive result.

## Comparison with the completed proposed statement contract

I independently compared every definition C.D01–C.D14 and every statement C.01–C.57, including the separate C.20a/C.20b declarations, in `collision_contract_statements.md` against the audit above. **All proposed core mathematical statements are accepted.** There is one wording correction to make in the degenerate-case discussion before freeze; it requires no change to a theorem or its hypotheses.

### Definition-by-definition comparison

| Definition | Verdict and exact checks |
|---|---|
| C.D01 | Accepted. Nonempty is the necessary domain of a uniform finite probability law. It is derived for fixed columns, not a new feasibility assumption. Positive cardinality supplies normalization. |
| C.D02 | Accepted. The supplied normalized laws suffice to construct their dependent finite product; no separate nonempty-fiber premise is needed. The empty coordinate product gives the single empty function weight 1. |
| C.D03 | Accepted. The subtype contains exactly histogram identities. Its finite enumeration is derived from finite functions and a decidable subtype predicate. |
| C.D04 | Accepted. Precomposition by a row permutation preserves histogram counts; the inverse uses the inverse permutation. C.08 is to precede this constructor as needed. |
| C.D05 | Accepted. The law is constructed uniformly using C.06. Its weights depend on counts, not the particular proof of their sum. |
| C.D06 | Accepted. The independent column product has the source sample space. C.17 certifies its uniformity on full matrices, rather than assuming it. |
| C.D07 | Accepted. `List.ofFn` in increasing Fin order preserves the source coordinate order and permits an empty alphabet when M=0. |
| C.D08 | Accepted. The row list has all K column entries in order. The zero-based adapter accesses only labels below N and fixes the outside value as `[]`; no default digit is needed. |
| C.D09 | Accepted. Sorting distinct original labels by their row words allows equal words without assuming antisymmetry on labels. Totality and transitivity are consequences of the row-word linear order. |
| C.D10 | Accepted. The proved length, nodup, and membership facts construct an actual index-to-label equivalence. This supplies the needed sorting permutation without assuming a row-matching witness. |
| C.D11 | Accepted. The source's sorted deck is the outcome-dependent permutation from C.D10 applied to the actual original rows. |
| C.D12 | Accepted. Both diagonal and off-diagonal two-digit factors have the correct ordered-distinct-row denominator. Natural falling factorials handle count zero/one; total division gives algebraic zero factors when N≤1. |
| C.D13 | Accepted. Prefix inclusion uses M≤K, and the suffix finset is exactly the complement in Fin K. Products for empty prefix/tail are 1, including K=0. |
| C.D14 | Accepted. Expected occupancy is a later proved equality, not an assumed property of this formula. |

I checked the permitted local mathlib sources for the two important sorting interfaces. `Mathlib.Data.List.Lex` supplies the lexicographic linear order on lists. `List.Nodup.getEquivOfForallMemList` really has forward map `l.get`, domain `Fin l.length`, and codomain the label type. `List.sorted_mergeSort'` requires totality and transitivity, while its following equality theorem additionally requires antisymmetry. The proposed proof must use the former; it does not need the latter. These are trusted API checks, not a claim that project code has been implemented or compiled.

### Complete statement comparison

| Statements | Verdict and substantive case checks |
|---|---|
| C.01 | Accepted, including an empty event. Nonempty refers to the sample space, not to the event. |
| C.02 | Accepted for any sample-space equivalence; no probabilistic invariance field is introduced. |
| C.03–C.04 | Accepted for arbitrary finite dependent products and empty coordinate selections. The event is true outside the selected finset. |
| C.05 | Accepted. Its explicit disjointness condition is the exact generic finite-union requirement. In the column application it follows from digit equality. An empty index type gives probability zero. |
| C.06–C.08 | Accepted. Feasible columns are constructed; n(a)≤N and reindexing of the histogram are derived. All include empty finite types when their stated data exist. |
| C.09 | Accepted for N=0 and N=1 by empty ordered-distinct-pair sets. The falling factorial is natural multiplication/subtraction. |
| C.10 | Accepted. If a≠b, the two digit fibers are disjoint, so every Cartesian pair has distinct labels. If a=b, exactly the diagonal must be removed. Neither branch requires positive counts. |
| C.11 | Accepted. The two pairs need only be individually distinct. They may overlap in any manner, including reversal; the implementation must handle those possibilities. |
| C.12 | Accepted as a consequence of the constructed row-action equivalence and the constructed uniform law. |
| C.13 | Accepted. A row label itself forces N>0. Summing exchangeable probabilities gives n(a), including n(a)=0. |
| C.14 | Accepted for general a,b, with its explicit a=b/a≠b split. Distinct row labels force N≥2 before division; no extra deck-size hypothesis is needed. |
| C.15 | Accepted. Equal digits are a disjoint union of the diagonal two-digit alternatives; the off-diagonal factors are not included. |
| C.16 | Accepted pointwise from a zero histogram count; no uniform-law premise is needed. |
| C.17 | Accepted. Uniform weights of all coordinate laws multiply to the reciprocal cardinality of the full product, including K=0. |
| C.18–C.19 | Accepted, including zero-length lists. |
| C.20a | Accepted; the value is independent of the proof of the row-index bound by proof irrelevance. |
| C.20b | Accepted, including N=0 and t=0. It is an adapter identity, not a statement about an actual row outside the deck. |
| C.21 | Accepted. The length bound M≤K is essential and explicitly present through the prefix data. Equality of natural digit encodings reflects equality in Fin k. |
| C.22 | Accepted. When K=0 both rows are the empty list and the coordinate condition is vacuous. |
| C.23 | Accepted exactly as stated: every in-alphabet list has the vector representation, regardless of its length. See the prose correction below. |
| C.24–C.26 | Accepted. Merge-sort preserves the list of distinct labels, so length, nodup, and occurrence of every Fin N label follow without any assumption about distinct row words. N=0 gives the empty list and empty equivalence. |
| C.27 | Accepted. It asserts monotonicity of row values in position order, not monotonicity of the label permutation itself. Equal row words give weak inequality. |
| C.28 | Accepted for all list prefixes, by a finite label bijection. |
| C.29 | Accepted. The image pair must be oriented by minimum/maximum; its two orientations require the equal-row prefix-transfer argument. Permutation injectivity excludes equal image labels. |
| C.30–C.31 | Accepted pointwise in each sample by C.28–C.29. The sorting permutation may depend on all column data. No density-invariance claim is made. |
| C.32 | Accepted only for a fixed original label, exactly as stated. It cannot be reused as a fixed sorted-position marginal. |
| C.33 | Accepted. Prefix coordinates prescribe both digits; tail coordinates require equality. The formula has no division by a possibly zero prefix probability. Empty prefix and tail cases are exact. |
| C.34–C.35 | Accepted for all N. N=0 gives an empty sum and prefixMean=0; sorting preserves the cardinality before taking expectation. |
| C.36–C.37 | Accepted for arbitrary rows/all N; increasing natural pairs count choose(N,2), including the two small-deck cases. |
| C.38–C.39 | Accepted for all N. N=0/1 must be settled using zero collision counts before C.33. The right side then vanishes through choose(N,2), even when empty products equal 1. |
| C.40–C.41 | Accepted without feasibility hypotheses: every numerator and denominator in these total rational expressions is nonnegative. |
| C.42 | Accepted on the explicit N≥2 arithmetic domain. Zero and one pile sizes may need separate cast/subtraction branches; feasibility provides the only upper bound n(a)≤N. |
| C.43–C.44 | Accepted. Nonnegative sums/products also cover arbitrary suffix start M>K, when the suffix factors are empty products equal to 1. |
| C.45–C.46 | Accepted by monotonicity of nonnegative products and C.42. No positive-factor division or logarithm is used. |
| C.47 | Accepted as a new generic consequence of v1. The sum-square inequality uses nonnegative marginal probabilities and v1 F12; no location, independence, or sorting assumption is required. |
| C.48–C.49 | Accepted by empty increasing-pair sets. |
| C.50 | Accepted. For N≥2 the coefficient is exactly (N−1)/(2N); for N=0/1 both sides are zero under the explicitly fixed total-division convention. |
| C.51–C.52 | Accepted with nonnegative factors. For N=1 the half-mean upper bound can be positive when the tail is empty, which is harmless; these statements do not claim equality. |
| C.53 | Accepted; both expectations are nonnegative before squaring their comparison. It correctly distinguishes collision count from edge count. |
| C.54 | Accepted as the all-size exact mean/tail bound. It contains no small-block premise or spatial spreading factor. |
| C.55 | Accepted for every allowed prefix; the full-word terminal case is included without any small-mean assumption. |
| C.56 | Accepted because no Fin K index satisfies K≤j.val. |
| C.57 | Accepted for the unique function on Fin 0, even when Fin k is empty. All three conclusions concern genuine empty objects/products. |

### Remaining pre-freeze issue and scope decisions

The single correction is in the case paragraph headed “A prefix list longer than K or containing a digit outside Fin k.” It currently says that no theorem claims C.23 encodes these lists. This is inaccurate for a list longer than K whose digits all lie in Fin k: C.23 does encode it, as it should. The precise distinction is:

> C.23 represents every in-alphabet list. To use that representation in the matrix-prefix theorems, one also supplies its length bound M≤K. Out-of-alphabet lists are outside C.23; overlong lists are outside those bounded matrix-prefix applications.

This is a documentation correction, not a mathematical rejection or request to modify C.23. Apart from it, there is no unresolved assumption or finite-case blocker in the core inventory. The new proof may proceed only after the independent reports are compared and the additive contract is explicitly frozen; v1 stays byte-identical.

The optional O.D01–O.D02/O.01–O.07 extension is also mathematically sound on independent review. Its slice formula conditions only on prefix occupancy and is stated without division, so q=0/1, q>N, and zero-probability slices are correctly included. Its splitting equivalence and product-expectation identity must be constructed, and no arbitrary exploration conditioning follows from them. This review does not select the optional extension for implementation: whether it is included in the freeze must be recorded explicitly. Omitting it leaves the occupancy-conditioning component outstanding without weakening or changing the accepted core.
