# Independent reconstruction review of the candidate manifest

Reviewed source: `formalization/CONTRACT.candidate.md`, compared only with my independent `reconstruction.md` report and the three user-authorized mathematical sources. No other reviewer report was read. No Lean code was written for this review.

**Verdict:** every candidate P01–P14, W01–W14, T01–T15, M01–M12, G01–G07, and I01–I12 is mathematically valid under the displayed conventions. There are 74 candidates. No mathematical assumption must be added, removed, or altered. The proof dependencies below are finite algebra/order/combinatorics plus trusted library facts, not probabilistic inputs.

Before freezing, make these representation details explicit:

1. `rankSet` is written using set notation but used with `.card`. Choose a `Finset (Fin N)`, or explicitly use finite-set `ncard`. This is a notation/type choice, not a changed set or statement.
2. `blockGraph` in G06 is a spanning graph on `Fin N` with outside-cylinder vertices isolated. The paper calls the graph on the cylinder's vertex set an induced subgraph. The two have identical relevant edges; the chosen spanning encoding is sound, but must not later be mistaken for equality of vertex sets or outside components.
3. `H_x` has a definition and no theorem candidates. No cardinality, boundary, or lattice-rounding claim about it is implicitly certified by I01–I12.

The endpoint convention already corrects the source's ambiguous comparison against a shorter word. It agrees with the intended rank counts and with 2103.05068v3 §4.1.1 after the shift to zero-based ranks. Allowing zero counts, empty realized cylinders, K=0, and empty intervals is essential and is respected by all candidates.

## Per-candidate review: profiles and masses

| ID | Verdict and compact proof | Dependencies |
| --- | --- | --- |
| P01 | Valid. Evaluate the `j<K` branch of `countAt`; proof irrelevance identifies the finite index. | definition |
| P02 | Valid. The `j<K` branch is impossible when K≤j. | definition; natural order |
| P03 | Valid. A nonnegative summand is at most the whole column sum N. | profile column-sum field; finite-sum inequality |
| P04 | Valid. Both the cast of a natural count and the real denominator N are nonnegative, with N positive. | N>0; cast and division order |
| P05 | Valid. For j<K use P03 and divide by N>0; for j≥K use P02 and obtain zero. | P01–P03; N>0 |
| P06 | Valid. Division by positive N preserves positivity; the natural cast is positive exactly for a positive natural number. | N>0; cast/division positivity |
| P07 | Valid. Distribute division across the finite sum, use the column sum, and simplify N/N=1. | P01; profile sum; N≠0 |
| P08 | Valid. If all counts were zero, their sum would be zero, contradicting N>0. | P01; profile sum; N>0 |
| P09 | Valid. The product over the empty coordinate type is one. | mass definition; finite empty product |
| P10 | Valid. Every factor is nonnegative. | P04; finite-product nonnegativity |
| P11 | Valid. A finite product of factors in [0,1] is at most one, including the empty product. | P04, P05; induction/product inequality |
| P12 | Valid. With m≤K supplied, legality is exactly positivity of every selected count. A finite product of nonnegative factors is positive exactly when each is positive. | P04, P06; finite-product positivity; legal definition |
| P13 | Valid. Induct on m. At successor depth every word is uniquely a length-m word followed by one digit; distribute the sum using P14 and P07. Base case is the unique empty word of mass one. | P07, P09, P14; vector last-digit decomposition; finite sums |
| P14 | Valid. Split the product of m+1 coordinates into the first m coordinates and the final coordinate. All old entries of the append agree with x, and the final entry is a. Works even for m≥K. | mass/append definitions; product over `Fin (m+1)` |

## Per-candidate review: words

| ID | Verdict and compact proof | Dependencies |
| --- | --- | --- |
| W01 | Valid. A list is its own prefix. | trusted list prefix reflexivity |
| W02 | Valid. Concatenate the suffix witnesses for the two prefix relations. | trusted list prefix transitivity |
| W03 | Valid. A prefix's list length cannot exceed the full list length; vector lengths give m≤n. | trusted prefix length inequality |
| W04 | Valid. The suffix witness has length zero when both lists have length m, so the lists and vectors are equal. | W03 / trusted equal-length prefix equality; vector extensionality |
| W05 | Valid. The target list itself is the suffix after the empty prefix. | list prefix definition |
| W06 | Valid. `take m` is a prefix of the original list; m≤n certifies the truncation vector's length. | trusted take-prefix fact |
| W07 | Valid. A length-m prefix is exactly the first m entries, in both directions. | trusted prefix/take equivalence; vector extensionality |
| W08 | Valid. Compare the two prefix lengths; the shorter consists of the same initial coordinates of z as the longer. | trusted common-prefix comparability, or W07 plus length trichotomy |
| W09 | Valid. A first strict lex difference before the cutoff survives taking; a later difference produces equal truncations. If one list is a prefix of the other, taking preserves prefix order. | ordinary list lex order; take induction |
| W10 | Valid. Taking |x| entries in a≤b≤c gives x≤take b≤x by W09. Hence take b=x; this equality forces b to have at least |x| entries and x to prefix b. | W09; list lengths; prefix/take equivalence; antisymmetry |
| W11 | Valid. m≤n≤K. The first m selected counts coincide with those of y and remain positive. | W06/W07; legal definition |
| W12 | Valid. 0≤K and there are no coordinate conditions. | legal definition |
| W13 | Valid. The bound m+1≤K is equivalent to m<K. Old selected counts give legality of x, and the unique new count is `countAt(m,a)`. Both directions use the exact same facts. | W11; append entries; natural successor order |
| W14 | Valid. Induct on K−m. If m=K use x. Otherwise choose a positive next digit by P08, append using W13, and continue. Prefix transitivity gives the final extension. | P08; W01, W02, W13; finite induction |

## Per-candidate review: prefix tree and cylinders

| ID | Verdict and compact proof | Dependencies |
| --- | --- | --- |
| T01 | Valid. Reduce the tree relation to list prefix. | W01 |
| T02 | Valid. Reduce to transitivity of list prefix. | W02 |
| T03 | Valid. Mutual prefixes have equal lists and equal depths. Dependent-pair extensionality then identifies the raw prefixes, and proof irrelevance identifies the legal subtype members. | W03, W04 / list prefix antisymmetry; subtype extensionality |
| T04 | Valid. The root list is empty, a prefix of every list. | W05; W12 |
| T05 | Valid. At the root it is reflexivity; otherwise the list with its last digit removed is a prefix. Its legality follows by prefix truncation. | W06, W11; parent definition |
| T06 | Valid. Taking depth−1 entries has exactly depth−1 entries; at depth zero the parent is the root. | vector length; natural subtraction; parent definition |
| T07 | Valid. A positive natural number is strictly larger than itself minus one. | T06; natural arithmetic |
| T08 | Valid. Choose a positive digit in the next column and append it; legality and depth certify a child. | P08; W13; append prefix/length |
| T09 | Valid. A legal prefix extends to a legal word of depth K. Package the extension as a FullWord. | W14; cylinder definition |
| T10 | Valid. Every full extension of y also extends x. | T02; cylinder definition |
| T11 | Valid. A common full word forces comparable prefixes. Conversely choose a word in the cylinder of the deeper of two comparable legal prefixes; nesting puts it in both. | W08; T09, T10 |
| T12 | Valid. A common member would force comparability by T11, contradicting antichain membership and distinctness. | T11; antichain definition |
| T13 | Valid. Cover supplies existence. Any two candidates have intersecting cylinders, so T11 and the antichain condition identify them. | T11; cover and antichain definitions |
| T14 | Valid. For s extending x, take its first depth(x)+1 digits; this is a legal node, a child of x, and a prefix of s. Conversely compose the two prefix relations. | W06, W07, W11; T02; child definition |
| T15 | Valid. There are finitely many depths ≤K; each finite-length vector over Fin k has finitely many possibilities; the legal subtype of that finite dependent sum is finite. | trusted finite vectors, dependent sums, and subtypes |

## Per-candidate review: matrices and rank sets

| ID | Verdict and compact proof | Dependencies |
| --- | --- | --- |
| M01 | Valid. Independently for each column j, concatenate n(j,a) copies of each digit a in alphabet order. The column list has length N. Its ith entry defines row i at column j. The list's digit counts are the required counts. Thus no extra consistency condition across columns is needed. | profile column sums; finite list replicate/concatenation counts; vector construction |
| M02 | Valid. The row's digit occurs at least once in each column because the row index itself belongs to its fiber. Exact column counts therefore make every selected pile positive. | matrix count field; finite-set membership implies positive cardinality; K≤K |
| M03 | Valid. A permutation gives a bijection between the two column fibers, preserving cardinality. | permutation bijectivity; finite cardinality under equivalence |
| M04 | Valid. Apply the trusted certified property of `Tuple.sort` to the actual ordinary lex order on `Word k K`. | sorting theorem; Word linear order |
| M05 | Valid. A sorted row is an original row at index `sortPerm i`. | M02; sorted-row definition |
| M06 | Valid. The row-index permutation bijects predicate fibers. Works for arbitrary Q; no property of Q or its relation to columns is needed. | permutation bijectivity; finite cardinality under equivalence |
| M07 | Valid. Truncated sorted rows are monotone by W09 and M04. Their values less than x form an initial segment of size L, and values at most x form one of size U. Their difference is exactly the ranks whose truncation equals x, equivalent to the prefix condition. | W07, W09; M04; finite monotone initial-segment cardinalities |
| M08 | Valid. M07 identifies the set with the half-open natural interval [L,U) inside Fin N; M09 ensures no clipping occurs. Its cardinality is U−L, including L=U. | M07, M09; finite interval cardinality |
| M09 | Valid. Naturals give 0≤L. The strict-comparison fiber is contained in the weak-comparison fiber, so L≤U. The latter fiber is a subset of Fin N, so U≤N. | definitions; finite-cardinality monotonicity |
| M10 | Valid. Either use M07 and transitivity of the two endpoint inequalities, or pull W10 back through monotonicity of sorted rows. | M07, or W10 and M04 |
| M11 | Valid. Compose the node-prefix and row-prefix relations. | W02; rank-set definition |
| M12 | Valid. A row in both rank sets gives a full word with both prefixes; W08 contradicts incomparability. | W08; rank-set definition |

## Per-candidate review: graphs

| ID | Verdict and compact proof | Dependencies |
| --- | --- | --- |
| G01 | Valid. Unfold the graph adjacency definition. The SimpleGraph constructor obligations follow from symmetric neighboring-rank and equality relations and from impossibility of i+1=i. | graph definition; natural successor inequality |
| G02 | Valid. Discard the equality conjunct of G01. | G01 |
| G03 | Valid. G01 gives equal row words, so substituting them makes the two prefix-membership predicates identical. | G01; rank-set definition |
| G04 | Valid. M04 gives row(i)≤row(j)≤row(l). Substitute row(l)=row(i) and apply antisymmetry. | M04; Word order antisymmetry |
| G05 | Valid. Along every graph walk, each edge preserves the row word, so reachability implies equality. Conversely, if i≤j have equal rows, G04 makes all intervening rows equal; all successive rank pairs are edges, furnishing a finite path. For j<i reverse the path. Reflexive reachability handles i=j. | G01, G04; finite interval induction; trusted reachability/path composition |
| G06 | Valid under the stated spanning-edge-restriction convention. Unfold the conjunction defining restricted adjacency. Symmetry and irreflexivity follow from the original graph. | block graph definition; G01 if constructor facts needed |
| G07 | Valid. Unfold the intersection adjacency predicate; its graph axioms inherit from either graph. | shared graph definition |

## Per-candidate review: weighted and lexicographic intervals

| ID | Verdict and compact proof | Dependencies |
| --- | --- | --- |
| I01 | Valid. A sum over a lower set of nonnegative weights is nonnegative. | finite-sum nonnegativity |
| I02 | Valid. Adding w(a)≥0 to left does not decrease it. | definitions; order under addition |
| I03 | Valid. The lower set of a together with a is contained in the full finite type; nonnegative weights give its sum ≤ total=1. | finite-sum monotonicity; sum=1 |
| I04 | Valid. If a<b, every index <a and the index a itself lie below b. Sum nonnegative weights over this inclusion. | finite-sum monotonicity; strict order transitivity |
| I05 | Valid. By linearity assume a<b or b<a. I04 orders the endpoint of the earlier interval before or at the start of the later one. A point cannot satisfy both half-open interval membership conditions. | I04; linear-order trichotomy |
| I06 | Valid. `Ico l (l+w)` is empty iff l+w≤l, equivalently w≤0; with w≥0 this is exactly w=0. | trusted half-open interval emptiness; real ordered-group arithmetic |
| I07 | Valid. `(left+w)−left=w` by additive cancellation. | definitions; ring/additive arithmetic |
| I08 | Valid. Enumerate the finite linear order increasingly. Its weighted intervals lie between consecutive partial sums starting at 0 and ending at 1; a finite induction shows their union is [0,1). Zero increments create empty intervals. If α is empty, sum=1 contradicts 0=1, so no extra nonemptiness assumption is needed. | nonnegative weights; sum=1; finite increasing enumeration; interval union/finite induction |
| I09 | Valid. I06 gives emptiness iff λ(x)=0. Since λ(x)≥0, this is equivalent to not 0<λ(x), and P12 identifies positivity with legality. | P10, P12; I06 |
| I10 | Valid. Apply generic disjointness to the finite word linear order with its nonnegative mass weights. No m≤K assumption is required. | P10; I05 |
| I11 | Valid. Apply generic coverage to word masses, whose total is one when m≤K. | P10, P13; I08 |
| I12 | Valid. From a<y≤t and t≤z<b obtain a<t<b. The other supplied endpoint inequalities are harmless and need not be used. | strict/weak order transitivity |

## Final approval boundaries

All 74 mathematical statements are approved for freezing. The recommendations about finite-set notation and the spanning block graph only make already-intended definitions explicit. This approval does not cover new theorem statements, a later strengthening to component cardinality or weighted prefix refinement, the 2Kk decomposition, or probabilistic statements. Those are useful future dependencies but are not secretly included in this manifest.

No counterexample appears in the permitted degenerate cases: at K=0 there is one empty word and every row equals it, so the shuffle graph is the entire N-vertex path; zero pile counts remove legal branches and give zero masses without invalidating a weighted partition; legal cylinders may be unoccupied in a particular matrix; N>0 is already frozen and is exactly what profile normalization and positive-column-digit existence use.
