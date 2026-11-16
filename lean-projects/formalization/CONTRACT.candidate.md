# Finite combinatorial formalization contract — candidate for independent review

Only the three user-named mathematical sources are used. Trusted Lean/mathlib source is allowed for implementation. No project probabilities, asymptotic hypotheses, auxiliary estimates, or sampling laws are assumed or asserted here. Every declaration below must be proved from its stated inputs; constructor proof fields and local proof facts are permitted, but no additional named theorem may be added after freeze. Implementation details of proofs and definitional notation may vary only without changing these mathematical definitions or statements.

## Standing data and exact conventions

Parameters N,k,K are natural numbers. PileProfile P contains counts n : Fin K → Fin k → Nat, N>0, k≥2, and for each column j the identity sum_a n(j,a)=N. K may be zero; individual counts may be zero. P.countAt(j,a) is n(j,a) for j<K and zero otherwise. P.probAt(j,a)=countAt(j,a)/N in the reals. NormalizedProfile k is the subtype of real k-vectors whose entries belong to [0,1] and sum to one; normalized(P,j), j∈Fin K, is the resulting vector; no limiting time profile is built into this finite structure.

Word k m = List.Vector (Fin k) m (lists of exactly m digits). Word order is the inherited ordinary list lexicographic linear order, NEVER coordinatewise function order. Prefix x y means x.toList is a List.IsPrefix of y.toList. Empty word is the empty vector. truncate(h:m≤n,y) has list y.toList.take m. appendDigit(x,a) has list x.toList ++ [a]. Legal P x means m≤K and every countAt(j,x[j]) is positive, j∈Fin m. Word mass λ(x)=product_{j∈Fin m} probAt(j,x[j]).

RawPrefix k K = dependent pair (m∈Fin(K+1), x∈Word k m). Node P is its legal subtype. depth is m; list is x.toList. Tree order is list prefix. The root is the empty legal node. The total parent operation deletes the final digit and fixes the root: depth(parent x)=depth x−1. A child y of x means prefix x y and depth y=depth x+1. FullWord P is the subtype of legal Word k K. cylinder(P,x), for a legal node x, consists of FullWord P extending x. An antichain U is a set of nodes with x,y∈U and prefix x y implying x=y; a cover means every FullWord lies in some cylinder from U.

ShuffleMatrix P consists of rows : Fin N → Word k K with exact column counts #{i : rows(i)[j]=a}=n(j,a). This is deterministic labelled data. sortPerm = Tuple.sort rows, a genuine permutation of Fin N. sortedRows = rows ∘ sortPerm. Reindex by any permutation changes row labels only and preserves the column counts.

rankSet(S,x) is the Finset {i∈Fin N : x.list is a prefix of sortedRows(i).list}. L(S,x)=#{i : take(depth x,sortedRows(i).list)<x.list}; U(S,x)=#{i : take(depth x,sortedRows(i).list)≤x.list}. Ranks are ZERO BASED: rankSet=[L,U)∩Fin N, count=U−L. This is the convention of 2103.05068v3 §4.1.1 with rank shifted by one. The sketch's direct comparison of a full row with a shorter prefix at lines 2951–2955 is not adopted. No empirical count is assumed positive merely because a word is legal.

shuffleGraph(S) is the SimpleGraph on Fin N with adjacency iff (i.val+1=j.val or j.val+1=i.val) AND sortedRows(i)=sortedRows(j). blockGraph(S,x) is the spanning graph on Fin N retaining precisely graph edges with both vertices in rankSet(S,x); vertices outside the block are isolated. Its edges agree with the paper’s induced graph, but its vertex type deliberately remains Fin N. shared adjacency for S,T is conjunction of their adjacency predicates. Reachability means mathlib SimpleGraph.Reachable.

For any finite linearly ordered type α and weights w:α→Real, define left(w,a)=sum_{b<a}w(b), right(w,a)=left(w,a)+w(a), interval(w,a)=Set.Ico(left,right). Generic weighted-interval results below use precisely nonnegative weights, with sum=1 only where stated. At every natural depth m, deterministic J_x is interval(λ,x), summing over ALL words of depth m, including illegal zero-mass words. Only the normalization and cover theorems impose m≤K; interval disjointness needs no depth bound. Define H_x={z∈Int : (z:Real)∈N • J_x}, where scaling means {(N:Real)*t : t∈J_x}. Define lexOpen(a,b)={x:Word k m : a<x and x<b}. No probabilistic expectation identity is claimed in this assignment.

## Frozen lemma candidates (universally quantified over displayed types)

### Profile and masses — Profiles.lean
P01 `countAt_of_lt`: j<K ⇒ countAt(j,a)=n(⟨j,h⟩,a).
P02 `countAt_of_ge`: K≤j ⇒ countAt(j,a)=0.
P03 `count_le_deck`: j∈Fin K ⇒ n(j,a)≤N.
P04 `prob_nonneg`: every natural j and digit a has 0≤probAt(j,a).
P05 `prob_le_one`: every natural j and digit a has probAt(j,a)≤1.
P06 `prob_pos_iff`: 0<probAt(j,a) iff 0<countAt(j,a).
P07 `prob_sum`: j<K ⇒ sum_a probAt(j,a)=1.
P08 `exists_positive_digit`: j<K ⇒ exists a, 0<countAt(j,a).
P09 `mass_empty`: λ(empty)=1.
P10 `mass_nonneg`: 0≤λ(x) for every Word k m.
P11 `mass_le_one`: λ(x)≤1 for every Word k m.
P12 `mass_pos_iff_legal`: for m≤K, 0<λ(x) iff Legal P x.
P13 `mass_sum`: for m≤K, sum_{x:Word k m} λ(x)=1.
P14 `mass_append`: λ(appendDigit(x,a))=λ(x)*probAt(m,a).

### Words and tree — Words.lean / PrefixTree.lean
W01 `prefix_refl`: Prefix x x.
W02 `prefix_trans`: Prefix x y and Prefix y z ⇒ Prefix x z.
W03 `prefix_length_le`: Prefix x y ⇒ m≤n.
W04 `prefix_eq_of_length_eq`: x,y:Word k m and Prefix x y ⇒ x=y.
W05 `empty_prefix`: Prefix empty x.
W06 `truncate_prefix`: m≤n ⇒ Prefix (truncate(h,y)) y.
W07 `prefix_iff_truncate`: for x:Word k m, y:Word k n, h:m≤n, Prefix x y iff truncate(h,y)=x.
W08 `prefix_comparable`: Prefix x z and Prefix y z ⇒ Prefix x y or Prefix y x (possibly different lengths).
W09 `take_lex_monotone`: for every m, List.take m is monotone for ordinary list lex order on List(Fin k).
W10 `prefix_lex_convex`: lists a≤b≤c, with x a prefix of a and c, imply x is a prefix of b.
W11 `legal_truncate`: Legal P y and m≤n ⇒ Legal P (truncate(h,y)).
W12 `legal_empty`: Legal P empty.
W13 `legal_append_iff`: Legal P (appendDigit(x,a)) iff Legal P x AND m<K AND 0<countAt(m,a).
W14 `legal_full_extension`: Legal P x ⇒ exists y:Word k K, Legal P y and Prefix x y.
T01 `node_prefix_refl`: tree-prefix x x.
T02 `node_prefix_trans`: tree-prefix x y and y z ⇒ x z.
T03 `node_prefix_antisymm`: tree-prefix x y and y x ⇒ x=y.
T04 `root_prefix`: tree-prefix root x.
T05 `parent_prefix`: tree-prefix (parent x) x.
T06 `parent_depth`: depth(parent x)=depth x−1.
T07 `parent_strict`: depth x>0 ⇒ depth(parent x)<depth x.
T08 `exists_child`: depth x<K ⇒ exists legal node y, Child x y.
T09 `cylinder_nonempty`: each legal-node cylinder is nonempty.
T10 `cylinder_mono`: tree-prefix x y ⇒ cylinder y⊆cylinder x.
T11 `cylinders_overlap_iff`: (cylinder x∩cylinder y).Nonempty iff tree-prefix x y or tree-prefix y x.
T12 `antichain_disjoint`: if U is an antichain, distinct x,y∈U have disjoint cylinders.
T13 `antichain_cover_unique`: if U is an antichain and covers all full legal words, every full legal word belongs to the cylinder of exactly one member of U.
T14 `cylinder_children`: depth x<K ⇒ for every full legal word s, s∈cylinder x iff exists node y, Child x y and s∈cylinder y.
T15 `tree_finite`: Node P is finite (Fintype/Finite instance, proved using dependent finite words).

### Matrices, ranks, and graphs — Matrices.lean / Graphs.lean
M01 `shuffleMatrix_nonempty`: exists a ShuffleMatrix P; no additional feasibility assumption.
M02 `row_legal`: every row of any ShuffleMatrix P is legal.
M03 `reindex_counts`: reindexing rows by any permutation preserves every column count (constructs another ShuffleMatrix P).
M04 `sorted_monotone`: S.sortedRows is monotone in ordinary word lex order.
M05 `sorted_row_legal`: every sorted row is legal.
M06 `sort_preserves_count`: for every predicate Q on Word k K (with classical decidability), #{i:Q(sortedRows i)}=#{i:Q(rows i)}.
M07 `rank_mem_iff`: i∈rankSet(S,x) iff L(S,x)≤i.val and i.val<U(S,x).
M08 `rank_count`: rankSet(S,x).card=U(S,x)−L(S,x).
M09 `endpoint_bounds`: 0≤L(S,x), L(S,x)≤U(S,x), U(S,x)≤N.
M10 `rank_convex`: i≤j≤l and i,l∈rankSet(S,x) ⇒ j∈rankSet(S,x).
M11 `rank_mono`: tree-prefix x y ⇒ rankSet(S,y)⊆rankSet(S,x).
M12 `rank_disjoint`: incomparable tree nodes x,y have disjoint rank sets.
G01 `graph_adj_iff`: adjacency iff neighbouring ranks and equal sorted words (as defined above).
G02 `graph_subpath`: every graph edge joins ranks differing by one.
G03 `adj_same_prefix`: graph-adjacent i,j have equivalent membership in every rankSet(S,x).
G04 `equal_rows_between`: i≤j≤l and sortedRows i=sortedRows l ⇒ sortedRows j=sortedRows i.
G05 `reachable_iff_eq`: graph-reachable i,j iff sortedRows i=sortedRows j.
G06 `block_adj_iff`: blockGraph(S,x).Adj i j iff shuffleGraph(S).Adj i j and i,j∈rankSet(S,x).
G07 `shared_adj_iff`: shared graph adjacency iff both shuffle graph adjacencies.

### Lexicographic intervals — Intervals.lean
I01 `left_nonneg`: weights nonnegative ⇒ 0≤left(w,a).
I02 `left_le_right`: weights nonnegative ⇒ left(w,a)≤right(w,a).
I03 `right_le_one`: weights nonnegative and sum w=1 ⇒ right(w,a)≤1.
I04 `right_le_left`: weights nonnegative and a<b ⇒ right(w,a)≤left(w,b).
I05 `weighted_intervals_disjoint`: weights nonnegative and a≠b ⇒ Disjoint(interval(w,a),interval(w,b)).
I06 `weighted_interval_empty_iff`: weights nonnegative ⇒ interval(w,a)=∅ iff w(a)=0.
I07 `weighted_interval_length`: right(w,a)−left(w,a)=w(a) (no positivity needed).
I08 `weighted_intervals_cover`: weights nonnegative and sum w=1 ⇒ union_a interval(w,a)=Set.Ico 0 1.
I09 `word_interval_empty_iff`: for x:Word k m, m≤K, J_x=∅ iff NOT Legal P x.
I10 `word_intervals_disjoint`: for distinct x,y:Word k m, J_x and J_y are disjoint.
I11 `word_intervals_cover`: for m≤K, union_{x:Word k m} J_x=Set.Ico 0 1.
I12 `lexOpen_convex`: a<y<b, a<z<b, y≤t≤z ⇒ a<t<b.

## Source issues and explicitly excluded work

The endpoint correction above is agreed independently by all three reviewers BEFORE freeze; it is a notation correction grounded in the older papers, not an added assumption. The expectation endpoint shift in 2510.22783v1 (2.15) is likewise not used. Fixed-count rows are dependent; no iid row claim is made. A prefix antichain need not cover the tree and a union of its cylinders need not be one interval. Matrix sorting is a proved permutation, never an input hypothesis. Probabilistic graph representation, concentration, asymptotic upper/lower bounds and the random mixture extension remain separately mapped dependencies, not placeholder Lean declarations. The 2Kk open-interval prefix decomposition used by exploration is beyond this basic finite foundation and is recorded as a subsequent combinatorial dependency.
