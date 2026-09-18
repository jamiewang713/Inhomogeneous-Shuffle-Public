# Independent threshold and hidden-assumption audit

Reviewer role: adversarial mathematical review, before any statement freeze. Only the three user-authorized mathematical sources were read. PDF citations below give the printed section/lemma and the corresponding derived-text lines in `tmp/lower-bound-sources`. No outside mathematical source is used.

## Verdict

Do not freeze the full time-inhomogeneous cold-spot theorem as proved. The current article contains an explicitly false bounded-difference lemma and an explicitly false inclusion-exclusion inequality. Several other proofs suppress errors or conditions that matter for formalization. The finite full-word increasing-run obstruction, exact finite digit-profile identities, finite hypothesis testing, and the many-to-one mixture test are suitable targets. The cold witness algebra can be formalized as algebra, but its realization as a cold set with enough graph edges is additional mathematics, not a consequence of those identities.

The large lower-bound overview at TeX lines 2562–2786 is inside a `comment` environment. Its conditions and identities must not be mixed with the later active lower-bound statements.

## Explicit errors and repairs

### 1. False block value-set bounded differences

`lem:block-bd`, TeX lines 4951–4977, asserts a McDiarmid bound for uniform disjoint value sets from coordinate oscillations obtained by adjusting only a reservoir. This is false.

Counterexample: let N=2, m=2, both blocks be singletons, and the reservoir be empty. Set f=1 if value 1 lies in the first block. The two equiprobable partitions give f=0 or f=1. Once either of the other blocks is fixed, the remaining block is uniquely determined, so the coordinate-oscillation hypothesis holds with L1=L2=1/10. Yet at t=1/2 the left side is 1 and the claimed right side is 2 exp(-25)<1. The martingale coupling in the proof cannot keep all other relevant blocks unchanged.

The application `lem:permutation-bd`, lines 4979–5024, inherits this invalid proof. Its particular conclusion has a plausible independent proof: generate the uniform rank permutation using independent continuous labels on vertices, group those independent labels by deterministic graph component, and sort inside each component. Each component-label vector changes at most its two boundary comparisons, while internal comparisons remain forced. An ordinary independent-input bounded-difference argument then applies. This is a proposed new proof, not a theorem available from the current text.

### 2. False Bonferroni coefficient

`lem:two-category-poisson`, proof around lines 4560–4574 and 4679–4692, uses

    (1/2) E(X)_2 - (1/6) E(X)_3 <= P(X >= 2).

This is false: X identically equal to 3 gives 3-1=2 on the left and 1 on the right. The valid first two terms of the indicator inversion use coefficient -1/3, not -1/6. The same error occurs when the expressions are multiplied by another event indicator. The article's earlier definition a_r=(-1)^r(r-1)/r! in `lem:central-window` gives the correct coefficient a_3=-1/3.

### 3. Central-window truncation argument is incomplete

`lem:central-window`, lines 4450–4540, establishes a polynomial identity only on X+Y<=R_N, but then substitutes unrestricted factorial moments and estimates only the probability of the complementary event. A high-degree polynomial can be arbitrarily large on that complement, so a small complementary probability does not justify this substitution. A global Bonferroni inequality with a controlled next-order remainder, or a separate weighted-tail estimate, is needed.

The displayed coefficient-error bound also has the factor (1+mu)(1+nu). The hypothesis epsilon_N N^(2 L_*)=o(N^(-4 a0)) alone does not absorb an extra logarithmic square. The particular later application appears to have a polynomial margin and could absorb it, but the standalone stated proof has not done so. I do not assert a counterexample to the comparison theorem itself; I reject the supplied proof as complete.

### 4. Clipped components do not have bounded total contribution

`lem:lalley-comparison`, lines 5050–5053, says the total contribution of O(|boundary H|) clipped intersections is O(|boundary H|). A single clipped graph component can contain arbitrarily many vertices of H and hence arbitrarily many forced internal ascents. For example, let G be the entire path and H a long strict subinterval: there is one clipped component with a linear number of ascents.

The intended expectation lower bound may be repaired by retaining every forced internal ascent and discarding only boundary comparison edges adjacent to clipped components. There are O(|boundary H|) such comparison edges. The elementary inequality

    1/2 - 1/binomial(a+b,a) <= ((a-1)+(b-1))/6

for positive integers a,b is valid, including the small cases a+b=2,3,4. The exact count of graph-component intersections and what is discarded must be frozen precisely.

### 5. Fixed cell variation cannot be called o(1)

In `lem:type-estimates`, lines 3888–3926, a chi-regular cell controls the logarithmic difference between actual column probabilities and a representative by O(chi); see the definition at lines 278–304. Summing this over O(log N) columns yields an exponent error O(chi), not o_N(1) for fixed chi. The exact equality lambda_x=N^(-J_theta^chi+o(1)) therefore does not follow from the stated regularity. A valid statement needs an explicit error in terms of the maximum per-column log discrepancy, or a declared hierarchy in which chi tends to zero with N and all other estimates remain uniform. The safe finite version is the exact identity using actual column probabilities; cellwise representative approximations have explicit nonzero error bounds.

### 6. Endpoint notation and one-based indices

At lines 2949–2956, full row strings are compared with shorter prefixes using `<_lex` and `<=_lex` to define L_w,U_w. Ordinary lexicographic order on variable-length words does not mean comparison of their length-|w| prefixes. Freeze L_w as the number of rows whose truncation to |w| is less than w, and U_w as the number whose truncation is less than or equal to w.

Similarly, integer intersections with half-open product intervals naturally use positions 0,...,N-1, while row positions in the article are 1,...,N. A proof with bridge slack can tolerate a shift by one, but a finite Lean theorem cannot silently identify these conventions.

In `lem:uniform-endpoint-theorem`, lines 4160–4224, the left side-piece decomposition is valid. For the right endpoint, a formula using right side pieces must also include the fluctuation of the whole ambient count C(a_s), because U_x^rel=C(a_s)-sum(right side pieces). The final error bound can absorb this extra term, but the stated assertion that the proof is directly analogous omits it.

## Threshold and assumption audit

### Full words versus proper prefixes

`prop:largest-prefix`, lines 3377–3428, actually chooses a complete length-K_T word. This is correct. Equal complete rows are consecutive after lexicographic sorting and all adjacent pairs within that block are graph edges. Equal proper prefixes only give a contiguous union of potentially many components. They do not force an increasing run after sorting separately within components.

A finite counterexample to the improper-prefix claim is a matrix with four rows sharing a first digit and four distinct second digits. The prefix block has size four, but all complete words are distinct, so G has no edges and the component-sorted output is a uniform permutation. The event of an increasing run of length four is not forced.

The finite probability estimate must also say that column assignments are independent and uniformly distributed among assignments with their fixed counts. Marginal column counts alone do not determine a product probability: two perfectly coupled columns can have very different complete-word probabilities from the product of their marginal masses.

### Cold witness and bridge

The active witness identity at lines 3472–3483 is correct:

    (2 Gamma-h)-F_theta=(theta-3)(J_theta-beta(s)/2).

The witness selection in `lem:cold-witness`, lines 3583–3796, is substantially more than substitution of an integral into a homogeneous constant. It uses uniform positivity of F_alpha over alpha in [3,4], continuity/monotonicity in the tilt, endpoint cases theta=3 and theta=4, backward motion in the splitting time, and an all-tail bridge condition.

Do not add smoothness, positive lower bounds on all coordinates, or a global homogeneous tilt equation after freezing. Zero coordinates are permitted by the simplex model; entropy and logarithmic products must use a support convention. Integrability and measurability of the time profile must be made explicit if integrals are formalized.

The bridge displacement must preserve s<=u. The proof applies the window lemma, which can replace u1 by T-rho_b, without explicitly proving T-rho_b>=s. A smallness bound can be obtained from beta(s)-beta(T) and the uniform upper bound a<=log k; it must be established, not silently assumed. Likewise, a lower bound F>=eta/2 cannot survive a nonzero bridge loss merely by referring to an already exhausted eta/2 margin; retain a stricter intermediate margin before applying the bridge.

The all-tail good-column condition guarantees a bridge only after its exact scale and quantifiers are fixed. A single fixed regularity scale is not equivalent to freely choosing arbitrarily smaller rho after the witness.

The obsolete overview claims that |J-1/2|<=eta/10 and Xi>=eta are a sufficient condition for a definition that requires J<=1/2-eta (lines 2637–2651). This implication is false even at J=1/2. The active witness uses a different buffered condition and must not inherit the overview shortcut.

The obsolete overview also has an algebraic factor error at lines 2620–2632: its definitions give gamma-h/2=3/2+(theta-3)J/2-B_theta/2-B_2, whereas the displayed claimed equivalence writes -B_theta-B_2. Its near-critical Xi consequently also has the wrong B_theta coefficient. The active identity for 2 Gamma-h has the correct coefficients.

### Occupancy and the critical window

The homogeneous fixed-column proof in 2510.22783v1, Section 6.3, Lemma 6.12, especially (6.21)–(6.23) on printed pages 57–58 (derived-text lines 3570–3597), uses a uniformly negative complete-word occupancy exponent. This makes triple and quadruple terms smaller than pair terms. The active inhomogeneous witness supplies only an upper bound beta(s)-J_theta-J_2<=kappa0, which permits positive occupancy exponents. Therefore the old rare-word first/second-moment proof does not apply unchanged. The two-category critical-window argument is new mathematics and currently has the defects listed above.

The iid-row proof in 2103.05068v3, Section 6.1, printed page 39 (derived-text lines 2188–2199), uses pairwise negative correlation of occurrence indicators. That property must not be imported into the fixed-column model without proof. Fixed column sums introduce dependencies across words and rows.

### Uniform ascents and hypothesis tests

For a uniform permutation, indicators on a deterministic matching of positions are mutually independent Bernoulli(1/2). Pairwise independence by itself is not enough for a Hoeffding bound. A path-edge set splits into its even and odd matchings. There is no independence assertion between those two matching families.

The uniform bound `lem:uniform-ascent`, lines 4899–4949, can be a finite bound: for any deterministic finite family of path-edge sets, each with at most M edges, a union bound after the two matching estimates gives a factor equal to the family cardinality. The boundary hypothesis is not used when centering at |E(H)|/2. If centering at |H|/2, account explicitly for the number of components. The growth M>=N^a is used only to absorb the N+1 translate scan; it is not needed for a fixed finite test.

2510.22783v1, Lemmas 6.3 and 6.5, printed pages 52–53 (derived-text lines 3240–3281), display K<=(tilde C_mu-epsilon)log N even though that subsection assumes K>=(tilde C_mu+epsilon)log N. These are inconsistent thresholds, almost certainly transcription/statement errors in the source. The graph-based ascent comparison itself should not need that K threshold at all. Do not freeze either contradictory threshold simply because it is printed.

### Random pile sizes and mixture cancellation

Conditional lower bounds in total variation cannot be averaged. For a finite state space of size n, let Q be uniform and let P_x be the point mass at x. Every dTV(P_x,Q)=1-1/n, but the uniform mixture of P_x is exactly Q and has distance zero.

The legitimate homogeneous argument in 2510.22783v1, Lemmas 6.5–6.6, printed page 53, constructs one event A=union_x A_x. It requires conditional success uniformly over typical cuts and a sum of false-positive probabilities tending to zero. For fixed k and K=O(log N), the number of integer cut sequences is at most (N+1)^(kK), so exp(-N^c) uniform false-positive bounds suffice. Merely knowing each false-positive probability is o(1) does not suffice. If k grows with N or cut entries are not integers, that particular counting argument is unavailable.

The full-word increasing-run event is common to every cut sequence and avoids this test-counting issue: conditional success can be averaged for that same event. No independence among random pile sizes across time is needed if one conditions on the complete sequence and the conditional shuffle law is correctly specified.

## Recommended frozen finite core

Each item below is a finite theorem candidate, not a license to assume an unproved probabilistic statement.

1. **Finite distributions and tests.** On a finite state space, nonnegative masses sum to one; define TV by half the L1 difference. Prove the event test inequality P(A)-Q(A)<=TV(P,Q), TV bounds, and finite union bounds directly.
2. **Mixture test.** For nonnegative weights summing to one and events A_x, set A=union_x A_x. Prove P_mix(A)>=sum_x weight_x P_x(A_x) and Q(A)<=sum_x Q(A_x). A typical-subset version should keep its exact missing weight explicitly. This proves a random-pile lower-bound transfer without the false averaging claim.
3. **Actual time-dependent word mass.** Define lambda(w)=product_t p_t(w_t), with p_t a finite probability vector. Prove product identities and maximality of the word choosing a maximizing digit at each time. For cell profiles, use exact products for truly constant cell probabilities or freeze an explicit accumulated error bound.
4. **Stable equal-full-word obstruction.** Define a complete word for each labelled row and the stable ordering precisely. Prove that rows with the same complete word occupy a contiguous block and their labels appear increasingly. If a complete word occurs at least m times, the output has an increasing contiguous run of length m. A proper prefix is not enough.
5. **Uniform-permutation run probability.** For 1<=m<=N, prove that a fixed length-m interval is increasing with probability 1/m!, then the union bound (N-m+1)/m!. Specify a permutation as a bijection and the orientation of its action. N=0, m=0, and m>N must be handled or excluded before freezing.
6. **Exact first and second occupancy moments.** In independent uniform fixed-count columns, E Y=N product_t(n_t/N). For N>=2,

       E[Y(Y-1)] = N(N-1) product_t[n_t(n_t-1)/(N(N-1))] <= (E Y)^2.

   Therefore Var(Y)<=E Y. This provides a safe finite lower tail using Chebyshev, without invoking the full hypergeometric or cold-window machinery.
7. **Finite largest-word TV lower bound.** With the model and sorting theorem proved, 1<=m<=N and mu=E Y>m give

       TV >= 1 - mu/(mu-m)^2 - (N-m+1)/m!.

   This is a substantive finite shuffle lower bound. It uses a full-word occupancy event and the common increasing-run test. Random cuts can use the same test with exact averaged failure bounds or a typical-event bound on mu.
8. **Uniform ascent mean and matching independence.** Prove each ascent has expectation 1/2 and a deterministic matching's comparisons have the product Bernoulli law. This is enough infrastructure for future finite cold tests; it does not establish the actual cold-set construction or concentration of its collision count.
9. **Cold exponent algebra only.** Exact identities for h,Gamma,F and entropy balances are valid algebraic finite targets with every variable and assumption explicit. Label them as algebraic identities, not a cold-spot lower-bound theorem.

The finite test theorem may be parameterized by already-proved event probabilities, but the project must not present a wrapper accepting the desired lower-bound event as a hypothesis as though it had proved the shuffle obstruction. The full-word structural theorem and exact model moment calculation are the substantive bridge from shuffle dynamics to the finite test.

## Proposed uniform-permutation contract U, for pre-freeze review

These statements use the root's real-valued `FiniteLaw`, `prob`, `expect`, and `uniformLaw` definitions. Let `PermN := Equiv.Perm (Fin N)`. A permutation is interpreted as the value at a position. The uniform law exists also for N=0 because the permutation type is nonempty. All factorial ratios below are in the reals.

Definitions:

* `increasingAlong e sigma := StrictMono (fun i : Fin m => sigma (e i))`, where `e : Fin m ↪ Fin N` is any embedding, not necessarily order preserving. The order on the domain Fin m specifies the tested sequence.
* `increasingAlongEvent e` is the finite set of sigma with `increasingAlong e sigma`.
* `windowEmbedding N m a h : Fin m ↪ Fin N`, with h:a+m<=N, maps i to a+i.val.
* `windowEvent N m a h := increasingAlongEvent (windowEmbedding N m a h)`.
* `ascentEvent i j := {sigma | sigma i < sigma j}`.
* `ascentCount E sigma := sum_{(i,j) in E} (if sigma i < sigma j then (1:Real) else 0)`, for a finite set E of ordered pairs of positions.

Every exported helper is listed below. Auxiliary facts inside the proof of a listed theorem may be local `have` statements; no unlisted top-level theorem is proposed.

U01. For any injective f:Fin m→Fin N, there is exactly one tau:Perm(Fin m) such that `StrictMono (f ∘ tau)`. It is `Tuple.sort f`. No assumption m>0 is needed.

U02. For any embedding e and tau:Perm(Fin m), the number of sigma:PermN satisfying `StrictMono (fun i => sigma (e (tau i)))` equals the number satisfying `increasingAlong e sigma`. This is a finite reindexing bijection. The extension of tau from the image of e to all Fin N is internal to the proof, using trusted `Equiv.Perm.extendDomain`.

U03. For any embedding e,

    (increasingAlongEvent e).card * m.factorial = N.factorial.

No extra inequality m<=N is a hypothesis: it follows from the embedding. The cases m=0 and m=1 are included.

U04. For any embedding e,

    prob (uniformLaw PermN) (increasingAlongEvent e) = 1/(m.factorial:Real).

U05. For a+m<=N, membership in `windowEvent N m a h` is equivalent to the exact fixed-start run predicate used in `HasIncreasingRun`: all i,j with a<=i.val, j.val<a+m, and i<j satisfy sigma i<sigma j. In particular, for m<=N,

    {sigma | HasIncreasingRun sigma m}
      = union_{a in range(N-m+1)} windowEvent N m a (proof a+m<=N).

The proof arguments in this union are dependent and proof irrelevant; implementation may express the same union over `Fin (N-m+1)`.

U06. If m<=N, then

    prob (uniformLaw PermN) {sigma | HasIncreasingRun sigma m}
      <= (N-m+1:Nat)/(m.factorial:Real).

This statement includes m=0, when the right side is N+1 and remains a valid bound. The lower-bound endpoint separately requires 1<=m. There is no claim that the bound is at most one.

U07. If i,j:Fin N and i!=j, then `prob (uniformLaw PermN) (ascentEvent i j)=1/2`. No condition i<j is needed: their supplied order determines the comparison.

U08. For any finite set E of ordered pairs with i!=j for every (i,j) in E,

    expect (uniformLaw PermN) (ascentCount E) = E.card/2.

Different comparisons need not be independent, disjoint, adjacent, or consistently oriented. E may contain both (i,j) and (j,i); linearity still gives the stated answer. Matching independence and exponential tail estimates are not claimed in this contract.

Trusted API inspected without writing Lean: `Tuple.monotone_sort`, `Tuple.unique_monotone`, `Equiv.Perm.extendDomain` and its image-action lemma, `Fintype.card_perm`. These support a double-counting proof of U03: each sigma has exactly one increasing reordering of its m sampled values (U01), while each fixed reordering has equally many increasing sigma (U02).

## Review of root candidate P01–P14, L01–L02

I approve the mathematical content of P01–P14 and L01–L02 as written in `contract-candidate.md`, subject to the shared model definitions and all displayed assumptions being frozen exactly. In particular:

* P08 may permit arbitrary real epsilon and delta; its hypotheses imply the needed numerical inequalities directly.
* P09 and P10 need the displayed nonnegativity assumptions on epsilon and delta; they do not need those errors to be at most one. A proof should split trivial large-error cases or bound the failure event directly.
* P13 is valid for arbitrary real-valued f: expanding f(f-1) yields Var(f)<=E(f). There is no hidden nonnegative or integer-valued f assumption.
* P14 uses strict m<mu; changing this to m<=mu creates division-by-zero and must not be done. Its failure event is f<m, which is contained in the Chebyshev deviation event with threshold mu-m.
* The concrete model uses independent uniform random permutations of base columns; repeated representations of each multiset assignment all have the same multiplicity, so it gives the desired uniform fixed-column assignment law.
* L01 is a finite full-word obstruction with a proved moment bridge, not an assumed cutoff.
* L02 uses the same increasing-run event for all environments. It consequently survives mixture cancellation and does not need a union over all cut-specific tests. The random-cut law itself may have arbitrary temporal dependence.
* The stable sorting permutation must mean the list of original row labels in sorted-position order (`Tuple.sort`), not its inverse. This convention is already stated in the shared model and must be preserved.

## Independent review of M01–M15 and S/D/C contracts

Read the complete `moments-contract.md` and `sorting-profile-contract.md` before freeze. Mathematical approval: **M01–M15, S1–S4, D1a–D1b, D2–D4, C1, C2, C3a–C3b**, exactly as stated.

One declaration-name correction is required before implementation: both modules currently propose a different `RiffleLower.wordMass`. The fixed-column definition takes a column array and a word; the generic profile definition takes a time-indexed real array and a word. These cannot be separate declarations with the same fully qualified Lean name. Freeze distinct names (for example `profileWordMass` for the generic definition), or put the generic profile declarations in a separately frozen namespace. This changes no mathematical assumption or assertion, but must be explicit before freeze.

Detailed checks:

* M01/M02 use normalized uniform laws, so nonempty domain/coordinate types are necessary and explicitly present. The empty time index remains valid.
* M03 follows from permutation symmetry and needs no row independence. M04 correctly uses distinct positions and the ordered-pair factor d(d-1)/(N(N-1)); replacing it by (d/N)^2 would be false.
* M05 includes ordered distinct pairs, so there is no missing factor two. M06 supplies the finite count partition needed for M07.
* M08–M11 have the exact independent-column source and correct N versus N(N-1) factors. Full-word equality means equality at all K coordinates, including the legitimate empty-word case K=0.
* M12 is valid at d=0 and d=1 despite the real d-1 factor. For d>=1 it reduces to d<=N after positive-denominator manipulation. M13 preserves nonnegativity when multiplying. M14 also needs N(N-1)<=N^2, which is an elementary consequence of N>=2, not an additional assumption.
* M15 requires the strict mean gap already present. It does not assume a positive lower bound on any pile size.
* S1–S3 concern arbitrary linear-order keys and the stable sorting permutation, so they legitimately generalize full row words without changing the shuffle convention. S4 requires a nonempty run and full equality of keys; it does not infer a run from shared proper prefixes.
* D1 is exact finite partition counting. D2 allows arbitrary real factors, with natural exponents, including zero and negative factors. D3's explicit positivity is restricted to the selected factors and must not be propagated into M or D2/D4. D4 supplies a maximizing word; it does not assert its existence for an empty digit type.
* C1 is an identity with no hidden theta range or sign hypotheses. C2's localization premise is deterministic and explicit, and the first two positions of each repeated fiber supply distinct adjacent edges. C3a follows from stable ties; C3b is cardinality monotonicity. These statements do not imply the missing high-probability localization or cold collision count.

No further mathematical correction is requested. This approval does not authorize adding unlisted exported helpers after freeze.

## Post-freeze implementation verification

`RiffleLower/UniformPermutation.lean` implements U01–U08 exactly, with U05 split into the fixed-window predicate equivalence and the finite union over admissible starts. All declarations kernel-check. The module proves the stronger arbitrary-injection fixed-order probability 1/m!, the requested (N-m+1)/m! increasing-run bound, single-pair ascent probability 1/2, and exact ascent expectation for any finite set of distinct-endpoint comparisons. It does not claim matching independence or an exponential ascent tail.

Independently compared `RiffleLower/FiniteProbability.lean` against P01–P14 after implementation. Every definition and theorem matches the frozen contract. In particular, the TV test has the frozen half-L1 convention; mixture tests use one observable event or an explicit union; the large-delta branch in P09 is handled; the Chebyshev threshold is strictly positive; and the final lower tail preserves the strict gap m<mu. Neither P13 nor P14 silently assumes that the variable is nonnegative or integer-valued.

The diagnostic `review/probability-uniform-axioms.txt` records a successful per-declaration `#print axioms` run for all 57 declarations in the probability and uniform-permutation modules. All dependencies belong to the frozen trusted set `propext`, `Classical.choice`, `Quot.sound`. No custom axiom, `sorryAx`, or native evaluation oracle occurs. This audit does not change any mathematical source or assumption.
