# Independent mathematical reconstruction

Author role: reconstruction agent. This report was formed independently of the statement-design and counterexample reports. Mathematical sources read: only `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `2103.05068v3.pdf`, and `2510.22783v1.pdf` (PDFs through direct text extraction). No Lean code is supplied or changed here. Statements below are proposals for comparison and freezing, not a declaration that the freeze has already occurred.

## 1. Source relationship and scope

The finite stable-block construction is in article lines 446–458, 490–697, with partition theorems at 788–855. The needed positivity argument is spelled out later at 965–992. The closest predecessor is 2510.22783v1, Definition 4.3 (pp. 18–19), the paragraph defining stable blocks and Lemma 4.9 (p. 25). The homogeneous ancestor is 2103.05068v3, Lemmas 4.4–4.6 (pp. 20–21): a decreasing size-minus-fluctuation function defines a full stopping subtree, whose leaves partition the full words.

The current article materially improves totality over 2510.22783v1: it includes legal words, both terminal boundary fallbacks, terminal retained pairs, a terminal stable fallback, and an explicit singleton branch. These must be formalized from the current article, without importing a terminal exclusion from the older argument. The older Lemma 4.9 uses a tail-size assumption to force a crossing at every leaf. The new finite partition lemma does not need that assumption because it includes Λ.

## 2. Finite data and assumptions needed by the assigned result

Use the given finite deterministic shuffle data:

- Integers N, k, K, with N > 1 for the logarithmic formulation and k ≥ 2 as in article 88. K may be zero in the finite combinatorial theorem.
- Natural pile counts n(j,ℓ), for 1 ≤ j ≤ K and 0 ≤ ℓ < k, with sum over ℓ equal to N.
- A real χ with 0 < χ < 1/k, as in 523; a legal ambient prefix w, |w| ≤ K.
- The real ambient exponent b and a positive δ. The admissibility constant C is the article's fixed constant; its size is irrelevant to the set-partition proof.

The finite partition result requires no almost-profile condition, no good-column condition, no tail-size margin, no asymptotic error assumption, and no fluctuation-regularity hypothesis. All of those enter quantitative estimates later. In a generic finite stopping-tree helper, antitonicity of the score is a legitimate abstract premise, but the final article theorem must discharge it from the concrete pile-count formula; it must not become a new unproved project hypothesis.

The ambient r is irrelevant to the finite combinatorics. The assertion r ≤ s at 690 is only asymptotic under the article's convention |w|/log N = r+o(1); do not include that exact inequality in a frozen finite theorem without reconciling the time convention. Exact length inequalities |w| ≤ |join| ≤ |stable word| ≤ K are valid.

Zero pile counts are permitted. Restricting the tree to legal words is essential: it makes log(N/n) finite on every used coordinate, and it preserves positivity of cylinder probabilities. The tree need not be a full k-ary tree, but every legal prefix has at least one legal child until level K because each column sums to N > 0.

## 3. Required helper statements and reconstructed proofs

The labels below are proposed mathematical interfaces, not existing Lean declarations. Every helper has the same ambient finite data unless a more general statement is explicitly indicated.

### F0: finite word and cylinder foundations

1. **Prefix truncation and transitivity.** Prefix order is reflexive/transitive/antisymmetric; x ≤prefix y implies |x| ≤ |y|; equal lengths plus prefix imply equality. Prefixes of a common word are comparable. The parent of a nonempty word is its length-minus-one prefix. If x is a strict prefix of z, then x is a prefix of parent(z).
2. **Legality inheritance and extension.** Every prefix of a legal word is legal. Every legal word of length < K has a legal child, and every legal word extends to a legal full word of length K. Proof: choose a positive-count digit from the next normalized column; iterate finitely.
3. **Cylinders.** B_x = {ω legal of length K : x ≤prefix ω}. B_x is nonempty for legal x. If x ≤prefix y then B_y ⊆ B_x. Two legal cylinders intersect iff their prefixes are comparable; in that case their intersection is the cylinder of the longer prefix. Incomparable prefixes have disjoint cylinders.
4. **Lexicographic convexity.** Each B_x is order-convex in the lexicographic order on legal full words. Proof: if a,c share prefix x and a ≤lex b ≤lex c, a first coordinate below or above x in b would force b below a or above c. Thus b also shares x. Consequently, for any nondecreasing list of legal full rows, the inverse image I(B_x) is an order-convex subset of row indices, hence an interval, possibly empty.
5. **Partition transport.** Any pairwise disjoint cylinder cover of B_v pulls back under any row assignment to a pairwise disjoint cover of I(B_v). Sortedness is needed for interval convexity, not for disjointness or coverage. This yields the random-interval statement samplewise, before any probability is used.

Sources: article 446–458, 803–825; 2103.05068v3 Lemma 4.6.

### F1: large-pile thresholds

6. **Threshold existence and positivity.** For every column j there exists ℓ with n(j,ℓ)/N ≥ χ. Otherwise all k masses are < χ and their sum is < kχ < 1. Thus the finite minimum L_j and maximum R_j in article 525–527 exist. They satisfy L_j ≤ R_j, n(j,L_j) ≥ χN > 0 and n(j,R_j) ≥ χN > 0. Digits ℓ < L_j and ℓ > R_j have mass < χ.

No good-column assumption is needed: L_j and R_j are allowed to coincide.

### F2: left/right boundary families and admissibility

7. **Boundary family characterization.** A legal extension y of w is left-boundary iff either its last coordinate is the first index j > |w| with y[j] > L_j, or it is a full word and has no such crossing. The right version replaces > L_j by < R_j. The displayed definitions include genuine crossings at j = K as well as no-crossing terminal words.
8. **Boundary stop exists for every full word.** For ω ∈ B_w, take the least crossing index j in (|w|,K], if one exists, and return ω restricted to j; otherwise return ω. That word is in the left family and is a prefix of ω. The construction is identical on the right.
9. **Boundary antichain.** If two members of the left family are comparable, they are equal. If the shorter one is terminal, equal length K forces equality. Otherwise it crosses at its final coordinate; a strictly longer left-family member would have to have no crossing at that same earlier coordinate, contradiction. The same proof works on the right.
10. **Unique boundary prefix and minimality.** Combining existence with the antichain proves that each full ω has exactly one left-family prefix and one right-family prefix. Thus the article's word “shortest” actually selects the unique family member. Every coordinate strictly before the selected genuine crossing satisfies the noncrossing inequality. A selected boundary word of length < K necessarily comes from the genuine-crossing branch. A selected boundary word of length K may or may not have a genuine crossing.
11. **Admissibility is a predicate on the selected boundary prefix.** Left bad-count counts j ∈ (|w|,|y|] with y[j] < L_j; right bad-count counts j with z[j] > R_j. The last crossing digit does not add a bad count on its own side. The truncation is exactly bad-count ≤ C log N / log(1/χ), with the natural count coerced to real. Admissible-family membership implies boundary-family membership; each admissible family remains an antichain. No theorem identifying < and ≤ variants should be imported from the older PDF: the current source uses ≤.

Sources: article 523–593; 2510.22783v1 Definition 4.3. The older PDF has apparent endpoint/index typographical inconsistencies, so it cannot override the current formulas.

### F3: compatible pairs, joins, and boundary fibers

12. **Pair compatibility.** For y in the left family and z in the right family, A_yz = {x legal : w ≤prefix x, y ≤prefix x, z ≤prefix x} is nonempty iff y and z are comparable. Forward: prefixes of a common x are comparable. Backward: the longer of y,z is itself in A_yz. (Admissibility is unnecessary for this helper.)
13. **Join and descendant identity.** For a compatible pair define v = y∨z to be the longer word, with either choice on a tie, since comparable equal-length words are equal. Then v is legal, w ≤prefix v, and A_yz = {x legal : v ≤prefix x}. In particular y,z ≤prefix v, |v| = max(|y|,|z|), and if the pair is terminal then |v| = K and B_v = {v} as a full-word set.
14. **Boundary fiber is exactly the join cylinder.** For compatible y,z in the boundary families,

   {ω ∈ B_w : L(ω)=y and R(ω)=z} = B_(y∨z).

   Forward: both words are prefixes of ω. Reverse: y,z are boundary-family prefixes of any ω extending the join, so uniqueness of the boundary stops identifies them. Incompatible pairs have empty fibers.
15. **Distinct boundary-pair cylinders are disjoint.** If two compatible pairs have intersecting join cylinders, a word in the intersection has both pairs as its unique boundary pair, so the pairs are equal. Consequently joins of distinct compatible boundary pairs are themselves incomparable. This is stronger and safer than assuming different joins are automatically disjoint.

Sources: article 595–603, 828–855. The fiber-to-cylinder identity is used by the source but deserves its own explicit lemma.

### F4: fluctuation pieces and retention

16. **Side-piece antichain.** P_(x,i) and Q_(x,i) are families of legal words all of length |x|, so they are prefix antichains. Therefore the interval convention in 455–457 applies.
17. **Side-piece cylinder characterization.** For |w| < i ≤ |x|,

   B_(P_(x,i)) = {ω ∈ B_w : ω[j]=x[j] for |w|<j<i, and ω[i]<x[i]},

   and the corresponding equality holds with > for Q. Given a full ω satisfying the right side, its prefix of length |x| supplies the witnessing element of P; the reverse direction is immediate.
18. **First-disagreement decomposition.** Among full words in B_w, the words whose length-|x| prefixes are lexicographically < x form the disjoint union of the P side cylinders over |w|<i≤|x|. The first differing coordinate is the unique piece index. There is an identical right decomposition. Each side cylinder is convex because it fixes earlier digits and allows a lower (or upper) interval of the digit order at the first difference.
19. **Continuation independence.** If v ≤prefix x and i ≤ |v|, the full-cylinder unions B_(P_(x,i)) and B_(P_(v,i)) are equal, and likewise for Q. Hence their row-count random variables are exactly equal, and so are their expectations. Since every fluctuation maximum uses exactly |w|<i≤|v| in the current article, both fluctuation quantities and c_F are exactly constant over A_yz. This is not merely an asymptotic statement. Beware: the piece sets themselves have different word lengths and generally are not equal; their full-cylinder unions are equal.
20. **Expected cylinder positivity / finite size.** A legal word has positive probability in a fixed labelled row, equal to the product of its positive column masses; hence its expected number of rows is N times that product, strictly positive and at most N. The same formula and summation give expected side-piece counts. This is the probability-model bridge needed to prove retention without adding it as a hypothesis.
21. **Positive fluctuations for a compatible nonterminal pair.** Here |y|,|z|<K, so both are genuine crossings. At i=|y|, the legal threshold digit L_i is strictly below y[i] and has mass ≥χ. Replacing only this coordinate in any full continuation produces a legal word in the left side cylinder. Therefore the left piece expectation is positive. The right proof uses i=|z| and R_i. Both indices occur in the common cutoff (|w|,|v|], so both finite maxima are positive; both square roots and base-N logarithms are finite. Thus c_F(v;y,z)>−∞. A quantitative version already in article 965–992 is

   E|I(P_(ξ,|y|))| ≥ χ E|I(B_ξ)| > 0,

   and likewise for Q. Exact positivity suffices for this assigned task.
22. **All compatible pairs are retained.** A terminal compatible pair is retained by the terminal clause, even when one fluctuation maximum is zero. A nonterminal compatible pair is retained by statement 21. Therefore among admissible boundary pairs, the retained ones are exactly the compatible ones. This is the missing explicit step in the article's proof of its final coverage assertion.

Sources: article 603–659, 965–992; 2510.22783v1 pp. 18–19, especially (4.2)–(4.5). The current article uses the common cutoff |y∨z| for both maxima, unlike the older PDF's separate |y| and |z| cutoffs. Preserve the current definition.

### F5: concrete score monotonicity

23. **Pile costs are nonnegative.** Legal n(j,x[j]) lies in [1,N], so N/n ≥1 and log(N/n)≥0. With log N >0, every normalized cost is nonnegative.
24. **Size exponent is antitone.** If w ≤prefix x ≤prefix z are legal, splitting the finite sum yields

   c_L(z) = c_L(x) − (1/log N) Σ_(|x|<j≤|z|) log(N/n(j,z[j])) ≤ c_L(x).

25. **Fixed pair score is antitone.** For a compatible nonterminal pair c_F(v;y,z) is a finite real by 21. The real score d(x)=c_L(x)−c_F(v;y,z) is antitone on descendants of v. No asymptotic fluctuation comparison is needed here.

Sources: article 503–507, 640–643, 803–806. The finite-real representation in the active stopping branch avoids undefined arithmetic with −∞.

### F6: stable descendants and stable partition

26. **Terminal branch.** If either boundary word has length K, v has length K and the stable family is exactly {v}. This must take priority over tests involving c_F; it handles the possible value −∞ and K=|w|, including K=0,w=empty.
27. **Immediate singleton branch.** If the pair is nonterminal and d(v)<δ, the stable family is exactly {v}; this gives a disjoint cylinder cover directly.
28. **First-crossing existence/minimality.** Suppose the pair is nonterminal and d(v)≥δ. For ω∈B_v, inspect the finite nonempty path of prefixes at lengths |v|,…,K. If any has score <δ, choose the least such length m. Because d(v)≥δ, m>|v|; the selected prefix x has d(x)<δ and its parent still has score ≥δ, so x∈Γ. This includes m=K. Every earlier path prefix has score ≥δ. If none has score <δ, ω itself has d(ω)≥δ and belongs to Λ.
29. **Γ cannot contain the join in the active branch.** Its strict below-threshold condition contradicts d(v)≥δ. Thus for every active-branch Γ element, its parent remains a descendant of v and all expressions used in the parent condition are in their intended domain.
30. **Γ∪Λ is an antichain.** If x∈Γ and x is a strict prefix of z, then x≤prefix parent(z), so d(parent(z))≤d(x)<δ, excluding z∈Γ. Also d(z)≤d(x)<δ excludes z∈Λ. If x∈Λ and x≤prefix z, |x|=K and |z|≤K force equality. These two arguments cover every orientation; Γ and Λ themselves are disjoint because of the <δ versus ≥δ conditions at level K.
31. **Unique stable prefix.** In either singleton branch this is immediate. In the active branch existence is 28 and uniqueness follows from 30 because two prefixes of the same full word are comparable.
32. **Stable partition.** For a retained pair, every stable prefix extends v, and every full word in B_v has a unique stable prefix. Therefore the stable cylinders have union B_v and are pairwise disjoint. By F0.5 their row-index sets have union I(B_v) and are pairwise disjoint, and by F0.4 each is an interval.

Sources: article 661–696 and 788–826. The source proof's phrase “Λ elements have no crossing before terminal time” is a consequence of antitonicity and d(leaf)≥δ, not an extra defining condition.

### F7: global boundary decomposition

33. **Untruncated global partition.** Every ω∈B_w has a unique boundary pair (F2.10). Its pair is compatible because both words are prefixes of ω. Pair fibers are exactly the join cylinders (F3.14), which are disjoint (F3.15), so the untruncated boundary-pair fibers partition B_w.
34. **Admissible stable coverage iff admissible boundary stops.** A full word ω∈B_w belongs to some stable cylinder of an admissible retained pair iff L(ω) and R(ω) are both admissible. The forward implication uses the pair-fiber identity. For the reverse implication, the selected pair is compatible, hence retained by F4.22, and F6.32 supplies the unique stable prefix.
35. **Global disjointness and intervals.** Stable cylinders belonging to different boundary pairs lie in disjoint pair fibers. Stable cylinders within one pair are disjoint by F6.32. Thus the entire retained admissible stable collection is an antichain and a disjoint cover of exactly the retained admissible full words. Their inverse images under the sorted row map are disjoint convex intervals. The omitted strings are exactly those excluded by at least one admissibility predicate, not an unspecified extra exceptional class.

Sources: article 828–855. This final equivalence is stronger than merely proving that every represented string is admissible; both directions are needed for the phrase “the only strings not represented.”

## 4. Explicit edge cases and freeze cautions

- A terminal boundary pair is a pair with either boundary length K; it is not synonymous with “a pair without a genuine crossing.” Genuine crossings at time K are terminal too.
- A singleton stable family need not equal {join}: a legal tree can have unary continuation, and Γ∪Λ may then contain just one proper descendant. Preserve the source's later literal test `stableFamily ≠ {join}`. Do not replace it by `card stableFamily ≠ 1`.
- Equality at threshold δ belongs to the no-crossing/continue side. Γ uses < at x and ≥ at its parent; Λ uses ≥ at the leaf.
- The parent operation needs an explicit total convention (e.g. parent(empty)=empty) or a well-typed nonempty domain. Γ is only semantically used on nonempty words in the active branch, but its displayed definition is global. Do not fix this by assuming K>0 or w nonempty.
- A terminal singleton with zero fluctuations must remain retained; the −∞ logarithm convention is real mathematical data, not the behavior of ordinary Lean `Real.log 0`.
- The maxima over no indices are zero. This occurs for terminal ambient w with |w|=K. Both boundary stops then equal w and the stable family is {w}.
- Do not assert every sampled cylinder interval is nonempty. A legal cylinder has positive expectation, but a realization can contain zero matching rows. Interval partitions can contain empty pieces unless empty intervals are removed explicitly.
- Different prefix lengths in P_(x,i) prevent equality of the prefix sets across continuations; only full-cylinder unions, row counts, and expectations are equal.
- Do not replace the legal tree by a full k-ary tree when some piles vanish. Extension existence is enough for the argument.
- The article has only asymptotic identification of b with log_N expected ambient size, so no exact equality between c_L(x) and log_N E|I(B_x)| should be silently frozen. Exact antitonicity of the displayed c_L formula remains valid.
- The old fixed-column PDF excludes coordinate 1 in fluctuation maxima because its column counts are fixed. The current article includes every coordinate after w, including |w|+1. This is not an obstacle to the assigned finite partition theorem, but quantitative fluctuation/anti-concentration claims later must be audited against that changed definition rather than assumed from the old result.

## 5. Whole-proof dependency skeleton

The following is a structural map of the complete article; it is not a claim that every analytic sketch is already a complete proof.

### Upper bound

1. Common setup (88–170): normalized piles and one-column costs → integrated A, Bθ, Jθ → global β and Λ0,…,Λ3 (176–233), profile-like cuts, regular partitions, and local good columns (249–313).
2. Ambient sizes and FM/RFM (318–373) are the hypotheses for the deterministic upper theorem (377–384).
3. Shuffle matrix/graph representation (388–407) → graph densities; local sparsity (424–427) → sparse factorial bound (429–438); graph density → truncated χ² bound (410–422).
4. **Assigned finite decomposition** (446–855): legal tree, boundaries, admissibility, joins, side pieces, score, stable stopping → stable and global cylinder/interval partitions.
5. Regular partition and interval blocking (857–896) + profile definitions (699–747) + concrete pile costs and side pieces → profile estimates (898–1037), including finite-positive fluctuations and entropy bounds.
6. Boundary/profile definitions + rare-small-pile factors + entropy counting → bad-profile reduction (1039–1119).
7. One-step hypergeometric estimates (1121–1152) + boundary crossing geometry → ambient conditioning transfer (1154–1200); both + profile/side decomposition → ambient concentration and anti-concentration (1202–1434).
8. Global/stable partitions + concentration + profile truncation → per-edge stable localization (1436–1484).
9. Concentration/anti-concentration + collision probabilities + stable threshold relations → edge-density bounds (1486–1638). Terminal pairs are routed separately through terminal singleton bound (1640–1660).
10. FM + profile entropy/cost bounds + stable parent condition + terminal/fallback cases → numerical lemma (1662–1815). Here the tail-size margin eliminates nonterminal Λ fallbacks; it is not an input to the finite partition theorem.
11. Bad-profile reduction + per-edge localization + edge-density bounds + numerical lemma + terminal singleton bound → first moment (1817–1914).
12. Conditional preservation (1923–1929) + RFM + first moment + small-block bounds → conditional first moment during exploration (1931–1943).
13. Conditional first moment → directional Portenko exponential moment (1949–1959) → shared-edge exponential moment by 2k-direction coverage (1961–1972).
14. Prefix concentration/stable estimates → regularity and sparsity (1974–1983). Together with shared-edge exponential moment, sparse factorial bound, and truncated χ² → deterministic TV upper bound (1985–1997).
15. Global negative margins → buffered pointwise upper bound (2029–2157), using monotonicity in accessible b and additivity of integrated costs. Margin monotonicity (2159–2289) → four-margin critical upper bound (2291–2321).
16. Basic one-column inequality (2349–2395) → dominance reduction Λ2,Λ3≤Λ0 (2397–2469) → buffered reduced consequence (2471 onward) → reduced critical-time theorem (235–247).

### Lower bound

The overview at 2564–2747 is superseded in detail by the proof at 2788–5206. The detailed lower proof imports only graph representation, regular partition/interval blocking/profile bookkeeping, and one-step hypergeometric estimates; see explicit imports U1–U5 at 2844–2895. Dominance is explanatory, not a lower-bound conclusion.

1. Labelled-row thinning (2915–3016) + one-column estimates → successive-thinning lower tail (3018–3167) → iterated hypergeometric prefix-tree concentration (3169–3373).
2. Λ0 positive + maximal-pile prefix + regular-cell cost estimates + iterated concentration → a polynomially long equal-string block → increasing-run test, whose uniform probability is ≤N/m! → largest-prefix lower bound (3377–3428).
3. Entropy inequalities (3498–3538) + profile integrals + bridge window from local goodness (3540–3581) → buffered cold witness from Λ1 (3583–3798). The witness supplies s,u,θ and gaps comparing cold interval size, fluctuation, collision count, and the near-critical mean.
4. Truncated tilted prefix definition (3847–3883) + regular-cell estimates/Stirling → type estimates (3885–3926) → relative cold-set geometry (3928–4002).
5. Two good bridge columns and fixed bridge words (4004 onward) + full collision-likely strings (4080–4093) → tail type estimates (4095–4121).
6. Side-prefix decomposition + iterated prefix concentration → relative endpoint theorem (4123–4224) → cold-prefix endpoint control (4226–4240). Cold witness + bridge masses → bridge buffers (4242–4280). Endpoint control + realized bridge-buffer concentration + deterministic lexicographic squeezing → localization (4282–4336).
7. Exact fixed-column sampling identities → fixed-column factorial moments (4340–4398) → conditional factorial moments (4400–4452) → central-window factorial comparison (4454–4534) → two-category Poisson bound (4536–4736).
8. Two-category Poisson + prefix/tail types + bridge factor + cold witness → fixed-column occupancy approximation (4738–4830) → cold collision count (4832–4864). Localization + distinct constant-string blocks → many cold edges (4866–4895).
9. Uniform permutation ascent concentration → uniform translate-scan ascent bound (4899–4949). Block value-set bounded differences (4951–4977) → component-value bounded differences (4979–5024) → Lalley component comparison (5026–5113). Together with graph representation, these imply the Lalley cold-spot test (5115–5163).
10. Cold witness + cold geometry + many edges + Lalley test → cold-spot lower bound (5167–5192). If max(Λ0,Λ1)≥η, split at κ0: largest-prefix if Λ0≥κ0, cold-spot otherwise → buffered reduced lower theorem (2812–2823, completed 5197–5206).

### Random pile-size extension

- Upper: randomized-profile-likeness definition (265–274) + local-goodness with probability 1−o(1) + **uniform** deterministic upper bound → mixture TV convergence (1999–2011). Quantitative elementary inequality: TV(E[P_X],U) ≤ P(atypical X)+sup_typical TV(P_x,U). The deterministic estimate must be uniform over typical realizations.
- Lower: conditioning alone cannot give a mixture lower bound because the distinguishing events can depend on the cuts. Use one common event: the union of the deterministic tests over every typical cut sequence (article 2737–2747; 2510.22783v1 §6.2, Lemmas 6.5–6.6, p. 53). There are at most (N+1)^(kK)=exp(O((log N)^2)) count sequences when K=O(log N). The deterministic tests have uniform false-positive bounds exp(−N^c), so their union still has vanishing uniform probability. Typical shuffled realizations accept their own test with probability 1−o(1), uniformly; the mixture therefore accepts the union with probability 1−o(1).
- For the largest-prefix branch the same increasing-run event can be shared already. For the cold branch the translated scan event additionally scans q∈{0,…,N}; this polynomial factor is absorbed in exp(−N^c). Preserve uniformity of the buffered exponents a,δ over typical cuts.

## 6. Foundational Lean module boundaries indicated by this proof

Before the assigned module can connect to the full shuffle proof, the project needs proved modules for:

1. finite alphabet words, prefix order, truncation, parent, lexicographic order and convex prefix cylinders;
2. deterministic pile data, normalized masses, legality, positive-column witnesses, and legal full extensions;
3. finite row assignments and sorted row index intervals, with deterministic partition transport;
4. fixed-column random shuffle matrix and independence of columns, including the exact one-labelled-row product law and expected cylinder/side counts;
5. finite products/sums, real logarithmic costs and antitonic size exponents;
6. bottom-valued logarithmic fluctuation convention or an equivalent finite/zero tagged representation, with exact continuation invariance;
7. finite first-hit stopping on a prefix tree, including terminal fallback and antichain/unique-prefix partition theorem.

For the remainder of the whole proof one additionally needs graph/component sorting and its density, finite total variation and mixture inequalities, hypergeometric concentration/conditioning, asymptotic uniformity and exponent bookkeeping, profile integration and Riemann-sum transfer, entropy/type counting, factorial-moment occupancy approximation, and permutation/ascent concentration. These are dependencies to prove or import from trusted mathlib, not assumptions to insert into the assigned final theorem silently.

The finite stable/global partition theorem can be finished independently of those later analytic modules once its concrete finite weights and logarithmic score are connected to proved foundations. Any generic stopping-tree theorem should be clearly identified as an auxiliary abstraction, with the article's actual boundary/weight construction instantiated and proved afterward.
