# Stable-block formalization contract — revision 1

Status: FROZEN after independent mathematical, representation, and adversarial reviews and comparison. No project Lean code existed at the time of this freeze. This document is immutable.

Mathematical sources: only time_inhomogeneous_riffle_shuffle_unified_article.tex, 2103.05068v3.pdf, and 2510.22783v1.pdf. The current article's definitions take precedence where it deliberately differs from the older papers. Operational instructions and trusted Lean/mathlib implementation dependencies are not additional mathematical sources.

## Scope and immutable source assumptions

The assigned deliverable is the exact finite stable-block decomposition, not an analytic cutoff theorem. Upper, lower, and random-pile proof dependencies are mapped separately; no sketched estimate is an imported theorem.

A pile model D consists of natural N,K,k and total natural counts n(i,a), with 1<N, 2≤k, and sum(a<k)n(i,a)=N for each i<K. There is no condition on unused i≥K or a≥k. The explicit 1<N records the domain of the source's asymptotic base-N logarithms. K=0 is allowed. Zero piles and probability-one columns are allowed.

Additional parameters are a legal ambient word w; arbitrary real b; 0<χ<1/k; real C>0 (the source's large constant); and δ>0. No exact equation between b and ambient expected mass is imposed. No FM, RFM, tail-crossing, goodness, fluctuation-regularity, profile, homogeneity, uniform positive pile, or nonempty sampled interval assumption is allowed in the assigned conclusions.

A theorem may quantify only the parameters it actually uses. Generic deterministic helper statements may quantify an arbitrary predicate or row map and state its mathematical properties explicitly; the concrete model must prove those properties before applying the helper. Such properties are never new hypotheses of the final source theorems.

## Frozen definitions (zero-based positions)

D01. Word is List ℕ. digit(x,i)=(x[i]?).getD(0). Only bounded-index theorems i<length(x) use its value. Prefix is List.IsPrefix. parent(x)=take(length(x)-1,x), so parent([])=[]. join(y,z)=y if length(z)≤length(y), otherwise z. The equal-length compatible case has y=z.

D02. Legal(D,x) means length(x)≤K and, for each i<length(x), digit(x,i)<k and 0<n(i,digit(x,i)). Full(D,x) means Legal(D,x) and length(x)=K. Desc(w,x) means Legal(D,x) and w prefixes x. B(x)={ω | Full(D,ω) and x prefixes ω}. FamilyCylinder(U)=union(x∈U) B(x). These sets contain only legal full strings.

D03. Ω=(Fin K→Fin k), fullList(ω)=List.ofFn(i↦value(ω i)). p(i,a)=n(i,a)/N as a nonnegative real. weight(ω)=product(i:Fin K)p(i,value(ω i)). ExpectedCount(E)=N*sum(ω:Ω)(if fullList(ω)∈E then weight(ω) else 0), a nonnegative real. This is the finite one-row marginal mass used in the source. It does not assume independent rows. A probability-space theorem identifying it with an integral over random fixed-column matrices is a separately listed future foundation, not an unproved input of this assignment.

D04. Large(i)={a<k | χ≤p(i,a)}. Left(i) is its minimum and Right(i) its maximum; the total definition uses 0 on an empty set, and the theorem proves this fallback is never used for i<K.

D05. For side ε∈{left,right}, Cross(ε,x,i) means Left(i)<digit(x,i) on the left and digit(x,i)<Right(i) on the right. Boundary(ε,x) means Desc(w,x) and either (length(w)<length(x), Cross at length(x)-1, and no Cross at w.length≤i<length(x)-1) or (length(x)=K and no Cross at w.length≤i<K). A first crossing exactly at K is included. The selected boundary prefix Select(ε,ω) is take(m,ω), with m the least i+1 for crossing at i∈[w.length,K), or K if there is none. Define it totally for all words; correctness statements concern ω∈B(w).

D06. Violations(left,x)=#{i∈[w.length,length(x)) | digit(x,i)<Left(i)}; Violations(right,x)=#{i in that range | Right(i)<digit(x,i)}. Admissible(ε,x) means Boundary(ε,x) and (Violations(ε,x):ℝ)≤C/log(1/χ)*log N. Keep ≤ exactly.

D07. A(y,z)={x | Desc(w,x), y prefixes x, z prefixes x}. Compatible(y,z) means A(y,z) is nonempty. RawPair(y,z) means Boundary(left,y), Boundary(right,z), and Compatible(y,z). AdmissiblePair adds both admissibility predicates. The definitions are total on arbitrary words but source claims only concern boundary pairs. v=join(y,z). Terminal(y,z) means length(y)=K or length(z)=K.

D08. For w.length≤i<length(x), P(x,i)={σ | Desc(w,σ), length(σ)=length(x), take(i,σ)=take(i,x), digit(σ,i)<digit(x,i)}. Q reverses the final inequality. The full-prefix equality before i agrees with the source's post-ambient equality since x,σ extend w. Later digits are unrestricted. Define Piece(ε,x,i) accordingly. PieceEvent is FamilyCylinder(Piece).

D09. For v prefix x, SideMaximum(ε,v,x)=max_{w.length≤i<length(v)} ExpectedCount(PieceEvent(ε,x,i)), with empty maximum 0 (finite supremum in nonnegative reals). SideFluctuation=sqrt(SideMaximum), a real. ExtendedLog(q)=bottom if q=0, otherwise (log q/log N):WithBot ℝ. cFAt(v,x)=min(ExtendedLog(left fluctuation),ExtendedLog(right fluctuation)). cF(y,z)=cFAt(v,v). Both maxima use length(v), as in the current article.

D10. Retained(y,z) means Compatible(y,z) and (Terminal(y,z) or cF(y,z)≠bottom). This extends the source expression to raw pairs for reusable lemmas; the final truncated decomposition uses AdmissiblePair.

D11. cL(x)=b-(sum_{w.length≤i<length(x)} log(N/n(i,digit(x,i))))/log N. This exact finite formula is defined for all words to make Lean functions total. Values outside legal ambient extensions, and parent values outside that domain, carry no source theorem. In every operative nonterminal Gamma use, parent legality and ambient extension must be derived.

D12. Stop(y,z,x) means (cL(x):WithBot ℝ)<cF(y,z)+(δ:WithBot ℝ). On finite cF=f this is exactly cL(x)-f<δ; on bottom it is false. Gamma(y,z)={x∈A(y,z) | Stop(x) and not Stop(parent x)}. Lambda(y,z)={x∈A(y,z) | length(x)=K and not Stop(x)}. Stable(y,z) is {v} if Terminal, otherwise {v} if Stop(v), otherwise Gamma∪Lambda. The order of cases is fixed; no bottom-to-real substitution is allowed.

D13. PrefixAntichain(U) means whenever x,y∈U and x prefixes y, x=y. Partition here means indexed pairwise disjoint sets whose union equals the claimed set; empty sampled pieces are permitted. Lexicographic order is ordinary List lex order: weak order is equality or List.Lex (<), never List.Lex (≤). For a row map rows:Fin M→Word, I(E)={i | rows(i)∈E}. All rows must be Full when speaking of sampled intervals; sorted means nondecreasing in lex order. No requirement that each legal word be observed.

D14. GenericCut(root,Q) is exactly {root} if Q(root) or root.length=K; otherwise it consists of legal descendants x with (Q(x) and not Q(parent x)) or (x.length=K and not Q(x)). Its hypotheses are a legal root and persistence Q(x)⇒Q(y) whenever legal root-descendants x prefix y. Generic first-digit boundary cuts use an arbitrary fixed relation on (position,digit), hence prefix-local, and exactly D05's first-crossing/fallback clauses. Concrete predicates are instantiated only after proving these hypotheses.

## Frozen theorem catalog

Each numbered entry is a universally quantified statement/schema with the indicated domains. Specialized left/right versions and definitional projections are instances of the same entry. Implementation proofs may use local facts and trusted library theorems; an additional mathematical statement outside this catalog requires independent review before implementation and must not change this frozen contract.

### W — words, support, and intervals

W01. Prefix reflexivity, transitivity, antisymmetry, length monotonicity; equal-length prefixes are equal; bounded digits of a prefix equal those of its extension; prefix iff corresponding take equals it. take has length min(m,len), take(len)=self, nested take uses min; bounded digit(take m x,i)=digit(x,i). Two prefixes of a common word are comparable, and if the first is no longer it prefixes the second.
W02. Legal words are prefix closed. Every column i<K has a positive legal digit. A legal nonleaf can be extended by exactly any a<k with n(i,a)>0. Every legal word extends to a full legal word. For legal x, parent is a prefix, has length len−1, and is legal; if v strictly prefixes x then v prefixes parent(x).
W03. B(x) nonempty iff Legal(x). Prefix gives reverse cylinder inclusion. Compatible legal prefixes' cylinder intersection equals the join cylinder; incomparable prefixes have disjoint cylinders. Full-leaf cylinder is {leaf}. An antichain gives pairwise disjoint cylinders.
W04. A(y,z) nonempty iff y,z are comparable, when both are legal ambient extensions. For compatible legal ambient y,z, join is legal, extends w, has length max(len y,len z), and A(y,z)=Desc(v). Terminal iff len(v)=K. Each component prefixes the join.
W05. fullList is injective, has length K and digits<k; every length-K bounded-digit list has a unique representing ω∈Ω. In particular every legal full list has a representing ω.
W06. A prefix cylinder is lexicographically convex among full legal strings. If equal-length prefixes x<lex y, every full extension of x is before every full extension of y. Truncation preserves weak lex order on full strings. Under legal sorted rows each cylinder's inverse image is order-convex. Inverse images preserve union equality and pairwise disjointness, with empty sets allowed.

### B — boundary stops and admissibility

B01. For i<K and a<k: n(i,a)≤N, 0≤p≤1, p>0 iff n>0, sum(a<k)p=1. Large(i) is nonempty under 0<χ<1/k. Left and Right belong to Large, have positive counts, are bounded digits, and Left≤Right. Digits below Left or above Right have p<χ.
B02. Boundary elements are legal ambient extensions. Every nonterminal boundary member has length>w.length and a genuine last crossing, with all previous post-ambient digits noncrossing. The two terminal/crossing clauses cover all possibilities including K=w.length.
B03. Each raw boundary family is a prefix antichain. Its admissible subfamily is a prefix antichain and subset of the raw family. Admissibility and violation-count definitions retain their exact non-strict cutoff.
B04. For each ω∈B(w), there exists exactly one prefix in each boundary family. It is Select(ε,ω); its length is the first crossing length if any, otherwise K. More precisely for any crossing at i, the selected crossing index is ≤i, every earlier post-ambient index does not cross, and when no crossing exists Select=ω. For every crossing index mentioned above require w.length≤i<K. For every boundary x, Select(ε,ω)=x iff ω∈B(x), for ω∈B(w).
B05. For each raw compatible pair, {ω∈B(w) | Select(left,ω)=y and Select(right,ω)=z}=B(v). Incompatible fibers are empty. Distinct raw compatible pair fibers (equivalently join cylinders) are disjoint. All raw fibers cover B(w). Comparable joins of raw pairs force equality of the respective components, using B03.

### F — exact side pieces and retention

F01. Weights and expected counts are nonnegative. For a full legal word, its representing ω has positive weight. A legal full word in E implies ExpectedCount(E)>0. Equal events have equal expected counts. The finite row weights sum to 1, so ExpectedCount(all full legal words)=N; for ω∈Ω with ¬Legal(fullList(ω)), weight(ω)=0.
F02. For legal ambient x and w.length≤i<len x, PieceEvent(ε,x,i) equals {ω∈B(w) | take(i,ω)=take(i,x) and digit(ω,i)<digit(x,i)} on the left (reverse on right). Different valid first-difference indices give disjoint PieceEvents. Their union is the portion of B(w) whose depth-len(x) truncation is lexicographically before/after x.
F03. If v prefixes legal ambient x and w.length≤i<len v, PieceEvent(ε,x,i)=PieceEvent(ε,v,i). Therefore SideMaximum, SideFluctuation and cFAt(v,x)=cFAt(v,v) are invariant under continuation.
F04. For a genuine boundary crossing and any full legal extension of its join, replacing its crossing digit by the corresponding large boundary digit gives a full legal word in that side PieceEvent. For every raw nonterminal compatible pair, both side maxima and square roots are positive, cF is not bottom, and both components have length>w.length. Every raw compatible pair is Retained, including terminal pairs. Thus no compatible admissible pair is lost by retention.
F05. ExtendedLog(0)=bottom; for q>0 it equals the indicated real log. If cF=f is finite, Stop(x) iff cL(x)-f<δ. If cF is bottom, Stop(x) is false. Retained nonterminal pairs have finite real cF; terminal pairs may have bottom.

### S — stable stopping

S01. For legal ambient x prefix y, cL(y)≤cL(x). Each added legal coordinate has nonnegative cost, since n≤N and log N>0. Therefore Stop(y,z,x) persists to every legal descendant with the same pair.
S02. For GenericCut with precisely D14 hypotheses, every full descendant has exactly one selected prefix; the family is a prefix antichain. If root fails Q and is not a leaf, any first crossing is a strict descendant, its parent extends root and fails Q, and all preceding root-descendant prefixes fail Q. If there is no crossing, the terminal word is the fallback. Crossing at K and threshold equality/fallback are covered.
S03. For a raw compatible pair, Gamma∩Lambda is empty. In the root-not-stopped branch every Gamma member is a strict join descendant and its parent is a legal ambient extension. Every preceding prefix between join and parent fails Stop. For full x∈A(y,z) in that branch, Lambda membership is equivalent to having no stopped prefix between join and x. Gamma members have no strictly longer selected descendants; Lambda members are leaves.
S04. For terminal raw pairs Stable={v}; for nonterminal raw pairs with Stop(v), Stable={v}. If w.length=K then both selected boundaries of any ω∈B(w) equal w and the stable family is {w}. Stable={v} is not asserted equivalent to cardinality one. For any raw pair Stable equals GenericCut(v,Stop).
S05. For every retained boundary pair (raw-family membership plus Retained), Stable is an antichain; every ω∈B(v) has exactly one stable prefix; its cylinders form a pairwise disjoint cover of B(v). Under any legal sorted row map the associated rank sets are individually order-convex, pairwise disjoint and cover I(B(v)). This is the full exact content of article lem:ub-stable-partition.

### G — global retained decomposition

G01. For ω∈B(w), existence of a retained admissible pair and stable prefix x with ω∈B(x) is equivalent to Admissible(left,Select(left,ω)) and Admissible(right,Select(right,ω)). When such an indexed triple exists it is unique.
G02. Indexed by admissible retained pairs and their stable members, all cylinders are pairwise disjoint. Their union is exactly the ambient full strings whose two selected boundary prefixes are admissible. The complement in B(w) is exactly failure of at least one admissibility predicate. Before truncation the union is B(w). This is the full exact content of article lem:ub-global-boundary-decomposition.
G03. The same equalities, disjointness, and omitted-string characterization hold after inverse image under any legal sorted row map; each individual piece is an order-convex rank set, including empty pieces. No probability or nonemptiness assumption is added.

## Dependencies and excluded conclusions

B01 depends on pile sums; W02 uses B01's positive-column fact; B02–B05 depend on W01–W04 and finite first-crossing minimality. F01 uses W05 and finite products; F02 uses W01–W02 and lex first difference; F03 uses F02; F04 uses B01,B02,W02,F01,F02. S01 uses B01 and real log monotonicity; S02 uses only W01,W02 and finite minimality; S03–S05 use W04,F05,S01,S02. G01–G03 use B04,B05,F04,S05,W06. No circular dependence on analytic estimates occurs.

The independent audit found that article lem:ub-ambient-concentration-anti-concentration cannot be imported as proved with these exact fluctuation definitions: equal deterministic three-pile first columns give fixed middle-block endpoints despite positive defined side mass. This is recorded without changing the assigned definitions. The whole-proof map also records that a random-pile lower bound needs a common hypothesis test; averaging conditional TV lower bounds is invalid.

Original mathematical sources remain unchanged. A freeze record will hash this file and the three inputs after all three reports agree. Final validation must kernel-check all project files, reject prohibited proof placeholders, and report project theorem dependency axioms using Lean's audit command; only foundational Lean logic and trusted mathlib dependencies may occur, never a new project axiom.
