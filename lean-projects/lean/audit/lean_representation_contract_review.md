# Final representation review of the pre-implementation contract

Reviewed `CONTRACT_DRAFT.md` against the permitted mathematical sources, my independently written `lean_representation.md`, and the inspected mathlib v4.19.0 interfaces. No Lean code was written. Every candidate below is approved, subject to three explicit spelling clarifications recorded at the end; these clarifications unpack already stated mathematical meanings and add no new assumption.

| ID | Representation review |
| --- | --- |
| F1 | Approved. Literal finite real sums give all identities. Linearity includes real scalar coefficients; monotonicity uses pointwise inequalities. Nonempty outcome spaces follow from normalization rather than being an extra premise. |
| F2 | Approved. Positive thresholds are exactly the premises needed for division. The centered-square form of variance in D1 directly supplies Chebyshev. |
| F3 | Approved. A positive event permits normalization; a uniform fibre is uniform either on the fibre subtype or, after the inclusion map, on the original type supported on that fibre. Null fibres carry zero mass and require no conditional probability law. |
| F4 | Approved. The coarser conditional version must use the conditional weights `P(Z=z | U=u)`. Only supported finer atoms contribute; all are positive unconditionally when positive inside a positive coarse atom. |
| F5 | Approved. On each finer fibre, the shift is fixed. If `j-A(z)` is negative the event is empty; otherwise it is a natural point-mass event. On fibres outside H, the restricted event S is empty. Thus S need not be reveal-measurable. The natural Y is cast to the integers before adding A. |
| H0 | Approved. The finite type `Fin(m+1)` prevents the truncated-subtraction mass-function error outside q≤m. The exact support criterion also handles N=0. Uniform-subset fibre counting supplies the sampling bridge; `PMF.ofFintype` supplies the probability representation once normalization is proved. |
| H1 | Approved. The N=0 law is concentrated at zero, and real total division makes μ=0. No positive-population premise is needed. |
| H2 | Approved. Natural descending factorials are essential. At order zero all factors are one, even for N=0. If r>N, both the random factorial and the numerator factorials vanish; the zero denominator gives the desired zero under total division. The order-two casts-first polynomial identity also holds for K=0 or m=0 because the zero factor eliminates the negative adjacent factor. |
| H3 | Approved. The stated casts-first variance has value zero at N=0 and N=1. For N≥2 the denominator is positive and the four zero-factor alternatives are exact. No N≥2 restriction should be inserted into the universal target. |
| H4 | Approved. Each endpoint parameter case determines the single possible intersection count. The zero-variance characterization from H3 gives deterministic laws and vanishing positive centered tails. |
| H5 | Approved. The existential constant must precede all parameter and threshold quantifiers. The mean-zero and t=0 conventions are explicitly correct. The target must be proved from D3 and cannot be replaced by F2 or an assumed negative-dependence property. |
| H6 | Approved. Strictly positive variance is precisely the branch where inverse square root is appropriate. The formulation covers points outside the finite support by zero mass. An eventual chosen numerical constant is proof data and does not alter this existential target. |
| H7 | Approved. Exponentiation is by natural Y and K. For N=0, feasibility gives K=m=0, the left side is one and the right side is the zeroth power of one. No independent-indicator assumption is allowed. |
| C1 | Approved. The residual-subset bijection is `S ↔ S\R` on the fibre `S∩R=B`, with inverse `T ↦ B∪T`. The listed conditions make both directions valid and ensure fibre nonemptiness. Empty residual universes produce the unique empty subset. |
| C2 | Approved. A prescribed map on R already supplies total prescribed count |R|. Per-digit domination implies the residual counts sum to |V\R|. Uniformity is a restriction/extension bijection; independence survives precisely because the joint prescribed event factors by column. |
| C3 | Approved. The marked set is a function of the reveal, hence fixed on each atom, and is a subset of V. The uniform conditional sample still comes from V; replacing population size by the preceding survivor count would be incorrect. |
| C4 | Approved. Equality of finite conditional laws transports every finite weighted sum and event probability. Thresholds depending on the reveal are constants inside the fibre. This is an interface lemma; equality of laws must be independently established at every shuffle application. |
| N1 | Approved. For N≥2 the finite-population correction N/(N−1) is at least one. Feasible parameters give nonnegative mean and complement factors. Therefore all weak lower bounds multiply without a sign issue. Its premises are local to this arithmetic implication and do not repair the ambient theorem. |
| N2 | Approved. The first conclusion uses `N−r>0`, reserve `h≤N−r−m`, and `N−r≤N` from r≥0. The second is the exact identity `((K−s)/(N−r)−K/N)=(rK/N−s)/(N−r)` followed by the absolute-value bound; r≥0 is not needed for this second implication. |
| X1 | Approved. Sampling all 2L residual labels gives Y=L deterministically. For the manuscript embedding, take at least two columns so the first-column crossings are nonterminal. In piles (L,1,L), c_L of the middle prefix is zero while c_F is nonnegative, so the stable family selects the singleton prefix for every positive δ. The bare finite-law and endpoint counterexamples need no probabilistic estimate. |

## Explicit spelling to retain in the frozen version

1. In F4, the coarser probability bound is `Σ z, P(Z=z | U=u) * b(z)`.
2. In C3, “marked subset” means `A(z) ⊆ V` on every supported reveal atom; “uniform m-subset” already entails `m ≤ |V|`.
3. In X1's manuscript embedding, there are at least two matrix columns, so the length-one boundary pair is nonterminal. The deterministic finite hypergeometric counterexample is valid independently of any number of columns.

These are clarifications of the candidate's terms, not permission to strengthen any frozen theorem later. For implementation, separate the N=0/N=1 cases before canceling denominators. A mathlib measure bridge should discharge measurability and square-integrability from the finite construction, not add them as new hypotheses to H1–H7.
