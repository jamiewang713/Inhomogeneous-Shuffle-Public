# Frozen mathematical contract v1

Status: FROZEN before Lean implementation, after unanimous independent per-ID review by probability reconstruction, Lean representation, and hypothesis audit. The mathematical sources and full dependency map are recorded in `proof_structure.md`. This contract does not change the manuscript.

## Definitions

D1. A finite law on a finite type Ω consists of real masses p(ω)≥0 summing to one. Probability of a predicate E is Σω p(ω)·1_E(ω); expectation of f is Σω p(ω)f(ω); variance is E[(f−Ef)²]. All predicates on these finite spaces are decidable classically. There are no extra integrability or nonempty-population assumptions. A finite law itself implies its outcome space is nonempty.

D2. Its conditional mass on an event E of strictly positive probability is p(ω)·1_E(ω)/P(E). Conditional expressions on null events are not asserted to be probability laws. Pushforward, product, and mixtures use their literal finite sums. A reveal is a function Z:Ω→Γ into a finite type. Positive reveal atoms are the events Z=z with positive probability.

D3. Hypergeometric parameters consist of natural numbers `population` N, `marked` K, and `draws` m, with K≤N and m≤N. Outcomes are q∈{0,…,m}, represented by Fin(m+1). Their mass is C(K,q) C(N−K,m−q)/C(N,m), with natural binomial coefficients and natural subtractions. An arbitrary natural point q has mass zero if q>m. Feasibility belongs to the definition of the experiment. Normalization must be proved.

D4. μ=K·m/N and v=K·m·(N−K)·(N−m)/(N²(N−1)), with every parameter cast to ℝ BEFORE subtraction or division. Real division is total, x/0=0. The falling factorial of a natural x at order r is Nat.descFactorial x r, cast to ℝ. Thus (x)_0=1 and (x)_r=0 for r>x.

D5. Sampling semantics: for a finite labelled population V, a fixed marked set A⊆V, and m≤|V|, S is uniform among the m-element subsets of V; Y=|A∩S|. Empty V and m=0 give the one-outcome empty-subset experiment. No independence of within-column row indicators is imposed.

D6. A legal fixed-count column on V with digit set Fin k is an assignment V→Fin k whose digit counts equal a given natural histogram n, Σ n=|V|. It is uniform on legal assignments. A matrix is a product of such independent columns. For random pile sizes, first choose the complete feasible histogram array with any finite law, then use this conditional product law. Independence of the random pile sizes is not imposed.

## Finite probability infrastructure

F1. For every finite law, event probabilities lie in [0,1], the empty event has probability zero and the full event one; probabilities are monotone and obey the finite union bound. Expectations are linear and preserve inequalities; variance equals E[f²]−(Ef)² and is nonnegative.

F2. For every finite law, f≥0 and t>0 imply P(f≥t)≤Ef/t. For every real-valued f and t>0, P(|f−Ef|≥t)≤Var(f)/t². These are auxiliary bounds, not replacements for H5.

F3. For a positive-probability event E, D2 defines a finite law and conditional probability is P(B∩E)/P(E). A uniform law conditioned on a nonempty fibre is uniform on that fibre. Null fibres contribute zero to unconditioned sums.

F4. Finite law of total probability and expectation over reveal atoms. If every positive atom obeys a numerical event-probability bound b(z), the unconditional event probability is at most Σz P(Z=z)b(z). The analogous conclusion on a positive coarser atom U=u uses the conditional weights Σz P(Z=z | U=u)b(z), whenever U=g∘Z. Bounds are required only for positive atoms.

F5. Suppose U=g∘Z, A:Γ→ℤ is a shift, Y:Ω→ℕ, H⊆Γ, S⊆{ω:Z(ω)∈H}, and b≥0. If, for every positive atom Z=z with z∈H and every q∈ℕ, P(Y=q|Z=z)≤b, then for every positive atom U=u and every j∈ℤ, P(A(Z)+Y=j and S|U=u)≤b. S need not itself be Z-measurable. No conditional-law claim is made at a null atom.

## Hypergeometric targets

H0. D3 masses are nonnegative and sum to one; their support is exactly q≤K, q≤m, and m−q≤N−K. The law agrees with D5 sampling semantics and has a mathlib PMF/measure representation with the same masses, expectations and variance.

H1. For every feasible D3 parameter, EY=μ, including N=0.

H2. For every natural r and every feasible parameter, E[(Y)_r]=(K)_r(m)_r/(N)_r, including r=0 and r>N. In particular E[Y(Y−1)]=K(K−1)m(m−1)/(N(N−1)), casts before real subtraction in the latter formula.

H3. For every feasible parameter, Var(Y)=v. Var(Y)=0 iff K=0 or m=0 or K=N or m=N. In particular N≤1 implies Var(Y)=0. There is no assumption N≥2 in this theorem.

H4. If K=0 or m=0, Y=0 with probability one; if m=N, Y=K with probability one; if K=N, Y=m with probability one. Hence for variance zero the law is deterministic, every positive centered-deviation tail has probability zero, and every point mass is at most one. These identities include N=0 and N=1.

H5. There exists an absolute real c>0 such that for EVERY feasible parameter and EVERY real t≥0,

P(|Y−μ|≥t) ≤ 2 exp(−c min(t²/(μ+t),t)).

The existential constant precedes the parameter quantifiers. The case μ=t=0 uses total division and gives 1≤2; μ=0,t>0 gives zero tail. Small means are included. No positive-mean premise may be added.

H6. There exists an absolute real C>0 such that for EVERY feasible parameter with v>0 and EVERY natural q,

P(Y=q) ≤ C/sqrt(v).

The zero-variance branch is H4; inverse zero is never used as an anti-concentration bound. A proof may choose an explicit constant, but the statement is existential.

H7. For EVERY feasible parameter and EVERY real s with 0<s≤1,

E[s^Y] ≤ (1−m/N+(m/N)s)^K.

The empty-population case is included and interpreted by total division. This is the one-step transform target from the successive-thinning proof, not an extra property assumed of D3.

## Conditional sampling and transfer targets

C1. Let R⊆V, B⊆R, |B|≤m, and m−|B|≤|V\R|. Under D5 uniform m-subset sampling, the event S∩R=B has positive probability and S\R, conditional on that event, is uniform among the (m−|B|)-subsets of V\R. Conversely these feasibility conditions characterize nonempty fibres. For a test set A⊆V\R, the conditional count |A∩S| has D3 law with N=|V\R|, K=|A|, m'=m−|B|. If no labels remain this is the empty law, not an error.

C2. In a D6 column, a prescription of symbols on a fixed R⊆V has positive probability exactly when each prescribed digit count r_l≤n_l. On each such event, the residual column is uniform with histogram n_l−r_l on V\R. For independent columns and one admissible prescription per column, the residual columns remain independent. This does not assert preservation under arbitrary exploration events.

C3. If a marked subset A⊆V is determined by already revealed information and S is, conditional on every positive reveal atom, a uniform m-subset of a fixed population V, then on that atom |A∩S| has the D3 law with N=|V|, K=|A|, m. In particular successive labelled-row thinning retains the FULL population N at each one-column transition.

C4. If an Ω-valued finite law, reveal Z and count Y satisfy equality of the conditional count law to D3 with feasible parameters p(z) on every positive atom, then H1–H7 transfer on those atoms with μ(z),v(z) and thresholds constant on each atom, retaining every original premise (including t≥0, v(z)>0, and 0<s≤1 where applicable). Conditional first and second centered moments are the corresponding finite weighted sums. F4 and F5 transfer their bounds to coarser information. Exact law equality is an interface, not a new assumption added to any shuffle application; C1–C3 must establish it there.

## Non-exhaustion arithmetic and counterexample

N1. For feasible parameters with N≥2, real u,a,b≥0, μ≥u, 1−K/N≥a, and 1−m/N≥b, v≥u·a·b. These are the explicit premises of a general arithmetic implication; they are NOT added to the false ambient theorem.

N2. For real N>0, 0≤r<N, m≥0, h≥0 and m+r≤N−h, the residual sample complement satisfies 1−m/(N−r)≥h/N. For real N>0,r<N,K,s,e with e≥0 and |s−rK/N|≤e, |(K−s)/(N−r)−K/N|≤e/(N−r). These algebraic implications explain the precise reserve and fluctuation estimates needed by an application.

X1. For every natural L≥1, the feasible hypergeometric law N=2L,K=L,m=2L is deterministic at L, has variance zero and sample complement 1−m/N=0, although its mean and both marked/unmarked population sizes are positive. This is the residual law in case a=b=1 for a root ambient block in a matrix with at least two columns, first-column piles (L,L,L), and x=y=z=(1). For every legal column with that histogram, exactly L rows precede the middle block and the cumulative count through the middle digit is exactly 2L, so both endpoints are deterministic. The alternative original piles (L,1,L), in population 2L+1, give the same residual law in population 2L and a singleton stable block. The source interpretation uses its standing k=3, 0<χ<1/3, δ>0 context; the exact finite count and residual-law statements do not require asymptotic assumptions. This refutes the manuscript's asserted non-exhaustion implication; it is not a corrected ambient theorem.

## Boundaries of this freeze

The ambient conditioning transfer, ambient non-exhaustion, and ambient endpoint anti-concentration statements in the manuscript are excluded from implementation as true theorems because all three independent reviews find X1. Their status remains **false as written**, pending an explicitly reviewed replacement. No axiom, assumption field, unproved declaration, or proof placeholder may stand in for them. The general exploration-preservation sketch likewise remains an unproved external integration obligation.

Exported definitions and mathematical conclusions must agree with this contract. Type/namespace spelling and proof-local intermediate equalities do not alter the contract. Any newly proposed mathematical lemma beyond these targets requires independent review before implementation; it must not strengthen or weaken the existing targets. Unfinished targets stay in documentation only, never as Lean declarations with missing proofs.
