# Candidate contract — not yet frozen

Only the three user-named mathematical sources are used. The finite model below specializes their independent, uniform fixed-column model exactly. No asymptotic profile, concentration, or cutoff assertion is imported as a hypothesis.

## Shared definitions

All finite types carry Fintype instances; equality and event membership may be classical. All probability masses and expectations are real numbers. Namespace: RiffleLower.

* `FiniteLaw α`: mass α→ℝ, nonnegativity at every point, sum of masses equal to one.
* `prob P A`: sum of P.mass over the finite event A.
* `expect P f`: sum over α of P.mass(a) f(a).
* `variance P f`: expect P ((f−expect P f)²).
* `uniformLaw α`, for nonempty α: every mass is 1/card(α).
* `mapLaw P f`: pushforward mass at b is the sum of P.mass over {a:f(a)=b}.
* `mixture ρ P`: mass at a is sum_e ρ.mass(e) P(e).mass(a).
* `tv P Q`: (sum_a |P.mass(a)−Q.mass(a)|)/2.
* `unionEvents A G`: union of A(e) for e in finite G.

## P: finite probability and hypothesis tests

All P and Q below are FiniteLaw values; this carries precisely nonnegativity and normalization.

P01. prob is nonnegative, at most one, zero on empty, one on univ, and monotone under inclusion.
P02. prob P Aᶜ = 1−prob P A.
P03. prob of a finite union is at most the sum of individual probabilities; in particular at most card(G)δ when each event indexed by G has probability ≤δ.
P04. Expectation preserves pointwise inequalities, constants, sums, addition, subtraction, and scalar multiplication. The expectation of an event indicator is its probability.
P05. The uniform probability of A is card(A)/card(α); uniform expectation is sum(f)/card(α).
P06. The displayed mass definitions of mapLaw and mixture give normalized nonnegative laws; probabilities and expectations obey the finite preimage and averaging identities.
P07. 0≤tv P Q≤1, and |prob P A−prob Q A|≤tv P Q.
P08. If prob P A≥1−ε and prob Q A≤δ, then tv P Q≥1−ε−δ. ε,δ are arbitrary reals; no unstated sign requirement.
P09. If ε≥0, δ≥0, prob ρ G≥1−ε, and prob (P e) A≥1−δ for all e∈G, then prob (mixture ρ P) A≥1−ε−δ.
P10. If ε≥0, δ≥0, prob ρ G≥1−ε, prob(P e)(A e)≥1−δ for all e∈G, and prob Q(A e)≤b(e) for all e∈G, then tv (mixture ρ P) Q≥1−ε−δ−sum_{e∈G} b(e). The observable event is unionEvents A G, independent of the realized environment.
P11. variance P f = expect P (f²)−(expect P f)², and variance is nonnegative.
P12. For t>0, prob P {a:t≤|f(a)−expect P f|}≤variance P f/t².
P13. For μ=expect P f, if expect P (f(f−1))≤μ², then variance P f≤μ.
P14. For μ=expect P f, if m<μ and variance P f≤μ, then prob P {a:m≤f(a)}≥1−μ/(μ−m)². Here m is real; there is no extra independence or concentration hypothesis.

## Concrete fixed-column model shared by the remaining modules

N,k,K are natural numbers. A base column array is c:Fin K→Fin N→Fin k. This makes the nonnegative integer pile counts and their sum N definitional: n(t,a)=card{i:c(t,i)=a}.

The random source Ω is Fin K→Perm(Fin N) with the uniform law. Thus columns are independent uniform randomizations of the prescribed multisets. For ω∈Ω and row i, row(c,ω,i)(t)=c(t,ω(t)(i)). Full words have all K coordinates, endowed with the lexicographic linear order. The inverse output permutation is the stable sorting permutation Tuple.sort of these row words.

For a full word w, Y(c,w,ω)=card{i:row(c,ω,i)=w}; p(t)=n(t,w(t))/N; λ=product_t p(t); μ=Nλ.

`HasIncreasingRun σ m` means there exists a natural start a with a+m≤N such that σ(i)<σ(j) whenever a≤i.val, j.val<a+m and i<j. The event depends only on the output permutation, never on hidden columns or their word witness.

## Endpoint statements

L01. With N≥2, 1≤m≤N and m<μ, the total variation distance between the stable inverse output of the concrete fixed-column model and the uniform permutation law is at least 1−μ/(μ−m)²−(N−m+1)/m!. Casts in this formula are real. This is a finite lower bound, not a cutoff theorem.
L02. Let E be a finite type, ρ a probability law on E, c(e) a fixed-column array with common N,k,K, w(e) a full word, and G⊆E. Suppose N≥2, 1≤m≤N, ε≥0, δ≥0, prob ρ G≥1−ε, and for every e∈G, m<μ(e) and μ(e)/(μ(e)−m)²≤δ. Then the mixture inverse-shuffle law has total variation distance from uniform at least 1−ε−δ−(N−m+1)/m!.

Every exported definition and lemma in the sorting/profile, fixed-column, and uniform-permutation modules must be listed in the appended module contracts and reviewed by all three agents before freeze. Local proof steps may use only these assumptions and trusted Lean/mathlib results. No extra top-level lemma may be introduced without prior independent review and an explicit, separately versioned contract; existing frozen statements must never change.

The cold-spot asymptotic theorem, exponential scan concentration, convergence of empirical profiles, tilted type asymptotics, endpoint localization, and Poisson approximation are explicitly outside the initial finite endpoint. Finite cold algebra/profile facts may be included only through the reviewed module contracts.
