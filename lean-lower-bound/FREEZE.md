# FROZEN CONTRACT v1

Freeze timestamp (UTC): 2026-09-17T20:11:32.408575+00:00.

No Lean source had been written in this deliverable at freeze. All mathematical
assumptions, definitions, and exported statements below are frozen. The three
independent reviewers read the authorized old proof sources and approved every
group: reconstruction, Lean statement design, and adversarial threshold audit.
Their reports are retained under review/. Generic profile mass/cost names are
`digitWordMass` and `digitWordCost`; concrete fixed-column names are `wordMass`
and `wordMean`. All indices use Fin N, hence zero-based positions. Tuple.sort
maps sorted output positions to original row labels. Words in the probability
model are raw functions; the stable output applies their lexicographic type tag.

Implementation may choose proof-local have statements, proof-irrelevant parameters,
and equivalent notation/implicit arguments, but must preserve the exact quantified
mathematics below. No extra hypotheses, axioms, or unproved placeholders are allowed.
Every theorem must be kernel checked. Ordinary trusted Lean/mathlib foundations
(propositional extensionality, classical choice, quotient soundness) are permitted;
no custom axiom or native evaluation oracle is permitted.

The source's full asymptotic cold theorem is NOT part of this formalized claim.
The authoritative finite endpoints are L01/L02 with (N−m+1)/m!, superseding the
weaker provisional N/m! expression in the historical statement-design report.

Review comparison: every role agrees on the actual independent-column model,
full-word rather than proper-prefix obstruction, strict m<μ, zero-pile handling,
correct 1/2 TV factor, and common-test requirement for random environments. All
three reject importing the false block-bounded-difference argument. The explicit
finite core is not conditional on the desired cold-spot conclusion.

# P/L contract

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

Every exported definition and lemma in the sorting/profile, fixed-column, and uniform-permutation modules are listed in the module contracts below and were reviewed by all three agents before this freeze. Local proof steps may use only these assumptions and trusted Lean/mathlib results. No extra top-level lemma may be introduced without prior independent review and an explicit, separately versioned contract; existing frozen statements must never change.

The cold-spot asymptotic theorem, exponential scan concentration, convergence of empirical profiles, tilted type asymptotics, endpoint localization, and Poisson approximation are explicitly outside the initial finite endpoint. Finite cold algebra/profile facts may be included only through the reviewed module contracts.


---

# Sorting, finite profiles, and cold combinatorics — frozen contract

This is the frozen mathematical contract; it was reviewed before any Lean declarations were written. It uses the
shared `RiffleLower` API in `contract-candidate.md`. All real-valued expressions
below use explicit natural-to-real casts where needed.

## Definitions

For `N : Nat`, a linearly ordered type `W`, and `f : Fin N -> W`:

* `stableSort f : Perm (Fin N)` is exactly `Tuple.sort f`.
* `sortedKey f i := f (stableSort f i)`.
* `keyCount f w := (univ.filter (fun i => f i = w)).card`.
* `lowerRank f w := (univ.filter (fun i => f i < w)).card`.
* `HasIncreasingRun sigma m` has exactly the definition in the shared contract:
  there exists `a : Nat` with `a+m <= N` such that for every `i j : Fin N`,
  `a <= i.val -> j.val < a+m -> i<j -> sigma i<sigma j`.

The concrete model's full-word type is `Lex (Fin K -> Fin k)`, with its
lexicographic linear order, and `f i` is the lex-tagged complete row word. No
prefix projection is used in the inverse output or the run theorem.

For finite types `Time`, `Cell`, and `Digit`, functions `cell : Time -> Cell`
and `word : Time -> Digit`:

* `digitCount cell word c d` is
  `(univ.filter (fun t => cell t = c and word t = d)).card`.
* `cellCount cell c := (univ.filter (fun t => cell t = c)).card`.
* For `p : Time -> Digit -> Real`, `digitWordMass p word := product_t p t (word t)`.
* `digitWordCost p word := -sum_t Real.log (p t (word t))`.
* For `r : Cell -> Digit -> Real`,
  `profileMass r cell word := product_c product_d (r c d)^(digitCount cell word c d)`.

The following cold exponents are functions of arbitrary real arguments
`beta, theta, J, J2, B, B2`; they do not refer to unformalized integrals:

* `tiltedEntropy theta J B := theta*J-B`.
* `coldSize beta theta J B := beta-J+tiltedEntropy theta J B`.
* `coldCollision beta theta J J2 B B2 :=
  2*beta-2*J-2*J2+tiltedEntropy theta J B+tiltedEntropy 2 J2 B2`.
* `coldMargin beta theta B B2 := (theta+3)*beta/2-B-2*B2`.

For finite position subsets `H : Finset (Fin N)`:

* `pathPairs N` is the finite set of pairs `(i,j) : Fin N × Fin N` with
  `j.val=i.val+1`.
* `equalKeyEdges f H` is the subset of `pathPairs N` consisting of pairs with
  `i in H`, `j in H`, and `sortedKey f i = sortedKey f j`.
* `ascentEdges sigma H` is the subset of `pathPairs N` consisting of pairs with
  `i in H`, `j in H`, and `sigma i < sigma j`.
* For `S : Finset W`, `localizedKeys f S H` means
  `forall w in S, forall i : Fin N, sortedKey f i=w -> i in H`.

## S: stable sorting

Each S statement quantifies over `N : Nat`, `W` with a linear order, and
`f : Fin N -> W`. There is no nonemptiness or stochastic assumption.

S1. If `i,j,l : Fin N`, `i<=j`, `j<=l`, and
`sortedKey f i=sortedKey f l`, then `sortedKey f j=sortedKey f i`.

S2. If `i,j : Fin N`, `i<j`, and `sortedKey f i=sortedKey f j`, then
`stableSort f i < stableSort f j`.

S3. For `w : W` and `i : Fin N`,

`sortedKey f i=w <-> lowerRank f w <= i.val and i.val < lowerRank f w+keyCount f w`.

S4. For `m : Nat` and `w : W`, if `1<=m` and `m<=keyCount f w`, then
`HasIncreasingRun (stableSort f) m`.

Dependencies: S1 and S2 use trusted `Tuple.monotone_sort` and
`Tuple.eq_sort_iff`. S3 uses finite order/counting and sorting bijectivity. S4
uses S2 and S3. The stable inverse output definition from the shared model
instantiates S4 with full row words.

## D: exact finite time-dependent digit profiles

Each D statement quantifies over the finite types and functions in the
definitions above. Empty time, cell, or digit types are allowed whenever the
functions themselves exist.

D1a. For every cell `c`,

`sum_d digitCount cell word c d = cellCount cell c`.

D1b. `sum_c sum_d digitCount cell word c d = Fintype.card Time`.

D2. For arbitrary `r : Cell -> Digit -> Real`,

`digitWordMass (fun t d => r (cell t) d) word = profileMass r cell word`.

No positivity or normalization is assumed; this is finite product regrouping.

D3. For `p : Time -> Digit -> Real`, if
`forall t, 0 < p t (word t)`, then

`Real.log (digitWordMass p word) = -digitWordCost p word`.

The hypothesis is explicit positivity of the selected digits only. It is not
imposed on the fixed-column model or on D2/D4, which permit zero piles.

D4. For `p : Time -> Digit -> Real`, `star : Time -> Digit`, and any `word`,
if `forall t d, 0 <= p t d` and `forall t d, p t d <= p t (star t)`, then

`digitWordMass p word <= digitWordMass p star`.

Dependencies: D1 is a disjoint partition of the finite time set; D2 is finite
product regrouping; D3 is the trusted real-log product theorem on nonzero
factors; D4 is finite product monotonicity. None depends on a Riemann-sum limit.

## C: finite cold algebra and combinatorics

C1. For arbitrary reals `beta,theta,J,J2,B,B2`,

`2*coldCollision beta theta J J2 B B2
 -coldSize beta theta J B
 -coldMargin beta theta B B2
 =(theta-3)*(J-beta/2)`.

C2. For arbitrary `N`, linearly ordered `W`, `f : Fin N -> W`, `S : Finset W`,
and `H : Finset (Fin N)`, if `localizedKeys f S H`, then

`(S.filter (fun w => 2 <= keyCount f w)).card <= (equalKeyEdges f H).card`.

The hypothesis is the exact deterministic statement needed to transfer repeated
cold words to edges; no probability, asymptotics, or hidden occupancy estimate is
assumed. This theorem does not claim to construct or probabilistically localize
the cold set.

C3a. For every `N`, linearly ordered `W`, `f`, and `H`,

`equalKeyEdges f H` is a subset of `ascentEdges (stableSort f) H`.

C3b. Consequently `(equalKeyEdges f H).card <= (ascentEdges (stableSort f) H).card`.

Dependencies: C1 is algebra only. C2 uses S3 to pick the first adjacent pair
in each repeated key's fiber, and equality of its first sorted key makes this
map injective. C3a uses S2 and the strict order of adjacent positions; C3b is
finite-cardinality monotonicity.



---

# M: frozen fixed-column moment contract

This contract uses exactly the shared `RiffleLower.FiniteLaw`, real probability, expectation, variance, uniform law, base-column array, sample space, row words, and word-count definitions in `contract-candidate.md`. It introduces no probabilistic assumptions beyond that concrete finite model. It is frozen by this record.

## Definitions owned by this module

* `ColumnArray N K k := Fin K → Fin N → Fin k`.
* `ColumnRandomness N K := Fin K → Equiv.Perm (Fin N)`.
* `columnCount c t a := (Finset.univ.filter (fun i => c t i = a)).card`.
* `rowWord c ω i := fun t => c t (ω t i)`.
* `wordCount c w ω := (Finset.univ.filter (fun i => rowWord c ω i = w)).card`.
* `wordMass c w := ∏ t, (columnCount c t (w t) : ℝ) / (N : ℝ)`.
* `wordMean c w := (N : ℝ) * wordMass c w`.
* `pairWordMass c w := ∏ t, ((columnCount c t (w t) : ℝ) * ((columnCount c t (w t) : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1))`.

All `N,K,k` are natural numbers. Every subtraction in a displayed real probability or moment expression occurs after casting to `ℝ`. An indicator is real-valued `if proposition then 1 else 0`. Predicate events mean `Finset.univ.filter` of the predicate. Empty products equal one. No lemma below excludes zero piles, deterministic columns, `K=0`, or repeated columns.

## Generic exact uniform counting helpers

M01. **`uniform_expect_equiv`**. For finite nonempty types `α,β`, an equivalence `e : α ≃ β`, and `f : β → ℝ`,

`expect (uniformLaw α) (fun a => f (e a)) = expect (uniformLaw β) f`.

M02. **`uniform_pi_expect_prod`**. Let `T` be finite, `A : T → Type` be finite nonempty coordinate types, and `f : ∀ t, A t → ℝ`. Then

`expect (uniformLaw (∀ t, A t)) (fun ω => ∏ t, f t (ω t)) = ∏ t, expect (uniformLaw (A t)) (f t)`.

M03. **`uniform_perm_indicator`**. For `N>0`, `S : Finset (Fin N)`, and `i : Fin N`,

`expect (uniformLaw (Equiv.Perm (Fin N))) (fun σ => if σ i ∈ S then 1 else 0) = (S.card : ℝ) / (N : ℝ)`.

M04. **`uniform_perm_pair_indicator`**. For `N≥2`, `S : Finset (Fin N)`, and `i,j : Fin N` with `i ≠ j`,

`expect (uniformLaw (Equiv.Perm (Fin N))) (fun σ => (if σ i ∈ S then 1 else 0) * (if σ j ∈ S then 1 else 0)) = ((S.card : ℝ) * ((S.card : ℝ) - 1)) / ((N : ℝ) * ((N : ℝ) - 1))`.

M05. **`indicator_sum_factorial`**. For a finite type `I` and predicate `B : I → Prop`, put `Y := (Finset.univ.filter B).card`. Then

`(Y : ℝ) = ∑ i, if B i then 1 else 0`,

and

`(Y : ℝ) * ((Y : ℝ) - 1) = ∑ i, ∑ j, if i ≠ j ∧ B i ∧ B j then 1 else 0`.

These are the only general exchangeability/counting helpers planned for the moment implementation. Permutation symmetry can be proved inside M03/M04 using right composition by a transposition. There is no need to assume independence of row indicators.

## Concrete column and word identities

M06. **`columnCount_le` / `sum_columnCount`**. For every `c,t,a`, `columnCount c t a ≤ N`; and for every `c,t`, `∑ a, columnCount c t a = N`.

M07. **`wordMass_bounds` / `wordMean_bounds`**. Under `0<N`,

`0 ≤ wordMass c w ∧ wordMass c w ≤ 1`,

`0 ≤ wordMean c w ∧ wordMean c w ≤ (N : ℝ)`.

M08. **`word_row_probability`**. Under `0<N`, for each `i : Fin N`,

`prob (uniformLaw (ColumnRandomness N K)) {ω | rowWord c ω i = w} = wordMass c w`.

M09. **`word_two_rows_probability`**. Under `2≤N`, for each distinct `i,j : Fin N`,

`prob (uniformLaw (ColumnRandomness N K)) {ω | rowWord c ω i = w ∧ rowWord c ω j = w} = pairWordMass c w`.

M10. **`wordCount_expect`**. Under `0<N`,

`expect (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ)) = wordMean c w`.

M11. **`wordCount_factorial_second_moment`**. Under `2≤N`,

`expect (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ) * ((wordCount c w ω : ℝ) - 1)) = (N : ℝ) * ((N : ℝ) - 1) * pairWordMass c w`.

## Nonpositive covariance and finite lower tail

M12. **`one_column_pair_le_square`**. For naturals `d,N`, assuming `2≤N` and `d≤N`,

`0 ≤ (d : ℝ) * ((d : ℝ)-1) / ((N : ℝ)*((N : ℝ)-1))`,

`(d : ℝ) * ((d : ℝ)-1) / ((N : ℝ)*((N : ℝ)-1)) ≤ ((d : ℝ)/(N : ℝ))^2`.

M13. **`pairWordMass_le_square`**. Under `2≤N`,

`0 ≤ pairWordMass c w ∧ pairWordMass c w ≤ (wordMass c w)^2`.

M14. **`wordCount_variance_le_mean`**. Under `2≤N`,

`variance (uniformLaw (ColumnRandomness N K)) (fun ω => (wordCount c w ω : ℝ)) ≤ wordMean c w`.

M15. **`wordCount_lower_tail`**. Under `2≤N`, for any natural `m` satisfying `(m : ℝ)<wordMean c w`,

`prob (uniformLaw (ColumnRandomness N K)) {ω | m ≤ wordCount c w ω} ≥ 1 - wordMean c w / (wordMean c w - (m : ℝ))^2`.

This is a direct application of shared P14 after M10 and M14. It must not import a hypergeometric concentration theorem or require positive pile proportions. The Chebyshev error is deliberately weaker than the article's exponential estimate and is sufficient for the largest-full-word finite lower-bound endpoint.

## Dependency graph

* M01 depends on shared P05 and finite sum reindexing.
* M02 depends on P05 and the finite product-of-sums identity.
* M03 depends on M01 and double counting a permutation's selected positions.
* M04 depends on M01, M03, and double counting selected ordered pairs; transpositions fixing one index suffice.
* M05 and M06 are finite counting identities.
* M07 depends on M06 and elementary nonnegative product bounds.
* M08 depends on M02, M03, and the equivalence of word equality with equality at every coordinate.
* M09 depends on M02, M04, and the same coordinatewise equality equivalence.
* M10 depends on M05, M08, and expectation of a finite sum.
* M11 depends on M05, M09, and expectation of a finite sum.
* M12 is elementary real arithmetic, including the cases `d=0,1`.
* M13 depends on M06, M12, and the product of inequalities.
* M14 depends on M10, M11, M13, and shared P11/P13.
* M15 depends on M10, M14, and P14.



---

# U: frozen uniform-permutation contract


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

