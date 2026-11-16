# Sorting, finite profiles, and cold combinatorics — candidate contract

This contract is not frozen and introduces no Lean declarations. It uses the
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

## Independent audit of the shared candidate P/L statements

P01–P08 are valid finite-law identities or inequalities with the stated
normalization assumptions. P07 is the half-L1 TV convention and uses equal
total masses to obtain the factor one-half in the event bound.

P09 is valid, including `delta>1`: split that case, where the conclusion follows
from nonnegative probability. When `delta<=1`, typical mass times `1-delta` is
at least `1-epsilon-delta`. P10 is valid by P09 for the union event, the union
bound, and P08. Its bounds `b(e)` require no separate sign hypothesis because
`prob Q(A e)<=b(e)` already implies `b(e)>=0` on the relevant finite set.

P11–P14 are valid even for a general real-valued `f`. P13 follows by expanding
`f(f-1)=f²-f`. In P14, `m<mu` ensures a positive deviation threshold; the
complement `{f<m}` is contained in `{mu-m<=abs(f-mu)}`. No nonnegativity of
`f` is needed, and `variance<=mu` itself forces `mu>=0`.

L01 is valid for the concrete uniform independent-column model, provided the
one-/two-row moment and exact uniform run-count lemmas are actually proved.
The event is an observable run of the stable inverse output and uses a complete
word. `m=N` is allowed but its strict mean hypothesis is impossible in this
model, so it introduces no false endpoint. `K=0` is legitimate. There is no
need to add `k>=1`: if the displayed column array or word cannot exist, the
corresponding quantified instance is empty.

L02 is valid with a common run length `m`; this single event is shared by all
environments. Consequently the uniform false-positive penalty is paid once,
not once per environment. The mixture/typical-event lemma gives success at
least `1-epsilon-delta`. No homogeneous cutoff constant, integral replacement,
or new concentration hypothesis is hidden in either endpoint.

Audit result: approve P01–P14 and L01–L02 as mathematically stated.

U01–U08 in `threshold-audit.md` are also approved. U01 relies on injectivity:
sorting a tuple with repeated values would not have a unique increasing
reordering. The embedding in U02–U04 supplies precisely that injectivity and
implies `m<=N`. U05 correctly includes the empty interval, and U06's `m=0`
bound is harmless. U07 requires only distinct supplied positions, and U08
requires no independence because it uses expectation linearity only.

M01–M15 in `moments-contract.md` are approved. In M12 the expression with a
real subtraction remains nonnegative at `d=0` because its first factor is
zero; at `d=1` it is also zero. No positive-pile hypothesis should be added.
M14 uses `N(N-1)<=N²` in addition to the displayed pair-mass inequality, with
nonnegative factors. M15 retains the strict threshold `m<mu`. To avoid an API
collision, this module's generic product is named `digitWordMass`, while the
concrete moment module retains `wordMass`.
