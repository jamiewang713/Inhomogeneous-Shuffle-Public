# LB04 independent missing-hypothesis and counterexample review v1

Date: 2026-10-01. Mode: independent adversarial review before dependent proofs. Scope: assigned prompt; manuscript labels `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`; frozen target predicates in `Contracts/v1/Ascent.lean`; shared definitions in `RiffleLowerV2/Shared/Path.lean` and `Shared/Model.lean`. No manuscript, shared, contract, or dependent proof files were changed.

## Verdict

No mathematical counterexample was found to the five frozen target predicates. The finite concentration, clipped expectation, finite scan, precise failure comparison, and eventual deterministic graph scan are sound as stated. The specified strict and weak inequalities are compatible. No new assumptions are needed for these targets. This is a mathematical review, not a claim that any target predicate has been proved in Lean.

The implementation must preserve four distinctions: component sorting versus arbitrary block statistics; relative-order independence versus independence of sampled values; a deterministic graph-only translate choice versus a choice using the permutation; and a conditional mixture argument versus the actual shuffle representation. Arbitrary integer `H0` requires no support, nonnegativity, interval, connectedness, or diameter assumption.

## Finite hypotheses and degeneracies

1. **Relative orders.** Pairwise disjoint position sets are sufficient. Empty sets are permitted in the joint relative-order assertion: their relative-order space has one element and `0! = 1`. The separate max/min formula uses nonempty A and B; otherwise max/min is undefined in the intended formulation. The exact count is `N! / product_j |A_j|!` for a prescribed order in each set, and division by `N!` gives the product uniform distribution. The values themselves are sampled without replacement and are not independent; only their relative orders on disjoint sets are independent.

2. **Component concentration.** A deterministic path graph and deterministic H suffice. The retained intercomponent boundary indicators are functions of relative orders on consecutive pairs of *whole* components, even if H clips those components. Sorting leaves every graph edge inside H as a deterministic ascent. The two component-index parity classes contain disjoint pair-unions, hence give independence inside each class. No independence between the two classes is asserted or needed. For an edgeless graph on three positions, `P(Y1=Y2=1)=1/6`, whereas `P(Y1=1)P(Y2=1)=1/4`; a proof using independence of all retained indicators would be false.

3. **MGF constants.** Bernoulli centering gives `E exp(lambda(Y-EY)) ≤ exp(lambda²/8)` for every real lambda, including p=0 or 1. Applying Cauchy–Schwarz with `2 lambda` to the two parity sums gives `exp(lambda² B/4)` for B retained boundaries. Chernoff at `lambda=2t/B`, or applied to the negative centered variable, gives each weak one-sided tail `exp(-t²/B)`. Since `0 < B ≤ |E(H)| ≤ |H| ≤ M`, replacing B by M weakens this bound in the correct direction. Handle B=0 before division: X is constant, and both tails are empty for t>0. This also covers H empty, N=0, and N=1. M need not be an integer.

4. **Clipped expectation.** With infinite-integer-path boundary d, every partial component contains a boundary edge, yielding at most d partial components and at most 2d bad retained intercomponent edges. No positive lower bound on a bad-edge ascent probability is needed. The remaining edges join two whole components contained in H, and their binomial deficit is at most `(a+b-2)/6`; each whole component is charged at most twice. Their total deficit is at most r/3. All r internal graph edges contribute, including edges belonging to partial components. This gives `e/2+r/6-d` without a connectedness assumption on H.

   A concrete counterexample to dropping the clipping penalty is N=4, graph components `{1,2}` and `{3,4}`, and H=`{2,3}`. Here e=1, r=0, d=2 and `E X=1/choose(4,2)=1/6 < e/2`. A proof discarding internal graph edges in partial components also misrepresents X: for a full three-position graph component and H=`{1,2}`, X is identically 1, although there is no graph component wholly contained in H.

5. **Strictness.** The scan event is `X > e/2+s`; its complement is exactly `X ≤ e/2+s`. If `E X ≥ e/2+r/6-d` and `Delta=r/6-d-s>0`, that failure event implies `X-E X ≤ -Delta`. Thus the frozen weak lower tail supplies exactly the desired failure estimate. The uniform scan uses containment of the strict upper-tail event in the weak upper-tail event at t=s. No no-atom assertion is available or required: these distributions are finite and atomic. The two-sided bound follows from the union of the two weak one-sided events at t>0.

## Arbitrary integer H0 and scan indexing

The shared definition is correctly one-based at the manuscript boundary: `manuscriptRank i = i.val+1`, and `i ∈ clipTranslate N H0 q` iff `(i.val+1)-q ∈ H0`. The injection `i ↦ (i.val+1)-q` into H0 proves `|H_q| ≤ |H0|` for every integer q. This argument tolerates negative elements, elements far outside the deck, sparse sets, and empty clips. Do not convert H0 elements to natural numbers before membership testing.

For example, N=2 and H0=`{-1,0}` has full clip `{1,2}` at q=2. H0=`{1,3}` has no adjacent members in any clip, so all its ascent scans with s>0 are empty. Many or all of the N+1 clips may coincide or be empty; the union bound remains valid. The scan is over exactly q in `{0,...,N}`, represented by `Fin (N+1)`, not all integer translations. The factor N+1 follows from that finite domain, independently of H0 diameter.

`UniformScan` explicitly assumes `0 < H0.card`, which supplies M>0. `ComponentConcentration` allows empty H through a separately positive M. The eventual graph target has no explicit M>0, but choosing its eventual N0 at least 1 and using `N^a ≤ M`, a>0, supplies positivity. The pointwise analogue at N=0 would be false: H0 empty, G empty, all boundaries zero, and the witness lower bound `r ≥ M^(1/2+delta)` holds as `0 ≥ 0`, whereas the threshold-zero strict scan is false. This does not invalidate `UniformGraphScan`, whose quantifiers allow N0≥1.

There is no assumption M≤N in these targets. H0 can contain arbitrarily many points outside every relevant clip. An implementation that imports M≤N from the cold-set application would silently restrict the frozen generic statement. All displayed estimates are still valid for arbitrarily large M. For delta≥1/2 the large-edge witness is eventually impossible because `r ≤ |H_q|-1 ≤ M-1` for nonempty H_q; the asymptotic implication is then vacuous, which is harmless. No extra delta<1/2 hypothesis is necessary.

## Quantifier order and explicit uniformity

Fix D≥0 and delta>0. For M>0, put s=`M^(1/2+delta/2)`. One sufficient deterministic size threshold is

`M ≥ max(1, 24^(2/delta), (24D)^(1/delta))`.

Indeed `D ≤ M^delta/24` and `M^(delta/2) ≤ M^delta/24`, so `D+M^(delta/2) ≤ M^delta/12`. Therefore, from `d ≤ D sqrt(M)` and `r ≥ M^(1/2+delta)`,

`Delta ≥ M^(1/2+delta)/12 > 0`,

and the precise finite comparison bounds failure by `exp(-M^(2delta)/144)`. This threshold and bound depend only on D, delta, M, and do not depend on N, G, H, q, support of H0, or the graph law.

For `UniformGraphScan`, fix a>0, delta>0, D≥0, epsilon>0 first. Choose N0≥1 so that, for all N≥N0, `N^a` exceeds the preceding M threshold and `exp(-N^(2 a delta)/144) ≤ epsilon`. This yields one N0 valid simultaneously for every permitted H0 and G. One can separately export the uniform null bound `(N+1) exp(-N^(a delta))`, using `M≥N^a`. To make a total-variation epsilon estimate, additionally enlarge the same N0 so that this null bound is ≤ the desired error budget. Merely proving a threshold depending on H0, G, or a chosen translate would not meet the frozen quantifier order.

The boundary hypothesis in `UniformGraphScan` holds for all N+1 shifts, although the proof needs it only for a successful shift. Do not silently change the frozen statement; a selected-shift variant may be an additive helper. The source's informal D<infinity is naturally represented by a real D. The frozen D≥0 assumption is appropriate; for large M a negative D is incompatible with the stated nonnegative boundary cardinalities anyway.

## Least successful deterministic q and conditional law

For fixed N, H0, delta, let

`Q(G) = {q : Fin (N+1) | M^(1/2+delta) ≤ |G ∩ E(H_q)|}`.

Use the least member of this finite set when nonempty, and a fixed default q=0 when empty. The graph-success event guarantees the nonempty branch. Both the set and its least member depend only on G and fixed parameters. Since the graph space is finite, this is measurable for the discrete/full sigma-algebra. It must not inspect pi, component-sorted values, or whether an ascent test actually succeeds. Conditional on each G, the independently sampled pi remains uniform, so the uniform deterministic-graph failure estimate applies at this chosen H_q.

No generic PMF on permutations can be substituted for this conditional uniform pi. For example, in the edgeless two-position graph a point mass on the increasing permutation has X identically 1, and its unsorted ascent mean is not 1/2. Any graph-law theorem must either explicitly sample an independent uniform pi and push forward `(G,pi) ↦ componentSort G pi`, or assume a proved equality with that mixture. The actual shuffle equality remains an LB01/LB10 obligation, not an LB04 consequence.

For an arbitrary graph law rho and its explicit mixture P, the deterministic estimate implies

`P(scan) ≥ rho(graphSuccess) - exp(-M^(2delta)/144)`

above the uniform threshold. Together with the uniform-null estimate, the TV lower bound is

`tv(P, uniform) ≥ rho(graphSuccess) - exp(-M^(2delta)/144) - (N+1)exp(-M^delta)`.

This identifies exactly where the graph success probability and the actual-law representation are used.

## Independent-uniform-keys cross-check

Give each position an independent continuous uniform key and rank all N keys, which are distinct almost surely. By exchangeability every permutation of these ranks has probability 1/N!, recovering the uniform permutation. Relative ordering of disjoint position groups is a function of disjoint families of keys, hence these orders are independent. Component-pair boundary indicators use only keys in their two components; disjoint pairs within a parity class are therefore independent. Sorting component ranks agrees with sorting component keys. This independently reconstructs the parity argument and its constants without claiming independence of global ranks themselves. The no-ties and rank-uniformity steps must be included if this route is formalized; the finite exact-counting route avoids these continuous-probability obligations.

## Finite adversarial computation

An inline independent Python enumeration checked every path graph and every H for N=0,...,7: 10,923 graph/set cases. Each graph was realized by sorting every permutation within its interval components. Expectations were computed exactly as rational numbers and checked against `e/2+r/6-d`, with d counting infinite-path boundary edges. Both weak one-sided concentration inequalities were checked at all 12,791 distinct nonzero support-deviation endpoints using M=|H|. The exponential comparison used floating arithmetic with tolerance 1e-14; these checks are counterexample searches, not formal proofs. A first execution hit an older Python interpreter lacking `int.bit_count`; replacing popcount by `bin(x).count("1")` completed the enumeration successfully. Empty-H concentration is separately deterministic.

Checking deviation endpoints suffices for this finite search: between successive positive deviations the weak tail probability is constant and the exponential bound decreases toward the next support endpoint. No violating case was found. This supports the finite audit but does not discharge any Lean target.

## Required proof obligations retained

- Establish exact component-sort behavior from the shared `Tuple.sort` representation; the definitions alone do not prove the decomposition.
- Prove joint finite relative-order counting, its boundary-binomial corollary, and parity independence.
- Prove the centered Bernoulli MGF, Cauchy–Schwarz combination, and both one-sided Chernoff bounds with the frozen constant.
- Prove partial-component and double-charging counts while retaining internal edges of partial components.
- Prove clipping cardinality and exact scan union indexing, preserving strict scan versus weak failure.
- Define and prove the graph-only least successful q and make eventual thresholds uniform in the prescribed order.
- Keep any mixture representation conditional until the concrete checked upstream export discharges it.

No target or assumption change is requested by this review.
