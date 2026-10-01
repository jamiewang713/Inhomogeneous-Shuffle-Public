# LB09 independent mathematical review v1

Date: 2026-10-01. Scope: read-only mathematical review of the three assigned manuscript lemmas, their prerequisites, shared geometry, and frozen targets. This report is the only file written by this reviewer. No Lean implementation or kernel certification is claimed here.

## Verdict

The mathematical conclusions are supportable with the current assumptions and frozen definitions. No target change is mathematically required. The proof must retain the ambient term in the right endpoint identity, recover the stronger entropy slack from the empirical tilt inequalities, and explicitly control integer rounding and the fixed good-column factors. A single existing simultaneous prefix event suffices for both endpoint and reserve estimates; this improves the event bookkeeping without changing any target.

References below use `paper` for `time_inhomogeneous_riffle_shuffle_unified_article.tex`, `Geometry` for `RiffleLowerV2/Shared/Geometry.lean`, and `Targets` for `Contracts/v1/WitnessGeometry.lean`.

## Assumptions and uniformity contract

Keep `k >= 2`, `T, eta, rho, chiGood > 0`, `kappa = eta/1000`, `kappa0 = min(kappa/100, 1/1000)`, and the additional bridge budget `2*rho*log k <= kappa0/100`. The bridge has the natural length `ceil(2*rho*log N)` and the real ambient exponent is `b`; these are distinct objects.

For deterministic geometry, choose `xi > 0` small enough and a regular partition `P` before choosing the eventual threshold. Set the type approximation budget to the frozen value `delta = min(kappa,kappa0)/1000`. First choose xi so that `Ctype*T*xi*log(1/xi) <= delta/2`; then choose N0 so that the rounding rate is at most delta/2 for this fixed P. The N0 must precede all cut arrays and all witnesses. This is exactly the order in Targets:100–110. For localization, the additional probability tolerance precedes N0, as in Targets:31–39. No rate of changing xi or P with N is needed.

The witnesses may depend on N and the deterministic cut array. No witness, selected bin, bridge, or cold set may depend on the sampled shuffle matrix. Existing `WitnessSpec` and `GeometrySpec` have the appropriate deterministic data separation.

## Review findings and resolutions

### 1. Use the stronger empirical entropy slack

Paper:3419–3425 cannot be justified by merely perturbing the displayed weak witness inequality `H <= b-J-kappa` in paper:3162 or Geometry:61. Positive type error could consume that entire margin. The needed stronger bound follows from `H <= J` and `J <= b/2-3*kappa`:

`H + J <= 2J <= b-6*kappa`.

The paper establishes this explicitly at 3231–3232. For the prefix approximation errors `dJ = Jp*-J`, `dH = Hp*-H`, `|dJ|+|dH| <= delta` gives

`ellp >= b/2+3*kappa-delta >= b/2+2*kappa`,

`Hp* + Jp* <= b-6*kappa+delta <= b-kappa`.

Also `|hN-h| <= delta`, so `hN >= kappa/2`. Obtain `H <= J` from the checked empirical tilt theorem, not an additional assumption in LB09. This is an implementation obligation rather than a false source theorem.

### 2. Exact integer geometry supports the frozen constants

Paper:3427–3444 and Geometry:192–200 correctly use a union of half-open intervals. Distinct selected suffix words give disjoint probability intervals, but adjacent selected intervals may merge into one connected component. Never identify the selected-word count with the component count.

Let `Pcard = N^Hp*`, `Q = N^ellp`, and `M = |Hrel|`. Each selected interval has length in `(exp(-1)*Q,Q]`; its integer count differs from its length by at most 2. Thus

`Pcard*(exp(-1)*Q-2) <= M <= Pcard*(Q+2)`.

For `Q >= max(2, 2/(exp(-1)-exp(-2)))`, this proves the frozen finite bounds

`exp(-2)*N^hN <= M <= 2*N^hN`.

The remaining cardinality bounds are uniform. Since `hN >= kappa/2`, `log N >= 12/kappa` implies `N^(kappa/3) <= M`. Since all relative intervals lie in `[0,N*lambda_a)`, and `lambda_a <= 1`, the integer union is contained in `{0,...,N-1}`, proving `M <= N` without asymptotics.

For the boundary, the union contributes at most `2*Pcard`, and clipping a translate to `[1,N]` costs at most 2 more boundary edges. The lower cardinality bound gives

`Pcard/sqrt M <= exp(1)*N^((Hp*-ellp)/2) <= exp(1)*N^(-kappa/2)`.

Once `log N >= 2/kappa`, `Pcard <= sqrt M`. As `M >= 1`, `2*Pcard+2 <= 4*sqrt M`, exactly Geometry:271. This covers empty individual lattice intervals and merging; large N additionally rules out empty selected lattice intervals if needed.

### 3. Bridge construction and fixed constants are correct

Paper:3446–3456 specifies two ordered good columns. At the left one choose the larger good digit; at the right one choose the smaller good digit; elsewhere choose a maximizing digit. The minus reserve changes only the left distinguished column, and the plus reserve changes only the right distinguished column. Their first differences prove strict lexicographic order, independently of the tail.

All three bridge masses are at least `chiGood^2*k^(-bridgeLength)`. The sharper bound with `k^(-(bridgeLength-2))` is unnecessary. Do not mistakenly count the unchanged distinguished column as a maximizing column. Existence of a good column implies `chiGood <= 1`, so the logarithmic estimates have the expected signs.

The explicit bridge exponent bound is

`0 <= ellb <= 2*rho*log k + (log k + 2*log(1/chiGood))/log N`,

matching Geometry:239–243. In particular fixed factors involving chiGood cannot be discarded before choosing N0. Every reserve prefix has the concrete lower mean

`mu_reserve >= exp(-1)*chiGood^2*k^(-1)*N^(ellp-2*rho*log k)`.

Since `ellp >= b/2+2*kappa`, its comparison with `N^(b/2+kappa)` follows whenever

`(kappa-2*rho*log k)*log N >= 1 + 2*log(1/chiGood) + log k`.

The coefficient on the left is positive by the bridge budget. This threshold is independent of cuts, selected words, and witness locations. The common digit bound is exactly `min(xi, min(chiGood,1/k)) > 0`, matching Geometry:258 and 279–286.

### 4. Collision exponents survive bridge deletion

Let `dpJ,dpH,dtJ,dtH` be the errors in paper:3484–3493. Set `d=(2*rho+1/log N)*log k`, with deleted bridge costs `0 <= dJ,dH <= d`. Then the exact subtraction is

`gN-hN/2 = Gamma-h/2 + 2*dJ-dH-2*ellb - (3/2)*dpJ + (1/2)*dpH - 2*dtJ + dtH`.

The manuscript's bound by `Gamma-h/2-7*delta-d-2*ellb` is conservative and valid; using the two sum-of-errors budgets even gives `-(7/2)*delta` in place of `-7*delta`. For sufficiently large N, `d,ellb <= kappa0/50`, yielding `gN-hN/2 >= kappa/2`. Likewise `zN <= b-J-Jt+2*delta+d < 2*kappa0`. No lower bound on zN is required.

Injectivity of concatenation on the disjoint prefix and tail coordinate sets gives `|Y|=N^(Hp*+Ht*)`. Multiplication of the two strict mass-bin lower bounds and the exact bridge/ambient masses gives `exp(-2)*N^zN < N*lambda_y <= N^zN`, including an empty prefix or tail position set.

### 5. Both side-cylinder endpoint identities are exact

Paper:3544–3571 and Targets:78–98 are mathematically correct. Split suffixes by their first differing coordinate. Left cylinders partition the suffixes smaller than x; right cylinders partition the suffixes larger than x inside the ambient a-cylinder. Therefore

`Lrel-muA*tx = sum_left (C(v)-mu(v))`,

`Urel-muA*(tx+mass(x)) = (C(a)-muA)-sum_right (C(v)-mu(v))`.

The ambient fluctuation in the second line is indispensable. It remains the only term when the suffix is empty. On each side, the cylinders are mutually disjoint and lie inside a, their number is at most `k*K`, and their mean sum is at most muA. Cauchy–Schwarz gives `sum sqrt(mu_j) <= sqrt(k*K)*sqrt(muA)`. Adding the two sides and the ambient deviation yields precisely

`A*((2*sqrt(k*K)+1)*sqrt(muA)+2*k*K+1)`.

No division by muA occurs, so zero or small means are covered. The frozen target also permits N=0; handle it separately (all counts and means vanish), rather than assuming normalization of the ratios `count/N` at N=0. For N>0 the per-column masses sum to one. Empty suffixes have tx=0 and mass=1, so both identities reduce correctly. The `sidePrefix` definition at Geometry:323–326 includes later x coordinates in its carrier full word, but `prefixAt(j+1)` removes them and gives exactly the desired side cylinder.

### 6. A single prefix event is sufficient

Preferred proof strategy: use the actual `allPrefixEvent (kappa/4)` for both endpoints and reserves. The same simultaneous event already controls every reserve prefix at every length, so no extra event and no independence claim are needed.

From `Jp* >= 0` and `ellp >= b/2+2*kappa`, derive `b >= 4*kappa` (paper:3601–3603). Set

`eN = N^(kappa/4)*((2*sqrt(k*K)+1)*N^(b/2)+2*k*K+1)`.

As `K <= T*log N`, a sufficient uniform finite condition for `eN <= N^(b/2+kappa/2)` is

`2*sqrt(k*T*log N)+2*k*T*log N+2 <= N^(kappa/4)`.

For every reserve mean mu, geometry gives `mu >= N^(b/2+kappa) >= N^(3*kappa) >= 1`. On the prefix event,

`C >= mu-N^(kappa/4)*(sqrt(mu)+1) >= mu-2*N^(kappa/4)*sqrt(mu)`.

Thus `N^(5*kappa/4) >= 4` implies `C >= mu/2` simultaneously for every reserve. Once `N^(kappa/2) >= 4`, the stronger mean exponent also gives `mu/2 >= eN+2` (the factor `N^(b/2+kappa/2)` is at least `N^(5*kappa/2)`). These are uniform deterministic thresholds.

The exact failure estimate is the already-proved polynomial union bound

`P(not allPrefixEvent(kappa/4)) <= 2*(K+1)*k^K*exp(-N^(kappa/4)/8)`

`<= 2*(T*log N+1)*N^(T*log k)*exp(-N^(kappa/4)/8)`.

It tends to zero uniformly in cuts and witnesses. The same event and same N0 can even handle every deterministic witness/geometry satisfying the assumptions simultaneously. The source's separate reserve-event route is also valid: for a fixed deterministic witness, at most `2*k^K` selected reserve prefixes give additional failure at most `2*N^(T*log k)*exp(-cCh*N^(3*kappa))`. This estimate does not assume independence between reserves. If unioning over all witness lengths via this latter route, one must include the length factor; the single-prefix-event route already does so.

### 7. Rank conventions, tails, and injection into edges

For fixed selected x, put `ell=muA*tx`, `r=muA*(tx+mass(x))`, and `q=lowerRank(a)`. Every row with prefix `a x central`, for every possible tail z, has one-based rank i satisfying

`q+Lrel+Cminus+1 <= i <= q+Urel-Cplus`.

Endpoint errors at most eN and reserve counts at least eN+2 imply `q+ell < i < q+r`. Therefore `i-q` is in the integer half-open interval `[ell,r)`. This agrees with the actual shared definition `manuscriptRank(i)=i.val+1` and `clipTranslate` in Shared/Path:12,25–26; using `i.val` directly would introduce an off-by-one error.

The proof applies to all z on the already fixed event. It needs neither a union bound over tails nor stochastic independence of tail columns, and it needs no distributional control of the random q.

For a full word with count at least 2, choose the path edge joining its first two sorted copies. Both endpoints lie in the clipped cold set, and the equal-word condition puts the edge in `shuffleEdges`. Equal chosen edges force equality of their sorted left words, proving injectivity. The old `RiffleLower.localized_collisions_supply_edges` implements this combinatorial argument under `localizedKeys`; it is usable only after that hypothesis has been proved for the actual cold family, and requires conversion from ordered vertex pairs to the shared `Fin(N-1)` edges. A direct shared-representation proof is equally valid.

## Proposed exports and dependency ledger

The final lane should prove the existing, unchanged exports (names below proposed in namespace `RiffleLowerV2.Localization`):

| Export | Exact target | Source | Mathematical status |
|---|---|---|---|
| `relativeEndpoint` | `Targets.RelativeEndpointTarget` | `lem:finite-relative-endpoints` | Sound, with N=0 branch and ambient term |
| `deterministicColdGeometry` | `Targets.DeterministicColdGeometryTarget` | `lem:cold-geometry` | Sound, actual construction required |
| `localization` | `Targets.LocalizationTarget` | `lem:localization` | Sound, single prefix event suffices |
| `coldGeometryFromEmpirical` | `Targets.ColdGeometryFromEmpiricalTarget` | combined construction and localization | Sound after all inputs discharged |
| `lB09` | `Targets.LB09Target` | all assigned obligations | Pending implementation, not implied by this report |

Useful lane-local proved helpers should expose exact first-differing-digit partitions, their weighted mass identities, disjoint half-open integer cardinality bounds, at-most-two-boundaries per interval, concatenation injectivity, the two reserve rank barriers, and the deterministic implication from the shared all-prefix event to `ColdLocalization`. None should accept localization, reserve counts, or geometric conclusions as a final external premise.

The upstream mathematical declarations inspected are concrete: `Witness.coldWitness` in Witness/Main:10–34; `Witness.empiricalTilt` through Witness/Main:3,38; `Types.roundedType` in Types/Main:12–26; `Thinning.prefixTails` and `Thinning.allPrefixConcentration` in Thinning/Prefixes:62–72. Receipts `audit/LB05/LB05_READY_v1.json`, `audit/LB06/COMPLETION_v1.md`, and `audit/LB02/LB02_READY_v1.json` state completion and standard axiom closure. The older `asymptotic_allprefix_receipt_v1.json` documents only a conditional helper and must not be mistaken for the final LB02 receipt. Final dependency hash verification and the LB00 interface receipt remain the coordinator's responsibility.

No external citation is needed for this review: all substantive mathematical inputs are explicit in the authoritative manuscript or checked project interfaces. There are no unresolved mathematical counterexamples in the reviewed scope. Implementation and independent final kernel/representation audits remain pending.
