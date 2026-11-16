# LB05 independent missing-hypotheses and counterexample review, v1

This review tests the finite empirical witness against degenerate columns, terminal witnesses, endpoint conventions and uniformity. It approves the frozen mathematical statement for implementation; it does not certify an unimplemented Lean proof.

## Inspected source and identity

The authoritative manuscript was inspected at `lem:cold-witness`, the preceding empirical-cost definitions and one-column inequalities, and `def:good-columns`. The inspected Lean definitions are `Contracts/v1/WitnessGeometry.lean`, `Shared/Empirical.lean`, `Shared/Geometry.lean`, and the imported `TimeProfile` definitions of `Simplex`, costs, column times and `LocalGood`. The LB00 foundation receipt was read. Historical `Analysis.lean`, `AnalyticParameters.lean` and `RiffleLower/Cold.lean` were checked for the distinction between available helpers and the actual target.

| File | SHA-256 |
| --- | --- |
| authoritative manuscript | `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d` |
| `Contracts/v1/WitnessGeometry.lean` | `bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc` |
| `Shared/Empirical.lean` | `84ea013c6f9c64073700be1dced470f11fa30a9b3d0b79a59dde63a099cf817e` |
| `Shared/Geometry.lean` | `cb992d0297bcf75ada15ff6154a146caadfa3d984629aafd70f74feef6bfbb09` |

No mathematical counterexample to the frozen LB05 target was found. No new premise, macro temporal regularity or contract amendment is needed. The open items are proofs and APIs, not repairs of the target.

## Degenerate columns

For a deterministic simplex point, every cost `a`, `psi(alpha)`, `I(alpha)` and `H(alpha)` is zero for alpha in [2,4]. The zero coordinates have zero tilted weight and are excluded from logarithmic cost terms. The positive support is nonempty because the coordinates sum to one. Thus all stated one-column inequalities and exact entropy identities remain valid; strict positivity of every pile is neither necessary nor permitted as a silent extra assumption.

For a general point with zero coordinates, restrict calculations to the fixed positive support. There the power-sum denominator is strictly positive and real powers are smooth in alpha. This proves continuity and the variance derivative for I without differentiating a logarithm at zero. The support argument also covers a column with several equal positive coordinates: I is constant in alpha and monotonicity is non-strict.

The bounds `H <= I <= log k`, `a <= I`, `psi(2) <= 2a`, and `2 psi(2) <= psi(4)` are consistent with all these cases. The last inequality follows from `sum p_i^4 <= (sum p_i^2)^2`; it is especially important that its direction is this one. No uniform positive lower bound on nonzero coordinates is used.

An entirely deterministic cut array has beta(S)=1, so it fails the frozen cold-branch terminal hypothesis. It is therefore not a counterexample. Mixed deterministic columns remain allowed and may make endpoint cost functions locally constant; the shortening argument uses continuity and the intermediate value theorem, not strict monotonicity or a positive derivative.

## Tilt selection and a long theta=4 move

The three source branches are consistent: theta=3 when J3 <= b0/2; theta=4 when J3 > b0/2 and J4 >= b0/2; otherwise an interior tilt has Jtheta=b0/2. Antitonicity and continuity are enough; equality at theta=4 is covered by that branch.

When shortening J to b0/2-4 kappa, the theta=3 and interior branches lose at most 4 kappa of J and therefore at most 16 kappa of F. In the theta=4 branch the decrease in J can be arbitrarily large. The exact difference is the integral of `psi4-2 psi2`, which is nonnegative. Any proposed proof assuming an O(kappa) backward displacement in this branch would be invalid, but the frozen statement and manuscript do not assume it.

## Terminal clearance and rounding constants

Write ell=log k, L=log N, rb=2 rho. The initial witness satisfies F4 >= 7 eta/8, hence b0 >= eta/4. The terminal hypothesis gives

`(S-s0) ell >= A(s0,S) = b0-beta(S) > eta/4-kappa0`.

Since kappa0 <= kappa/100 and eta=1000 kappa, the right side is at least 249.99 kappa. Meanwhile rb ell <= kappa/100. Thus a witness apparently born near S is actually separated from S by far more than the reserved bridge length, uniformly in the cuts. In particular, after taking L sufficiently large, `s0+rb+2/L<S`. Clipping the rounded upper index to `K-ceil(rb L)` cannot take it below the rounded lower index.

The floor/ceiling errors give `0 <= s0-s < 1/L` and `0 <= u1-u <= rb+2/L`. The source bounds are conservative and valid:

`|F(s,u)-F(s0,u1)| <= 5 rb ell+20 ell/L`,

`|(J(s,u)-b(s)/2)-(J(s0,u1)-b0/2)| <= rb ell+4 ell/L`.

For example the cut-independent condition `L>400 ell/kappa` makes the first error strictly less than kappa/10 and the second strictly less than kappa/50. It also supplies the terminal clearance above. These are genuine eventual thresholds, with no dependence on the particular selected s0,u1,theta or cut array.

The retained upper gap and nonnegativity of J imply b>=6 kappa, so the final deduction h>=b/2+3 kappa>=kappa does not need an unrecorded positivity premise on b. The exact identity is

`2 Gamma-h = Ftheta+(theta-3)(J-b/2)`.

For theta=3 the extra term vanishes. Otherwise theta-3 belongs to [0,1] and J-b/2>=-5 kappa, so the extra term is at least -5 kappa. This checks both signs and all constants in the collision gap.

## Good bridge columns and endpoint loss

Lean column j has source time `(j.val+1)/L`, whereas the bridge uses zero-based indices `mu <= j.val < mu+bN`. Thus source-time membership is precisely `mu/L < columnTime j <= (mu+bN)/L`. The closed interval used by `LocalGood` may include the column at the left endpoint; at most one column has that time. Losing one column is enough, with no loss at the right endpoint.

The frozen `LocalGood` quantifies over every real interval `[a,a+rho]` in [0,T], not merely rho-grid intervals. One may therefore apply it to `[u,u+rho]` and subtract at most one column, or to the interior interval `[u+rho/2,u+3rho/2]`, which has no endpoint loss. Both are contained in the bridge since bN/L>=2 rho and bridge clearance has already been proved. The weaker manuscript argument using a complete rho-grid interval is also sound.

Taking `density*rho*L>3` leaves more than two good columns after the possible one-column loss. Positivity and fixedness of rho and density are essential to selecting N0 before the cuts. The exact target already supplies these conditions. The horizon `floor(T L)/L` is at most T, so applying `LocalGood` on [0,T] does not require a hypothesis beyond the recorded one.

## Parameter and quantifier stress tests

The frozen order is correct: k,T,eta,rho,chiGood,density are fixed; then N0 is chosen; then N and every cut array are quantified; then the witness is constructed. The explicit bounds above depend only on the fixed constants. No temporal regularity, almost-profile premise, supplied witness existence, or assumption naming the desired conclusion enters this order.

No upper bound on eta, chiGood or density is missing. In infeasible parameter regimes there simply are no cut arrays satisfying all premises. In particular the empirical margin bound itself bounds any feasible eta. Likewise no separate rho<T premise is needed: the beta-difference clearance and mesh budget force enough time whenever the substantive hypotheses hold.

The positivity conditions cannot be deleted indiscriminately. With rho=0 the bridge has length zero and cannot contain two columns, while `LocalGood` becomes vacuous. Uniform binary columns with terminal cost near 1.1 have beta near -0.1 and empirical cold margin at least 0.8, so this would be a real false variant. With density=0, choosing chiGood=1 makes the local condition vacuous even for uniform binary columns and there are no good columns. These variants are excluded by the current contract.

## Implementation obligations still requiring proof

- Actual one-column continuity, antitonicity, sharp psi bound and entropy identities, including zeros.
- Endpoint continuity and uniform Lipschitz estimates for the frozen finite-step interpolation.
- Nonempty, bounded alpha images and time triangle before real sInf/sSup extraction.
- Rounding arithmetic, terminal clearance, good-column extraction and one uniform N0.
- Concrete construction of `ColdWitnessData` satisfying every `WitnessSpec` conjunct.

Historical scalar cold-geometry identities and the LB00 foundation receipt do not themselves discharge these obligations. An abstract lemma assuming a witness specification would be useful only as a helper, not as completion of LB05.
