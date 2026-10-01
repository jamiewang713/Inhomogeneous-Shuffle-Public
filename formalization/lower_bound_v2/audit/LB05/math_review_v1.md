# LB05 independent mathematical review, version 1

Date: 2026-10-01. Reviewer: independent `lb05_math_review` agent.

Scope: the argument at `lem:cold-witness`, its empirical and one-column definitions, the assigned LB05 prompt, and the frozen `OneColumnTiltTarget`, `EmpiricalTiltTarget`, `ColdWitnessTarget`, and `WitnessSpec`. This is a mathematical review, not a checked Lean proof or a build receipt. Only this new report was written.

## Verdict

The frozen LB05 targets are mathematically consistent with the authoritative source. I found no false inequality, missing substantive hypothesis, or counterexample. In particular, the theta=4 move does not need a length bound; terminal clipping has ample uniform slack; deterministic and zero coordinates cause no obstruction. The implementation must prove the boundedness facts for real infima/suprema and the endpoint and column-counting details below. Existing target predicates do not provide those proofs.

No contract change is recommended. The remaining obligations described here are proofs of the existing statement, not proposed assumptions.

## Reviewed snapshot

```text
672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d  time_inhomogeneous_riffle_shuffle_unified_article.tex
bbd3f28678e95ace37f07c0d993992f20fd4dc4d565ccbc11d0b8a4f1ba822bc  Contracts/v1/WitnessGeometry.lean
cb992d0297bcf75ada15ff6154a146caadfa3d984629aafd70f74feef6bfbb09  RiffleLowerV2/Shared/Geometry.lean
84ea013c6f9c64073700be1dced470f11fa30a9b3d0b79a59dde63a099cf817e  RiffleLowerV2/Shared/Empirical.lean
```

The LB00 `CONTRACT_READY.md` receipt was inspected. Its release distinguishes pending targets from the checked shared foundation. This review preserves that distinction.

## One-column argument, including the boundary of the simplex

Write `C = log k > 0`, `a = log(1/pmax)`, `Z(alpha) = sum p_i^alpha`, and `q_i = p_i^alpha/Z(alpha)`. For alpha at least one, the support of q equals the positive support of p. The denominator is positive since a simplex has at least one positive coordinate. At a zero coordinate the numerator and every weighted log contribution are zero. Work on positive support when differentiating or taking logarithms.

The exact formulas are

```text
I(alpha) = sum q_i log(1/p_i)
H(alpha) = alpha I(alpha) - psi(alpha)
I'(alpha) = -Var_q(log(1/p_i)) <= 0.
```

The finite formulas are continuous in alpha on `[1,4]`. Monotonicity on `[1,4]` gives `I(alpha) <= I(1) = H(p) <= C`. Although the target only requests alpha in `[2,4]`, a proof based on comparison with one needs a helper valid down to alpha=1; it cannot infer the comparison from antitonicity on `[2,4]` alone. This is a helper-domain obligation, not a missing target hypothesis.

Nonnegativity of the coordinate costs gives `I >= 0`; nonnegativity of entropy gives `H >= 0`. Gibbs' inequality yields `H <= I`. Since every positive coordinate has `log(1/p_i) >= a`, averaging gives `a <= I`. The power-sum bounds `k^(1-alpha) <= Z(alpha) <= 1` give the sharper required `0 <= psi(alpha) <= (alpha-1) C`. Finally,

```text
Z(2) >= pmax^2               => psi(2) <= 2a <= 2I(alpha),
Z(4) <= Z(2)^2               => psi(4) >= 2psi(2).
```

The last power-sum inequality follows by expanding the square and retaining diagonal terms. It holds without strict positivity. A deterministic column has `a = I = H = psi = 0` at every relevant tilt. Plateaus in J therefore occur and are permitted: the proof uses continuity and the intermediate value theorem, never strict monotonicity or uniqueness.

## Empirical interpolation and the variational starting point

For `L=log N>0`, `S=K/L`, the frozen clipped column fractions produce exactly the integral of the finite empirical step function, including zero extension outside `[0,S]`. Their weights on `[r,s] subset [0,S]` are nonnegative and have total `s-r`. Thus the one-column bounds give all needed interval bounds, continuity in endpoints, additivity, and continuity/antitonicity in alpha. At grid endpoints, the result is the normalized sum over zero-based columns `[a,b)`.

The triangular domain contains `(0,0)` because `S>=0`; `[3,4]` is nonempty. For example, on these domains,

```text
abs(F_alpha(s,u)) <= (7/2)(1+S C) + 5S C.
```

This supplies boundedness below and above for the image sets defining both real infima and the real supremum. It should be established before applying conditional-completeness order lemmas. Since `lambda1 >= eta > 7eta/8`, the supremum property gives a pair whose infimum is strictly greater than `7eta/8`; each F value is at least that infimum. No supremum/infimum interchange is involved and no attainment theorem is required. Continuity plus compactness would also work, but is unnecessary for selecting this slackened value.

At the selected `(s0,u0)`, nonnegative B terms and the alpha=4 bound give

```text
(7/2)b0 >= 7eta/8, hence b0 >= eta/4 = 250kappa.
```

Consequently `b0/2-4kappa > 0`.

## Tilt selection and the potentially long theta=4 move

There are precisely three cases.

1. If `J3(s0,u0) <= b0/2`, choose theta=3.
2. Otherwise, if `J4(s0,u0) >= b0/2`, choose theta=4.
3. Otherwise, continuity in alpha on `[3,4]` gives a theta in `(3,4)` with `Jtheta(s0,u0)=b0/2`. Monotonicity verifies the orientation of the endpoint values; strict monotonicity is unnecessary.

If the chosen J is already at most `b0/2-4kappa`, leave u unchanged. This can happen only in case 1. Otherwise continuity of the endpoint integral, its value zero at s0, and the positive target value give `u1 in [s0,u0]` with

```text
Jtheta(s0,u1) = b0/2-4kappa.
```

For theta=3 and for the interior case, the removed J is at most `4kappa`. Hence

```text
Ftheta(s0,u1)-Ftheta(s0,u0)
  = Btheta(u1,u0)-2B2(u1,u0)
  >= -4Jtheta(u1,u0)
  >= -16kappa.
```

For theta=4, the exact same difference is nonnegative because `psi4 >= 2psi2` pointwise. The removed J and the time displacement may both be large; bounding either by `4kappa` in this branch would be a false intermediate claim. The source does not make that error. Every branch gives

```text
Ftheta(s0,u1) >= 7eta/8-16kappa = 859kappa.
Jtheta(s0,u1)-b0/2 <= -4kappa.
theta = 3 or Jtheta(s0,u1)-b0/2 = -4kappa.
```

## Terminal clearance and explicit uniform error budget

Let `rb=2rho` and `bN=ceil(rb L)`. A sufficient eventual choice is

```text
L >= max(1, 1000 C/kappa, 4/(density*rho)).
```

All quantities on the right are fixed before the cuts are quantified. Increasing a natural `N0>=2` until this holds for every `N>=N0` gives a threshold uniform over the cut array. No limit assumption on the actual columns, tilted observables, or a macroscopic profile is involved.

The beta difference protects the starting endpoint:

```text
(S-s0) C >= A(s0,S)
             = b0-beta(S)
             > eta/4-kappa0
             >= 249.99 kappa.
```

In contrast, `(rb+2/L)C <= 0.012 kappa` under the budget above. Thus `s0 < S-rb-2/L`. This implies `K>=bN` and shows that

```text
ms = floor(s0 L),
mu = min(floor(u1 L), K-bN)
```

satisfy `ms<=mu` and `mu+bN<=K`, including the natural-subtraction side condition. It is unsafe to omit this step and rely only on `s0<=u1`: clipping can otherwise move mu below ms.

The resulting endpoint displacements satisfy

```text
0 <= s0-s < 1/L,
0 <= u1-u <= rb+2/L.
```

The manuscript's safe bounds are valid:

```text
abs(Delta F)       <= 5rb C + 20C/L <= 0.07kappa < kappa/10,
abs(Delta(J-b/2))  <= rb C + 4C/L  <= 0.014kappa < kappa/10.
```

For example, summing the absolute endpoint contributions gives the sharper coefficients `(13/2)C` at s and `5C` at u for F, and `(3/2)C` at s and `C` at u for `J-b/2`; the displayed source bounds dominate these. Signed additivity avoids any difficulty if rounding produces `u<s0` while still `s<=u`.

The remaining margins are therefore stronger than required:

```text
Ftheta(s,u) >= 858.9kappa > eta/2,
J-b/2 <= -3.9kappa < -3kappa,
theta = 3 or J-b/2 >= -4.1kappa > -5kappa.
```

## Good bridge columns and endpoint loss

The frozen `LocalGood` quantifies every real starting point a with `0<=a` and `a+rho<=T`. It does not require a to be a source-grid point. A simpler implementation than the source-grid sentence is therefore available: apply it directly to `[u,u+rho]`. Clearance gives `u+2rho<=S<=T`.

This interval contains at least `density*rho*L>=4` good column times. The bridge contains all of these except possibly the column at exactly u. There is at most one such column because `columnTime N j=(j.val+1)/L` is injective when L>0. After deleting it, at least three, in particular two, good columns remain. Their zero-based indices satisfy

```text
mu <= gL.val < gR.val < mu+bN.
```

This is exactly `WitnessSpec`; the manuscript's one-based bridge is `mu<j<=mu+bN`. No second endpoint loss is needed: the upper end `u+rho` lies strictly before `u+2rho<=u+bN/L`. If retaining the source-grid proof, its complete interval also loses at most one column at the bridge's open left endpoint.

## Exact final algebra

Write the final quantities exactly as in `WitnessSpec`. The entropy identities yield

```text
2Gamma-h = 3b+(theta-3)J-Btheta(s,u)-2B2(u,S)
         = Ftheta(s,u)+(theta-3)(J-b/2).
```

If theta=3 the correction is zero; otherwise the lower J condition and `0<=theta-3<=1` give a correction at least `-5kappa`. Consequently

```text
Gamma-h/2 >= (eta/2-5kappa)/2 = 247.5kappa >= kappa.
```

Because `0<=H<=J` and `J<=b/2-3kappa`, one obtains `b>=6kappa`,

```text
H <= b-J-6kappa <= b-J-kappa,
h = b-J+H >= b-J >= b/2+3kappa >= kappa.
```

Finally, the one-column comparison `a<=I` and additivity give

```text
b-J-Jt <= 1-A(0,s)-A(s,u)-A(u,S) = beta(S) < kappa0.
```

All formulas remain valid for empty selected intervals and for columns with zero coordinates. An entirely deterministic cut sequence cannot satisfy the cold terminal premise because then beta(S)=1 whereas kappa0<=1/1000; that case is vacuous rather than a singularity in the argument.

## Implementation-facing proof ledger

| Obligation | Mathematical status | Required proof content |
|---|---|---|
| One-column bounds and identities | Valid | Positive support, positive denominator, entropy bound, Gibbs inequality, power sums |
| Antitonicity of I | Valid | Derivative/variance proof on `[1,4]`, or an equivalent finite comparison |
| Empirical endpoint and alpha properties | Valid | Finite fraction weights, exact total length, additivity and continuity |
| Real variational selection | Valid | Nonempty triangle and tilt interval, explicit bounded image sets |
| Three tilt cases and shortening | Valid | IVT; theta=4 uses `psi4>=2psi2` with no displacement estimate |
| Uniform rounding and terminal clearance | Valid | Beta difference, floor/ceiling inequalities, natural-subtraction side conditions |
| Two good bridge columns | Valid | LocalGood on `[u,u+rho]`, injectivity of column times, at most one discarded column |
| Final geometry and mean comparison | Valid | Exact entropy identity and linear arithmetic |

These proofs have not been implemented or compiled by this reviewer. Mathematical approval must not be reported as successful Lean completion.
