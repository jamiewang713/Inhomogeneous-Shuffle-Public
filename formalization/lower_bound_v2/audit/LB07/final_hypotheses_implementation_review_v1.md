# LB07 independent final implementation/hypotheses review, v1

Date: 2026-10-01. Reviewer scope: parent-owned `Endpoint.lean`,
`Parameters.lean`, and `Main.lean`; the completed `Quadrature.lean`,
`Margin.lean`, and `Extrema.lean`; and the unchanged frozen LB07 targets.
I also inspected `Empirical.lean`, the compatibility quadrature/counting
proofs, and their provenance. I authored Spatial and therefore do not count
my own Spatial receipt as its independent implementation review.

**Verdict: accept the implementation's mathematics and assumption closure.**
No new hypothesis, changed target, hidden regularity, or mathematical defect
was found. This review supports the exact four named exports below. At the
time of the source review, Endpoint, Parameters, Quadrature, Margin, Spatial,
and Empirical have successful private lane logs; the root's aggregate Main
build and aggregate `collectAxioms` check are the final separate verification
receipts. This report does not claim their outcome before those logs exist.

## Exact endpoint interfaces

The declarations are under `RiffleLowerV2.ProfileTransfer` and their stated
types are literally the frozen target predicates, with no additional theorem
parameters:

```
genericQuadrature   : RiffleLowerV2.Targets.GenericQuadrature
jointPsiContinuity  : RiffleLowerV2.Targets.JointPsiContinuity
marginTransfer     : RiffleLowerV2.Targets.MarginTransferTarget
profileTransfer    : RiffleLowerV2.Targets.ProfileTransferTarget
```

`profileTransfer` constructs its A/B error proof with `genericQuadrature` and
then passes that constructed proof to `marginTransfer`. It does not assume
either conclusion or an unproved target. The four typed examples in the
root's `Check_v1.lean` check the literal interface matches, and its environment
traversal checks all lane public/private declaration axiom closures.

## Endpoint interpolation and finite quadrature

`gridTime_floor_bounds` uses the positive log and the exact floor bound. Its
rounded endpoint remains in `[0,S]`; the construction works at zero horizon.
The filter identity in `empiricalIntegral_sample_error` matches source column
`j.val+1` exactly: `r<columnTime≤s` becomes
`floor(rL)≤j.val<floor(sL)`. Thus the corresponding normalized sum is the
frozen grid integral, and moving the two endpoints costs at most `2M/L`.
The normalization by L is neither missing nor duplicated.

The two-sided proof applies the genuinely proved historical lower bound to
f and its complementary observable `M-f`. It proves spatial integrability
from continuity and boundedness before rewriting the complementary spatial
integral as `M-∫f`. It restricts the own-observable temporal-integrability
premise before splitting the complementary time integral. The total column
count error contributes at most `M/L` in the reverse direction. Adding the
endpoint interpolation therefore costs `3M/L` beyond the old error.

Clipping the effective oscillation to `min(omega,M)` is justified by
`0≤f≤M`; it permits
`min(omega,M)+M+2Mm≤4Mm`. The proof derives `m≥1` from the probability measure
and the classifier, so no extra k or nonempty-simplex assumption is imposed
on the generic target. Its algebra explicitly retains `Mm phi T`, dominates
the complete-block count by `T/rho+2`, and gives exactly the frozen budget

```
2T omega + Mm phi T + 4M rho + [4Mm(T/rho+2)+6M]/L.
```

The closed-to-half-open discrepancy and up to two incomplete blocks remain
in the checked compatibility proof. The complementary route is more general
than the selected-cell temporal premise: `genericQuadrature` leaves that
premise unused. This is logically valid and does not silently change the
frozen interface. It does not infer integrability from AlmostLike; its own
observable time-integrability premise is essential and actually used.

## Margin constants and variational domains

`common_F_error` has exactly `7/2+1+2=13/2` times e on the common terminal
horizon. `macroF_bound` and `empiricalF_bound` establish the uniform absolute
bound `4+20*T*log k`. It is sufficient with the available coarse bound
`psi≤4log k`. `[3,4]` contains 3, and every nonnegative time triangle contains
`(0,0)`, including a zero empirical horizon.

`alphaInf_bounds`, `alphaInf_le_add`, and `variational_le_of_lift` prove the
needed real conditional-completeness bounds. They do not exploit default
values of an empty/unbounded real supremum or infimum. In particular a
pointwise lower bound makes the alpha image bounded below, and the uniform
upper bound bounds the image of alpha-infima above before `le_csSup` is used.

The terminal comparison is independently verified. Clipping both interval
endpoints to S removes only nonnegative costs; the beta multiplier is
positive. This gives `Lambda_mu(T)≤Lambda_mu(S)`. On the smaller triangle the
identity is `F_S=F_T+2B₂(S,T)`, with a shift independent of alpha and time
coordinates. Hence

```
0 ≤ Lambda_mu(S)-Lambda_mu(T) ≤ 8 log(k) (T-S).
```

The floor gap bounds this by `8log(k)/L`, safely below the frozen `14log(k)/L`.
The beta proof uses the actual additive split at S and obtains `e+log(k)/L`.
No time derivative, supremum attainment, temporal alpha regularity, or
macro J/H integral is assumed.

## Ordered parameters and final assumption closure

Main uses `M=4log k` and the explicit choices

```
chi = min(1/(2k), e/(8(T+1)))
rho0 = min(rhoCeiling, e/(16(M+1)))
phi0 = e/(4(M*m*T+1))
D = 4*M*m*(T/rho+2)+6*M
N0 = max(2, ceil(exp(4D/e))).
```

The four corresponding error terms are each at most e/4. The added 1 in
the denominators keeps positivity transparent and does not weaken the
required inequalities. `transferThreshold_spec` proves the numerical log
bound for every N≥N0. No asymptotic assertion is used without a threshold.

The partition and chi precede rho, phi, μ, and N. For every fixed positive
rho within the ceiling, phi0 is chosen; after fixing permitted phi and μ
with `ScalarIntegrable μ P T`, the supplied N0 precedes every N and cut array.
The actual formula is independent of phi and μ, which is stronger than the
permitted dependence. No threshold depends on cuts, interval endpoints, or
alpha. The same P appears in the scalar predicate, AlmostLike, the oscillation
bounds, and the quadrature application; there is no refinement or substitution.

The strengthened-assumption ledger is exactly:

* the chosen P's cell masses are interval-integrable on `[0,T]`;
* `profileMaxCost μ` is interval-integrable on `[0,T]`;
* each `profilePsi μ · alpha`, alpha∈[2,4], is interval-integrable there.

Main discharges generic spatial continuity with the spatial helpers and time
integrability with those exact scalar clauses. The generic arbitrary f gets
its own temporal premise. No kernel, time continuity, differentiation, macro
J/H integrability, or alternative partition premise enters. Historical
`TimeLaw`, `AlmostLike`, integrated costs and frozen theorem types are
unchanged. The temporal predicate remains confined to transfer/macro
interfaces; the empirical primitives, witness/type/probability contracts,
and empirical lower endpoint gain no such premise.

This proves the explicitly integrable transfer lane, subject to the final
compiler receipts, and makes no claim to the original arbitrary-TimeLaw
two-sided theorem. The nonmeasurable switching counterexamples in the
independent preliminary review remain applicable to that historical claim.

## Source identities reviewed

At review the parent-owned source hashes were:

| File | SHA-256 |
| --- | --- |
| Main.lean | `a3dac5b594186f345fcb4a26b565d6de4fc9bbd83b0af6ad0c93869d8f2a166c` |
| Endpoint.lean | `7ef5ccace9000d5a2d44201f831bacfde6282b745198a366d5b491bc5821b56f` |
| Parameters.lean | `fe5fe94d97efc824c28559f7d119d6f65a4eb984fec8974bf7bb16aa29e45df5` |
| Quadrature.lean | `a4f65d208be27de1e8c8c97673d563d47bada12bb34427a2340147433c0d20f0` |
| Margin.lean | `0cd1f3b94947da08fcd316a1b7b1df3e5e3356f6c05843ee4d6aa6bd6db4c964` |
| Extrema.lean | `9834ecf915048be8d83af99c01e47fdd109eea1f5441b3fc5e5aa9c1cbeebb79` |

No source or shared contract was edited by this implementation review.
