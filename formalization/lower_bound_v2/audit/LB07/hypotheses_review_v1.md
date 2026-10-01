# LB07 independent hypotheses and counterexample review, v1

Date: 2026-10-01. Scope: independent mathematical audit of the frozen LB07
statements and their strengthened-assumption ledger. This report does not
certify any implementation or change any contract.

## Sources inspected and verdict

I read the assigned LB07 prompt; the live manuscript's common scalar-integral
convention and `lem:lower-profile-transfer`; `Contracts/v1/TransferFinite.lean`,
`Contracts/v1/Endpoints.lean`, `Contracts/v1/CONTRACT.md`; the actual
`Shared/Empirical.lean` definitions; historical `Base.lean`, `GridQuadrature.lean`,
and `reviews/analytic_alternatives.md`.

**No false frozen LB07 target was found.** `GenericQuadrature`,
`JointPsiContinuity`, `MarginTransferTarget`, and `ProfileTransferTarget` have
sufficient mathematical hypotheses. Their proof obligations are substantial;
the old one-sided theorem alone does not establish the new absolute error.
The selected-partition scalar integrability assumption is a genuine, necessary
visible strengthening over the historical arbitrary totalized `TimeLaw` target.
It is sufficient here without a measurable probability kernel or temporal
differentiability. This verdict is a statement audit, not a Lean proof receipt.

## Strengthened-assumption ledger

| Item | Exact status and necessity |
| --- | --- |
| `TimeLaw k = ℝ → ProbabilityMeasure (Simplex k)` | Historical definition unchanged; contains no temporal regularity. Each spatial measure is already a Borel probability measure. |
| Selected `P` and its cell masses | `ScalarIntegrable μ P T` explicitly requires `IntervalIntegrable (cellMass μ P i) volume 0 T` for every cell of this exact `P`. These assumptions license integrating the finite representative sum and comparing its integral with cell frequencies. |
| `profileMaxCost μ` | Explicit interval integrability on `[0,T]`; necessary for the absolute A estimate under totalized integral semantics. |
| `profilePsi μ · α`, every `α ∈ [2,4]` | Explicit interval integrability on `[0,T]`, separately for each α. Uniform bounds and cell oscillation yield a uniform numerical error; no joint time/α measurability is required. |
| Arbitrary generic observable `f` | The frozen generic target separately assumes `Continuous f`, `0 ≤ f ≤ M`, cell oscillation, selected-cell temporal integrability, and temporal integrability of `t ↦ ∫ f dμ_t`. The a/ψ predicate cannot substitute for the last assumption for arbitrary f. |
| Spatial integrability | Derivable from continuity, the Borel simplex, boundedness, and finite measure. It must actually be discharged before using linearity/difference estimates for spatial integrals. |
| Subinterval integrability | Derived by restriction from `[0,T]`, since all relevant endpoints lie in that interval. It is not a new premise. |
| Time continuity, derivative, or differentiation under an integral | None required or allowed as hidden strengthening. |
| Full measurable probability kernel | None required. The exact scalar assumptions suffice. |
| Macro J/H integrability | None required. LB07 transfers only A and B and uses their combinations in the margins. |
| Good-column, witness, type, probability assumptions | None are needed for this transfer. A source search shows the only occurrences of `ScalarIntegrable` in shared/contract Lean sources are its own definition and the transfer/macro endpoint interfaces. No temporal premise appears in the empirical combined endpoint. |

The quantifier order in `ProfileTransferTarget` is correct: fixed `k,T,e` and
positive bridge ceiling; choose regular `P`; choose `rho0`; fix positive
`rho ≤ rho0`; choose `phi0`; fix positive `phi ≤ phi0`; then require the
scalar predicate for **that same P**; choose `N0`; finally quantify all large
N and all cuts. Neither a cut-specific N0 nor a later unnoticed refinement is
permitted. The permitted μ-dependence of N0 is harmless; the standard finite
bound actually permits a uniform N0 independent of μ.

## Counterexamples ruling out tempting hypothesis removals

### Fixed-partition AlmostLike does not imply scalar integrability

Let `k=2`, choose two distinct rational vectors
`p=(a,1-a)`, `q=(b,1-b)` with `1/3<a<b<1/2` in the interior of the same
sufficiently small regular partition cell, and choose a non-Lebesgue-measurable
`V ⊂ [0,T]`. Put `μ_t=δ_p` on V and `μ_t=δ_q` off V. Every selected cell-mass
function is constant. All cut columns can be p when divisibility permits, or
rounded p remaining in the same cell for all large N. The literal closed-grid
cell counts have normalized discrepancy at most `1/log N`, so `AlmostLike`
holds with `phi=0` and any positive rho. All coordinates can remain above
`1/3`, so adding the source local-good condition does not repair the defect.

Both maxCost and ψ₂ have distinct positive values at p and q. Their time
integrands are nonmeasurable; the totalized Lean integrals are zero. In contrast,
the empirical A and B₂ converge to positive constants proportional to T.
Thus fixed-partition counting, even exact up to the unavoidable lattice error,
does not support the old two-sided theorem. Making p and q arbitrarily close
makes the cell oscillation arbitrarily small without curing the constant-order
failure caused by totalization. This is the historical same-cell switching
example, checked against the actual scalar definitions.

### The a/ψ scalar predicate does not cover arbitrary f or refinements

Take p and q to be distinct coordinate permutations of the same probability
vector. For example `(1/3,2/3)` and `(2/3,1/3)` suffice for a one-cell Borel
partition. All maxCost and ψα values agree, for every α. Switch their Dirac
laws on a nonmeasurable V as above. The original partition masses and all the
listed scalar costs are constant, so `ScalarIntegrable μ P T` holds.
Nevertheless the continuous observable `f(p)=p₀` has a nonmeasurable expected
value. A refinement separating p and q likewise has a nonmeasurable cell mass.
The same construction works in arbitrarily small regular cells by taking
distinct vectors with sufficiently close exchanged coordinates and choosing a
regular cell containing both; the one-cell example already refutes the
unqualified logical implication.

Consequently neither “the a/ψ predicate covers every continuous f” nor “scalar
integrability survives arbitrary refinement” is valid. These are not missing
hypotheses in the frozen target: its own-observable premise and selected-P
quantifier order correctly prevent both errors.

## Numerical and endpoint checks

Write `L=log N>0`, `q=log k>0`, `S=floor(TL)/L`, and `m=P.cellCount`.
The floor lemma supplies `0≤S≤T` and `0≤T-S<1/L`, including `S=0`.
There is no need to assume a nonempty set of empirical columns. The empirical
triangle still contains `(0,0)` when the horizon is zero.

The `m*phi` factor is necessary: multiplying the per-cell frequency error by
representative values and summing cells costs at most `M*m*phi*length`.
Do not drop m or replace it by an unproved cell-independent cancellation.
Complete half-open rho-grid blocks are disjoint; their number is at most
`T/rho+2`. The literal `AlmostLike` count is closed at both ends; removing the
left endpoint changes at most one column per block (hence at most one per
cell). Arbitrary endpoints leave at most two incomplete blocks. The column
step integral and the right-endpoint column sum can differ in at most two
partial columns, costing at most `2M/L`. These facts support the frozen
absolute error

```
2Tω + MmφT + 4Mρ + [4Mm(T/ρ+2)+6M]/L.
```

Nonnegativity and spatial/temporal integrability are indispensable when
converting pointwise representative errors into the **two directions** of
this estimate. A proof may obtain the reverse inequality from a complementary
observable `M-f`, but then it must prove that observable's time integrability
and relate the empirical integral of the constant M exactly to interval
length on `[0,S]`; applying the old theorem a second time without those checks
is insufficient. A larger omega does not cause a defect: the complete interval
empirical mass is at most T, so replacement errors can be bounded globally by
`Tω` on each side without an uncontrolled `ω/L` term.

The following explicit choices demonstrate that the frozen ordered threshold
claim is mathematically consistent (they are suggestions, not new premises):

* Set `M=3q`, and choose a regular partition at
  `chi=min(e/(8T),1/(2k))`; then `2Tchi≤e/4` and `0<chi<1/k`.
* After that partition, set `rho0=min(rhoCeiling,e/(16M))`.
* For each positive permitted rho, set `phi0=e/(4MmT)`; `m≥1` follows from
  the nonempty simplex and existence of its classifier, since `k≥2`.
* Put `D=4Mm(T/rho+2)+6M`, and choose
  `N0=max(2,ceil(exp(4D/e)))`. Then each N≥N0 satisfies `D/log N≤e/4`.

Each of the four error terms is at most e/4. These bounds are uniform in all
cut arrays, all endpoints, and α∈[2,4]. Any implementation using a slightly
different constant must show it still meets the frozen error, not silently
replace that target.

## Margin domains, boundedness, and constants

For α∈[3,4], the one-column bounds imply `0≤a≤q`,
`0≤ψα≤3q`, and the sharper `0≤ψ₂≤q`. Probability integration and the
scalar-integrability clauses transfer these bounds to every nonnegative
time interval in `[0,T]`. The finite step sums have the analogous bounds.
The sharp ψ₂ bound is useful for the frozen terminal coefficient 14; using
`3q` everywhere would give a needlessly larger intermediate constant.

For every admissible `(s,u)` and α∈[3,4], both empirical and macro F are in

```
[3 - (17/2) T q, 7/2].
```

Indeed `c=(α+3)/2∈[3,7/2]`, `A(0,s)≤Tq`,
`Bα(s,u)≤3Tq`, and `B₂(u,end)≤Tq` imply
`c(1-A)-Bα-2B₂≥3-(7/2+3+2)Tq`, while nonnegative costs imply F≤7/2.
This establishes finite uniform lower/upper bounds without continuity of
α↦integratedPsi. The α-domain `[3,4]` is nonempty (contains 3), and both
triangles are nonempty (contain `(0,0)`). Therefore every relevant image has
the `BddBelow`/`BddAbove` and nonemptiness properties required by real `sInf`
and `sSup`; their totalized values must not be used without these facts.

On the common triangle `0≤s≤u≤S`, A/B errors at most e give

```
|F_N(α,s,u)-F_macro(α,s,u)| ≤ (13/2)e + 2q/L.
```

Here `7/2+1+2=13/2`; the additional `2q/L` is exactly the macro B₂ tail
from S to T. The beta terminal error is `e+q/L`.

For the reverse supremum comparison, project `(s,u)∈triangle T` to
`(min(s,S),min(u,S))∈triangle S`. Each coordinate changes by at most `T-S`.
The macro F displacement is at most

```
[(7/2) + 6 + 2] q (T-S) ≤ (23/2)q/L.
```

The three pieces are the beta endpoint, the two endpoints of Bα, and the
lower endpoint of B₂. Combining with the common-domain error gives
`(13/2)e+(27/2)q/L`, hence the frozen safe coefficient 14. In the other
direction the empirical triangle is a subset of the macro triangle. Apply
the uniform α bound through the infima, then use inclusion and projection
for the suprema, with the verified finite bounds above. No attainment of a
supremum/infimum and no temporal derivative is needed.

### Independently checked simpler terminal comparison

After the initial review, the coordinator proposed comparing the macro
functional at the two different terminal horizons before comparing empirical
and macro quantities. This is valid and avoids needing the sharp ψ₂ bound
for the frozen coefficient 14. Write `Λμ(V)` for the same macro definition
with terminal V. Nonnegativity gives, pointwise for every α∈[3,4],

```
F_macro(μ,S,α,min(s,S),min(u,S)) ≥ F_macro(μ,T,α,s,u).
```

If `u≤S`, the difference is the nonnegative terminal tail. If `s≤S<u`,
the left expression ends its Bα interval at S and its B₂ interval is empty;
the removed costs are nonnegative. If `S<s`, the left expression is
`c*beta(S)`, and all costs removed from the right are nonnegative, including
`c*A(S,s)` since c>0. Thus infima and suprema give `Λμ(S)≥Λμ(T)`.
Conversely, on the smaller triangle the exact identity
`F_S=F_T+2B₂(S,T)` has a shift independent of α,s,u, so

```
0 ≤ Λμ(S)-Λμ(T) ≤ 2B₂(S,T).
```

Comparing empirical F with macro F at terminal S gives exactly `(13/2)e`.
This alternative proves a still smaller terminal error whenever an available
pointwise ψ₂ bound is at most `7 log k`, and hence the historically available
looser bounds suffice. The proof must still verify the nonempty/bounded image
facts recorded above. The earlier absolute-projection calculation remains
valid but is unnecessary for an implementation using this monotonicity.

## Required implementation resolutions

1. Supply the new absolute quadrature proof and its own scalar-integrability
   arguments; the historical one-sided proof is not already the target.
2. Prove joint spatial/α continuity, including zero coordinates and strict
   positivity of the power sum before applying logarithmic continuity.
3. Prove boundedness/nonemptiness before every real supremum/infimum step.
4. Keep the actual selected P in the scalar predicate and in `AlmostLike`.
5. Describe the endpoint as the explicitly strengthened integrable target;
   do not certify the historical unchanged arbitrary-TimeLaw statement.

No new frozen assumption or changed conclusion is recommended by this review.
