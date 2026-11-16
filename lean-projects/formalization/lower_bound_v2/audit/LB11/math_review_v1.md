# LB11 independent mathematical pre-proof review

Verdict: the frozen scalar-integrable macroscopic endpoint follows from the actual LB07 and LB10 theorem interfaces with the stated constants and uniform quantifier order. I found no mathematical obstruction to this assembly. The current obstacle is coordinator registration of the completed input lanes: this is an import/build readiness issue, not a false theorem or a missing mathematical hypothesis. This review does not certify an unimplemented LB11 theorem or an unchanged arbitrary-TimeLaw theorem.

## Reviewed evidence

- Authoritative manuscript `time_inhomogeneous_riffle_shuffle_unified_article.tex`, labels `thm:buffered-reduced-lower-bound` (around line 2853), `lem:lower-profile-transfer` (around line 2921), and `prop:cold-lower` with the final branch argument (around lines 4277–4321). Its actual SHA-256 matches the planning snapshot: `672f414c9ccd6229c7f496c80cba6cc989c5fd07d93b75e66083456ee6242b1d`.
- Frozen `Contracts/v1/Endpoints.lean`, `Contracts/v1/CONTRACT.md`, shared `Empirical.lean`, historical `time_profile/RiffleTimeProfile/Base.lean`, and `time_profile/reviews/analytic_alternatives.md`.
- Actual LB07 source declarations in `RiffleLowerV2/ProfileTransfer/Main.lean`, `Margin.lean`, and `Parameters.lean`, its final receipt, and compiled export inventory.
- Actual LB10 source assembly in `RiffleLowerV2/EmpiricalLower/Main.lean`, its completion receipt, and compiled export inventory.
- LB00 foundation receipt, latest integration ledger v7, existing `Contracts/dependencies/` receipt directories, and `scripts/lane.py`.

I independently checked all 12 proof-source hashes in LB07's receipt and all 8 proof-source hashes in LB10's receipt against current files: all match. This review did not run a fresh Lean compilation or re-audit every upstream proof body. Both lane receipts report ordinary kernel axiom closure `Classical.choice`, `Quot.sound`, `propext` only; downstream final checking must verify that closure for LB11 itself.

## Exact mathematical invariants

The margins remain precisely

\[
\Lambda_0(T)=1-\int_0^T a(t)\,dt,\qquad
\Lambda_1(T)=\sup_{0\le s\le u\le T}\inf_{3\le\alpha\le4}
\left\{\frac{\alpha+3}{2}\beta(s)-B_\alpha(s,u)-2B_2(u,T)\right\}.
\]

The finite horizon is `horizon N (horizonDepth N T)` with the source floor convention, and the finite margins use the actual column step integrals. The endpoint law is `physicalInverseLaw cuts`, compared with `uniformPermutation N`. Replacing these margins by homogeneous formulas or replacing this law by an unproved graph identification would change the contract; neither change is necessary.

Set `etaCold = eta / 2`, `kappa etaCold = eta / 2000`, and `k0 = kappa0 etaCold = min (eta / 200000) (1 / 1000)`. In particular `0 < k0` and `k0 ≤ eta / 200000` for every `eta > 0`. No extra upper bound on eta is needed.

The reviewed scalar premise is exactly

```lean
ScalarIntegrable μ P T :=
  (∀ i, IntervalIntegrable (cellMass μ P i) volume 0 T) ∧
  IntervalIntegrable (profileMaxCost μ) volume 0 T ∧
  ∀ α ∈ Icc (2 : ℝ) 4,
    IntervalIntegrable (fun t => profilePsi μ t α) volume 0 T
```

It is indexed by the same partition returned by LB07. There is no temporal regularity assumption on the finite arrays. The predicate does not require a probability kernel, time continuity, integrability of tilted-cost or tilted-entropy profiles, positive lower bounds on every pile, or any upper-bound theorem.

The current manuscript's global sentence says that all displayed scalar integrals are ordinary measurable integrable scalar functions. That convention implies the restricted scalar assumptions used here, including the selected cell masses; it is broader than this endpoint needs. Historical Lean `TimeLaw k` is merely `ℝ → ProbabilityMeasure (Simplex k)` and contains no corresponding temporal premise. Thus this theorem is an explicitly regularized interpretation, not certification of the historical arbitrary totalized-TimeLaw statement.

## Constant and branch audit

A concrete safe choice is

\[
e=\min\{k_0/20,\eta/200\}.
\]

It gives `0 < e < min (k0 / 10) (eta / 100)` without any extra assumption. Since `k ≥ 2`, `log k > 0`; feed the positive ceiling

\[
\rho_{\rm ceiling}=\frac{k_0}{200\log k}
\]

to `ProfileTransfer.profileTransfer`. Its chosen `rho0 ≤ rhoCeiling` then satisfies `2 * rho0 * log k ≤ k0 / 100`. For any fixed `0 < rho ≤ rho0`, the same inequality holds for rho, supplying `ColdParameters` after the user-visible positive chiGood and gamma are fixed.

LB07's actual `ProfileMarginErrors` gives

\[
|\beta_N(S_N)-\Lambda_0(T)|\le e+\frac{\log k}{\log N},\qquad
|\Lambda_{1,N}-\Lambda_1(T)|\le\frac{13}{2}e+
\frac{14\log k}{\log N}.
\]

The coefficient `13/2` is exactly `7/2 + 1 + 2` on the common domain, and the frozen explicit coefficient 14 safely covers terminal clipping. It is important to use both sides of these inequalities; an unrelated one-sided totalized-integral result does not provide this macro lower-bound argument.

Choose a further threshold, independent of μ and cuts, with `14 * log k / log N ≤ e`. An existing proved helper makes this explicit: `ProfileTransfer.transferThreshold_spec (14 * log k)` at tolerance `4 * e` gives that bound. Because `log N > 0` after `N ≥ 2`, it also implies `log k / log N ≤ e`.

Now split at exactly `k0`:

1. If `k0 ≤ beta_N(S_N)`, use `EmpiricalLower.largestOnly` with positive exponent `k0`. This branch requires neither the profile premise nor LocalGood, although the final macro theorem may retain its standing assumptions.
2. Otherwise `beta_N(S_N) < k0`. The first margin estimate yields `Lambda0(T) < k0 + 2e < eta`. The macro maximum assumption therefore forces `eta ≤ Lambda1(T)`. The second margin estimate yields `lambda1_N ≥ eta - (15/2)e > eta/2`, hence the non-strict empirical cold margin required by `EmpiricalLower.coldOnly`. That theorem receives the fixed admissible cold parameters, actual `LocalGood`, and the strict small-beta branch.

The displayed strict inequalities have ample slack. For example `k0 + 2e < eta/200000 + eta/50 < eta` and `(15/2)e < 3eta/40 < eta/2`. No appeal to a homogeneous constant or an implicit positivity cap is involved.

A mathematically equivalent second implementation is to construct `EmpiricalAlternative` by this numerical split and apply `EmpiricalLower.empiricalCombined` with `etaLargest = k0` and `etaCold = eta/2`. It is acceptable only if the branch transfer is actually proved; supplying `EmpiricalAlternative` as an extra endpoint assumption would not complete LB11.

## Uniformity and threshold order

The required order is

\[
(k,T,\eta)\ \longrightarrow\ (\chi_{\rm partition},P,\rho_0)
\ \longrightarrow\ \rho\ \longrightarrow\ \varphi_0
\ \longrightarrow\ (\varphi,\chi_g,\gamma,\epsilon,\mu,
\operatorname{ScalarIntegrable}(\mu,P,T))
\ \longrightarrow\ N_0\ \longrightarrow\ (N,\text{all cuts}).
\]

The transfer accuracy and rho ceiling are chosen from `k,T,eta` before P. In particular P is not selected after learning μ's integrability and is never refined after the scalar premise is supplied. The final threshold may depend on the fixed profile and fixed tolerances; it must not depend on the particular cut array or on which branch holds at a given N.

Using the separate endpoints, take the maximum of the transfer threshold, the explicit logarithmic-error threshold, the largest-branch threshold, and the cold-branch threshold. Both empirical thresholds use the same requested final accuracy epsilon, so there is no loss from adding branch errors and no reason to split epsilon in half. Every admissible array at each `N ≥ N0` then obeys `1 - epsilon ≤ tv`; arrays alternating between branches are automatically included.

The frozen contract requires the exact quantified uniform theorem, not a Tendsto wrapper. If an optional sequence corollary is included, derive it from that theorem plus `tv ≤ 1`, using eventual AlmostLike and LocalGood for a fixed admissible parameter selection. A standalone sequence proof cannot substitute for uniformity over all cuts. The final declaration must not take upstream target propositions or a supplied TV-convergence claim as premises.

## Readiness obstacles and resolution criteria

Mathematical inputs are present: the actual theorem declarations `ProfileTransfer.profileTransfer : Targets.ProfileTransferTarget`, `EmpiricalLower.largestOnly : Targets.LargestOnlyTarget`, `EmpiricalLower.coldOnly : Targets.ColdOnlyTarget`, and `EmpiricalLower.empiricalCombined : Targets.EmpiricalCombinedTarget` exist in source, and matching receipts claim successful lane builds. LB07's receipt says complete with no pending lane obligations. LB10's receipt says completed and ready for coordinator integration, explicitly leaving LB00 registry/integration work outside its lane.

Coordinator readiness is not yet present in the inspected snapshot:

- `Contracts/dependencies/` has no LB07 or LB10 receipt directory.
- Latest `audit/LB00/INTEGRATION_LEDGER_v7.md` certifies LB01–06, LB08, LB09, but not LB07 or LB10.
- `.build/lib/lean/RiffleLowerV2/ProfileTransfer/Main.olean` and `.build/lib/lean/RiffleLowerV2/EmpiricalLower/Main.olean` are absent. Their owner-lane oleans exist in LB07 and LB10 caches respectively.
- `scripts/lane.py` explicitly rejects an unregistered upstream import; LB11 must not silently copy or mix sibling lane caches to bypass that restriction.

Accordingly, request LB00's additive integration/registration receipt for these unchanged completed declarations before dependent LB11 compilation, without rewriting shared contracts or old freeze hashes. No additive mathematical target change is needed. After registration, the proposed proof is an ordinary finite branch assembly; the final independent type/axiom/build audit remains necessary.

## Missing-hypothesis control

The historical same-cell switching example remains a valid obstruction to deriving scalar cost integrability from fixed-partition AlmostLike, even when all cell masses are constant and LocalGood holds. It refutes the unchanged two-sided transfer route; this report does not overclaim that the example alone refutes every possible historical endpoint theorem. The opt-in scalar premise addresses precisely the transfer needed in the current argument and should remain visible in both the expanded final theorem type and delivery report.

Final independent assessment: mathematical assembly approved under the frozen explicit scalar assumptions; no new hypothesis proposed. Coordinator import registration and the actual LB11 checked implementation remain pending at review time.
