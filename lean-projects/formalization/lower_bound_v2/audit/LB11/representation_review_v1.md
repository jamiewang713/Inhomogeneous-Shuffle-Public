# LB11 independent pre-proof representation review v1

Date: 2026-10-01. Mode: read-only review of existing mathematical and Lean sources, with this new report as the sole write. No proof implementation or build was performed by this reviewer.

## Verdict

The exact frozen `MacroscopicIntegrableTarget` has the assumptions and uniform quantifier order required by LB11. It can be assembled from the actual proved LB07 and LB10 exports without a shared interface amendment. The existing `audit/LB00/CONTRACT_READY.md` is the unchanged-interface freeze receipt. The source and private-cache evidence supports completed LB07 and LB10 proof lanes, but **coordinator integration of their dependencies remains absent at this review snapshot**. Do not confuse a private lane completion receipt with the shared dependency registration required by `scripts/lane.py`.

The required sole frozen export is:

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
  RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

The required entry point is `RiffleLowerV2.MacroscopicLower.Main`; the owned implementation directory is `RiffleLowerV2/MacroscopicLower/`, and owned audit directory is `audit/LB11/`. A Tendsto corollary is not a separate frozen target. If added as a convenient owned helper, it must follow from the quantified endpoint.

## Exact target and meanings

The frozen target body in `Contracts/v1/Endpoints.lean` is the following, in namespace `RiffleLowerV2.Targets` with `TimeProfile` open:

```lean
def MacroscopicIntegrableTarget : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (T eta : ℝ), 0 < T → 0 < eta →
  ∃ (chiPartition : ℝ), 0 < chiPartition ∧ chiPartition < 1 / (k : ℝ) ∧
  ∃ (P : BorelPartition k), P.IsRegular chiPartition 1 ∧
  ∃ (rho0 : ℝ), 0 < rho0 ∧
      2 * rho0 * Real.log (k : ℝ) ≤ kappa0 (eta / 2) / 100 ∧
    ∀ (rho : ℝ), 0 < rho → rho ≤ rho0 →
    ∃ (phi0 : ℝ), 0 < phi0 ∧
      ∀ (phi : ℝ), 0 < phi → phi ≤ phi0 →
      ∀ (chiGood gamma : ℝ), 0 < chiGood → 0 < gamma →
      ∀ (epsilon : ℝ), 0 < epsilon →
      ∀ (μ : TimeLaw k), ScalarIntegrable μ P T →
      ∃ (N0 : ℕ), 2 ≤ N0 ∧
        ∀ (N : ℕ) (hN : 2 ≤ N), N0 ≤ N →
        ∀ (cuts : HorizonCuts k N T),
          AlmostLike cuts (deckPos hN) μ P T rho phi →
          LocalGood cuts (deckPos hN) chiGood gamma rho 0 T →
          eta ≤ max (macroBeta μ T) (macroLambda1 μ T) →
          1 - epsilon ≤ tv (physicalInverseLaw cuts) (uniformPermutation N)
```

`HorizonCuts k N T` is definitionally `Cuts k N (horizonDepth N T)`. `horizonDepth N T` is `floor(T * logScale N)` in naturals and `logScale N = log N`. `deckPos hN` supplies `0 < N` from `2 ≤ N`. All finite profile costs are computed from these actual integer cuts.

`ScalarIntegrable μ P T` is exactly:

```lean
(∀ i, IntervalIntegrable (cellMass μ P i) volume 0 T) ∧
IntervalIntegrable (profileMaxCost μ) volume 0 T ∧
∀ α ∈ Icc (2 : ℝ) 4,
  IntervalIntegrable (fun t => profilePsi μ t α) volume 0 T
```

The regular partition is selected before the profile and its integrability premise. It is the identical partition used in `AlmostLike`; no refinement is licensed. `TimeLaw k` remains the unrestricted function `ℝ → ProbabilityMeasure (Simplex k)`. Thus this added predicate neither redefines TimeLaw nor proves the historical arbitrary-TimeLaw endpoint. It imposes no kernel measurability, time continuity, global lower bound on pile probabilities, or scalar tilted-cost/entropy integrability.

The margin definitions are unchanged: `macroBeta μ T = 1 - integratedMaxCost μ 0 T`; `macroLambda1` uses the supremum over `0 ≤ s ≤ u ≤ T` of the infimum over `α ∈ [3,4]` of the actual stated `macroF`. The finite `lambda1` has the finite terminal horizon. `tv` is half the finite L1 distance of the chronological physical inverse law from the uniform permutation law.

The target allows `N0` to depend on the fixed profile and all preceding parameters. It is uniform in `N` and the entire cut array, with branch membership permitted to vary at every `N`. It does not assert a profile-uniform threshold, although LB07's implementation offers more uniformity than its public type.

## Actual available upstream declarations

Read sources and exact compiled inventories show the following proved declarations, rather than unproved target predicates:

| Declaration | Exact type | Relevant role |
|---|---|---|
| `RiffleLowerV2.ProfileTransfer.profileTransfer` | `Targets.ProfileTransferTarget` | Same-P partition choice and two-sided transfer |
| `RiffleLowerV2.ProfileTransfer.marginTransfer` | `Targets.MarginTransferTarget` | Quantified finite-to-macro margin error |
| `RiffleLowerV2.EmpiricalLower.largestOnly` | `Targets.LargestOnlyTarget` | Large terminal beta branch |
| `RiffleLowerV2.EmpiricalLower.coldOnly` | `Targets.ColdOnlyTarget` | LocalGood, empirical lambda, and small beta branch |
| `RiffleLowerV2.EmpiricalLower.empiricalCombined` | `Targets.EmpiricalCombinedTarget` | Optional existing uniform branch assembly |

No LB07 transfer estimate appears as an extra final theorem hypothesis. No witness, geometry, occupancy estimate, concentration inequality, graph identity or target predicate appears as an extra empirical endpoint hypothesis: their concrete discharge is inside the read LB10 proof sources.

`ProfileMarginErrors` provides exactly

```text
|beta_N(S_N) - macroBeta μ T| ≤ e + log k / log N
|lambda1_N - macroLambda1 μ T| ≤ (13/2)e + 14 log k / log N.
```

LB10's `ColdParameters k etaCold chiGood gamma rho` is the conjunction of positivity of `chiGood`, `gamma`, `rho` and `2*rho*log k ≤ kappa0 etaCold/100`. Its `coldOnly` uses the exact strict cutoff `beta_N(S_N) < kappa0 etaCold`. The largest endpoint uses `etaLargest ≤ beta_N(S_N)` and requires no LocalGood or temporal regularity.

## Feasible assembly and constant accounting

The following proof route changes no frozen definition or assumption.

1. Fix `k ≥ 2`, `T > 0`, `eta > 0`; set `etaCold = eta/2`, `d = kappa0 etaCold`, and `e = min (d/10) (eta/100) / 2`. Then `d > 0`, `e > 0`, `e < d/10`, `e < eta/100`. Unfolding `kappa0` and `kappa` gives `d ≤ eta/200000`.
2. Since `log k > 0`, choose the transfer rho ceiling `d / (200 * log k)`. Apply the actual theorem `profileTransfer` to obtain chi, P, rho0. Its `rho0 ≤ rhoCeiling` proves the desired displayed budget on rho0, then on each `rho ≤ rho0`. Choose phi0 as supplied by LB07.
3. Fix phi, positive chiGood and gamma, epsilon, the profile μ, and **its ScalarIntegrable premise for the already chosen P**. Obtain the LB07 transfer threshold, the LB10 largest threshold at margin d, and the LB10 cold threshold at margin eta/2. These are all obtained before arbitrary N or cuts.
4. The existing proved auxiliary

```lean
RiffleLowerV2.ProfileTransfer.transferThreshold_spec
    (C : ℝ) {e : ℝ} (he : 0 < e) :
  2 ≤ transferThreshold C e ∧
    ∀ N : ℕ, transferThreshold C e ≤ N → C / logScale N ≤ e / 4
```

supplies an explicit logarithmic remainder threshold with `C = log k`. Taking the maximum with the three previous thresholds gives one N0. This avoids any new limit API or duplicate asymptotic proof.
5. At each N and cuts, split on `d ≤ beta_N(S_N)`. The large case invokes `largestOnly`. In the other case, the first absolute-value bound and the remainder threshold imply `macroBeta μ T < d + 5e/4 < eta`. Hence `eta ≤ max (macroBeta μ T) (macroLambda1 μ T)` forces `eta ≤ macroLambda1 μ T`. The second absolute-value bound is at most `(13/2)e + 14(e/4) = 10e`, so `eta/2 ≤ lambda1_N`. Invoke `coldOnly` with the same LocalGood parameters.
6. The same maximum threshold works for both cases pointwise. No subsequence extraction or eventual branch stability is needed; alternating cases are already included.

All helper inequalities are ordinary ordered-field calculations after positivity of the denominators. Proof irrelevance handles the varying `hN` witnesses without changing cuts. There is no representation obstacle involving the empirical horizon, because both the transfer and LB10 endpoints use `HorizonCuts` and `deckPos` literally.

For an optional Tendsto helper, use the just-proved uniform theorem for arbitrary epsilon and `RiffleLowerV2.Ascent.tv_le_one` for the upper bound, following the already checked `Ascent.conditionalLalleyTendsto` pattern with `tendsto_order.mpr`. Any such helper must state eventual AlmostLike/LocalGood conditions for the chosen fixed parameters and same-P ScalarIntegrable premise, and must not assume the endpoint conclusion.

## Dependency readiness and build isolation

The immutable foundation manifest hash is `4aa7208c17818ae792398054c98ccd25c6c2270c6877572161ab73341398f858`; its reviewed release is `audit/LB00/CONTRACT_READY.md`. The authoritative manuscript hash in that receipt equals the planning snapshot. The registered compiler is Lean 4.33.1 and the mathlib revision is `0df444a360eaa60ab8c11dca51a86af692955474`.

`audit/LB07/FINAL_RECEIPT_v1.json` certifies all four LB07 targets, no pending lane obligations, 140 audited declarations and axiom union exactly `{propext, Classical.choice, Quot.sound}`. This review recalculated all 28 entries in its `certified_files` map and found zero mismatches.

`audit/LB10/COMPLETION_RECEIPT_v1.json` certifies the five frozen LB10 targets, no pending mathematical obligations, 93 audited declarations and the same axiom union. This review recalculated all 8 proof-source hashes and found zero mismatches. Its stated remaining external task is LB00 dependency registry and integration ledger registration.

At this snapshot, `audit/LB00/INTEGRATION_LEDGER_v7.md` certifies LB01–06, LB08 and LB09; it does not certify LB07 or LB10. Both lane entry point `.olean` files exist under their own `.build/lanes/LB07/lib/lean/` and `.build/lanes/LB10/lib/lean/` directories. Neither entry point exists in `.build/lib/lean/`.

The correct lane build after coordinator integration is:

```text
python3 scripts/lane.py LB11 RiffleLowerV2.MacroscopicLower.Main
```

`scripts/lane.py` expressly refuses to build upstream dependencies; it symlinks shared compiled sibling modules into the lane overlay and fails with `Upstream module not registered by coordinator` if an imported upstream `.olean` is absent. `--check-ready` checks only foundation inputs and is not sufficient evidence that LB07/LB10 dependencies are ready. LB11 must not rebuild either upstream lane into the shared cache or modify ownership, freezes, tooling, or umbrella imports. Obtain the coordinator registration/receipt, or an explicitly authorized lane-local read-only import arrangement, before dependent compilation.

The intended direct imports are `RiffleLowerV2.ProfileTransfer.Main` and `RiffleLowerV2.EmpiricalLower.Main`. Their transitive imports include the frozen Contracts and the finite-law/concentration results. No historical package cache is required.

## Source correspondence and reporting requirement

The new endpoint corresponds to `thm:buffered-reduced-lower-bound` using `lem:lower-profile-transfer` and `prop:cold-lower`. The frozen scalar predicate is narrower than a global assertion that all manuscript integrals are integrable, and stronger than the historical unrestricted totalized-TimeLaw contract. `formalization/time_profile/reviews/analytic_alternatives.md` explains why literal fixed-partition AlmostLike does not imply cost integrability; that is a substantive logical distinction and must remain visible in the delivery.

Final verification must print both the theorem and expanded `MacroscopicIntegrableTarget`, verify the required export's actual theorem kind, audit its complete axiom closure, record a successful owned-lane build, and explicitly distinguish empirical E (no temporal regularity) from integrable M (same-P scalar integrability). Compilation would certify the amended endpoint only, not the unchanged arbitrary-TimeLaw statement.
