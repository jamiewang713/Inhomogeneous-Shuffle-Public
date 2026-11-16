# LB11 exact checked public exports

Import `RiffleLowerV2.MacroscopicLower.Main`. Extracted from the successful v2 elaborated declaration audit. The required endpoint is a theorem, with its type literally the unchanged frozen target constant. Generated internal declarations are retained in compiled-declarations-v2.json.

## RiffleLowerV2.MacroscopicLower.macroscopicIntegrable

Source: `RiffleLowerV2/MacroscopicLower/Main.lean`, line 12. Kind: theorem.

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable :
RiffleLowerV2.Targets.MacroscopicIntegrableTarget
```

## RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto

Source: `RiffleLowerV2/MacroscopicLower/Main.lean`, line 54. Kind: theorem.

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable_tendsto :
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T eta : ℝ),
      0 < T →
        0 < eta →
          ∃ (chiPartition : ℝ),
            0 < chiPartition ∧
              chiPartition < 1 / ↑k ∧
                ∃ (P : TimeProfile.BorelPartition k),
                  P.IsRegular chiPartition 1 ∧
                    ∃ (rho0 : ℝ),
                      0 < rho0 ∧
                        2 * rho0 * Real.log ↑k ≤ RiffleLowerV2.kappa0 (eta / 2) / 100 ∧
                          ∀ (rho : ℝ),
                            0 < rho →
                              rho ≤ rho0 →
                                ∃ (phi0 : ℝ),
                                  0 < phi0 ∧
                                    ∀ (phi : ℝ),
                                      0 < phi →
                                        phi ≤ phi0 →
                                          ∀ (chiGood gamma : ℝ),
                                            0 < chiGood →
                                              0 < gamma →
                                                ∀ (μ : TimeProfile.TimeLaw k),
                                                  RiffleLowerV2.ScalarIntegrable μ P T →
                                                    ∀ (cuts : (N : ℕ) → RiffleLowerV2.Targets.HorizonCuts k N T),
                                                      (∀ᶠ (N : ℕ) in Filter.atTop,
                                                          ∀ (hN : 2 ≤ N),
                                                            TimeProfile.AlmostLike (cuts N) ⋯ μ P T rho phi ∧
                                                              TimeProfile.LocalGood (cuts N) ⋯ chiGood gamma rho 0 T) →
                                                        eta ≤
                                                            max (RiffleLowerV2.macroBeta μ T)
                                                              (RiffleLowerV2.macroLambda1 μ T) →
                                                          Filter.Tendsto
                                                            (fun (N : ℕ) =>
                                                              RiffleLowerV2.tv
                                                                (RiffleLowerV2.physicalInverseLaw (cuts N))
                                                                (RiffleLowerV2.uniformPermutation N))
                                                            Filter.atTop (nhds 1)
```

## RiffleLowerV2.MacroscopicLower.transferAccuracy

Source: `RiffleLowerV2/MacroscopicLower/Parameters.lean`, line 8. Kind: definition.

```lean
RiffleLowerV2.MacroscopicLower.transferAccuracy :
ℝ → ℝ
```

## RiffleLowerV2.MacroscopicLower.transferAccuracy_spec

Source: `RiffleLowerV2/MacroscopicLower/Parameters.lean`, line 11. Kind: theorem.

```lean
RiffleLowerV2.MacroscopicLower.transferAccuracy_spec :
∀ {eta : ℝ},
  0 < eta →
    0 < RiffleLowerV2.MacroscopicLower.transferAccuracy eta ∧
      RiffleLowerV2.MacroscopicLower.transferAccuracy eta < RiffleLowerV2.kappa0 (eta / 2) / 10 ∧
        RiffleLowerV2.MacroscopicLower.transferAccuracy eta < eta / 100
```

## RiffleLowerV2.MacroscopicLower.coldMargin_scale

Source: `RiffleLowerV2/MacroscopicLower/Parameters.lean`, line 24. Kind: theorem.

```lean
RiffleLowerV2.MacroscopicLower.coldMargin_scale :
∀ {eta : ℝ}, 0 < eta → 0 < RiffleLowerV2.kappa0 (eta / 2) ∧ RiffleLowerV2.kappa0 (eta / 2) ≤ eta / 200000
```

## RiffleLowerV2.MacroscopicLower.bridgeCeiling

Source: `RiffleLowerV2/MacroscopicLower/Parameters.lean`, line 33. Kind: definition.

```lean
RiffleLowerV2.MacroscopicLower.bridgeCeiling :
ℕ → ℝ → ℝ
```

## RiffleLowerV2.MacroscopicLower.bridgeCeiling_spec

Source: `RiffleLowerV2/MacroscopicLower/Parameters.lean`, line 36. Kind: theorem.

```lean
RiffleLowerV2.MacroscopicLower.bridgeCeiling_spec :
∀ {k : ℕ},
  2 ≤ k →
    ∀ {eta : ℝ},
      0 < eta →
        0 < RiffleLowerV2.MacroscopicLower.bridgeCeiling k eta ∧
          ∀ rho ≤ RiffleLowerV2.MacroscopicLower.bridgeCeiling k eta,
            2 * rho * Real.log ↑k ≤ RiffleLowerV2.kappa0 (eta / 2) / 100
```

## RiffleLowerV2.MacroscopicLower.small_beta_forces_cold

Source: `RiffleLowerV2/MacroscopicLower/Parameters.lean`, line 49. Kind: theorem.

```lean
RiffleLowerV2.MacroscopicLower.small_beta_forces_cold :
∀ {eta betaFinite lambda0 lambda1 lambdaFinite d : ℝ},
  0 < eta →
    d ≤ RiffleLowerV2.MacroscopicLower.transferAccuracy eta / 4 →
      |betaFinite - lambda0| ≤ RiffleLowerV2.MacroscopicLower.transferAccuracy eta + d →
        |lambdaFinite - lambda1| ≤ 13 / 2 * RiffleLowerV2.MacroscopicLower.transferAccuracy eta + 14 * d →
          betaFinite < RiffleLowerV2.kappa0 (eta / 2) →
            eta ≤ max lambda0 lambda1 → lambda0 < eta ∧ eta / 2 ≤ lambdaFinite
```

## Full compiled frozen target and scalar premise

The pretty printer abbreviates only proof-valued arguments as `⋯`; their explicit source expressions are `Targets.deckPos hN`. No mathematical premise is omitted.

```lean
def RiffleLowerV2.Targets.MacroscopicIntegrableTarget : Prop :=
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T eta : ℝ),
      0 < T →
        0 < eta →
          ∃ (chiPartition : ℝ),
            0 < chiPartition ∧
              chiPartition < 1 / ↑k ∧
                ∃ (P : TimeProfile.BorelPartition k),
                  P.IsRegular chiPartition 1 ∧
                    ∃ (rho0 : ℝ),
                      0 < rho0 ∧
                        2 * rho0 * Real.log ↑k ≤ RiffleLowerV2.kappa0 (eta / 2) / 100 ∧
                          ∀ (rho : ℝ),
                            0 < rho →
                              rho ≤ rho0 →
                                ∃ (phi0 : ℝ),
                                  0 < phi0 ∧
                                    ∀ (phi : ℝ),
                                      0 < phi →
                                        phi ≤ phi0 →
                                          ∀ (chiGood gamma : ℝ),
                                            0 < chiGood →
                                              0 < gamma →
                                                ∀ (epsilon : ℝ),
                                                  0 < epsilon →
                                                    ∀ (μ : TimeProfile.TimeLaw k),
                                                      RiffleLowerV2.ScalarIntegrable μ P T →
                                                        ∃ (N0 : ℕ),
                                                          2 ≤ N0 ∧
                                                            ∀ (N : ℕ) (hN : 2 ≤ N),
                                                              N0 ≤ N →
                                                                ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T),
                                                                  TimeProfile.AlmostLike cuts ⋯ μ P T rho phi →
                                                                    TimeProfile.LocalGood cuts ⋯ chiGood gamma rho 0 T →
                                                                      eta ≤
                                                                          max (RiffleLowerV2.macroBeta μ T)
                                                                            (RiffleLowerV2.macroLambda1 μ T) →
                                                                        1 - epsilon ≤
                                                                          RiffleLowerV2.tv
                                                                            (RiffleLowerV2.physicalInverseLaw cuts)
                                                                            (RiffleLowerV2.uniformPermutation N)
def RiffleLowerV2.ScalarIntegrable : {k : ℕ} → TimeProfile.TimeLaw k → TimeProfile.BorelPartition k → ℝ → Prop :=
fun {k : ℕ} (μ : TimeProfile.TimeLaw k) (P : TimeProfile.BorelPartition k) (T : ℝ) =>
  (∀ (i : Fin P.cellCount), IntervalIntegrable (TimeProfile.cellMass μ P i) MeasureTheory.volume 0 T) ∧
    IntervalIntegrable (TimeProfile.profileMaxCost μ) MeasureTheory.volume 0 T ∧
      ∀ α ∈ Set.Icc 2 4, IntervalIntegrable (fun (t : ℝ) => TimeProfile.profilePsi μ t α) MeasureTheory.volume 0 T
```

## Closure

The complete transitive axiom union is `Classical.choice`, `Quot.sound`, `propext`. The main proof uses actual checked LB07 and LB10 theorem values, not assumptions of their target propositions. The sequence corollary depends directly on the uniform theorem and `Ascent.tv_le_one`.
