# LB07 exact compiled exports v1

All four entries are checked theorem declarations. Their frozen target definitions are reproduced after the declaration inventory in `check_v1.log`, and remain unchanged in `Contracts/v1/EXPORTS.md`.

```lean
RiffleLowerV2.ProfileTransfer.genericQuadrature : RiffleLowerV2.Targets.GenericQuadrature
```

Transitive axiom closure: `propext`, `Classical.choice`, `Quot.sound`.

```lean
RiffleLowerV2.ProfileTransfer.jointPsiContinuity : RiffleLowerV2.Targets.JointPsiContinuity
```

Transitive axiom closure: `propext`, `Classical.choice`, `Quot.sound`.

```lean
RiffleLowerV2.ProfileTransfer.marginTransfer : RiffleLowerV2.Targets.MarginTransferTarget
```

Transitive axiom closure: `propext`, `Classical.choice`, `Quot.sound`.

```lean
RiffleLowerV2.ProfileTransfer.profileTransfer : RiffleLowerV2.Targets.ProfileTransferTarget
```

Transitive axiom closure: `propext`, `Classical.choice`, `Quot.sound`.

## Complete owned declaration inventory

140 elaborated declarations were inspected, including generated declarations and private helpers. The union of their transitive axiom closures is exactly: `Classical.choice`, `Quot.sound`, `propext`.

Machine-readable types and direct constant dependencies: `compiled_declarations_v1.json`. Exact compiled types of all named public helpers follow.

```lean
RiffleLowerV2.ProfileTransfer.Compat.AlmostLike.timeCellCount_error : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} {hN : 0 < N} {mu : TimeProfile.TimeLaw k}
  {P : TimeProfile.BorelPartition k} {T rho phi : ℝ},
  TimeProfile.AlmostLike cuts hN mu P T rho phi →
    2 ≤ N →
      0 < rho →
        ∀ {a : ℝ},
          0 ≤ a →
            (∃ (z : ℤ), a = rho * ↑z) →
              a + rho ≤ T →
                ∀ (i : Fin P.cellCount),
                  |↑(RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts hN P a (a + rho) i) /
                          TimeProfile.logScale N -
                        ∫ (t : ℝ) in a..a + rho, TimeProfile.cellMass mu P i t| ≤
                    phi * rho + 2 / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.BorelPartition.cell_mass_bounds : ∀ {k : ℕ} (P : TimeProfile.BorelPartition k) (nu : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k))
  (i : Fin P.cellCount), 0 ≤ (↑nu (P.cell i)).toReal ∧ (↑nu (P.cell i)).toReal ≤ 1
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.BorelPartition.measurableSet_cell : ∀ {k : ℕ} (P : TimeProfile.BorelPartition k) (i : Fin P.cellCount), MeasurableSet (P.cell i)
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.BorelPartition.sum_cell_mass : ∀ {k : ℕ} (P : TimeProfile.BorelPartition k) (nu : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k)),
  ∑ i : Fin P.cellCount, (↑nu (P.cell i)).toReal = 1
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.cellMass_bounds : ∀ {k : ℕ} (mu : TimeProfile.TimeLaw k) (P : TimeProfile.BorelPartition k) (i : Fin P.cellCount) (t : ℝ),
  0 ≤ TimeProfile.cellMass mu P i t ∧ TimeProfile.cellMass mu P i t ≤ 1
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.columnTime_injective : ∀ {N K : ℕ}, 2 ≤ N → Function.Injective (TimeProfile.columnTime N)
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.finite_integral_envelope : ∀ {Ω : Type u_1} {ι : Type u_2} [inst : MeasurableSpace Ω] [inst_1 : Fintype ι] (nu : MeasureTheory.Measure Ω)
  [MeasureTheory.IsFiniteMeasure nu] (h : ι → Ω → ℝ) (r : ι → ℝ) (F : Ω → ℝ) {M omega : ℝ},
  0 ≤ M →
    0 ≤ omega →
      (∀ (i : ι) (t : Ω), 0 ≤ h i t) →
        (∀ (t : Ω), ∑ i : ι, h i t = 1) →
          (∀ (i : ι), 0 ≤ r i ∧ r i ≤ M) →
            (∀ (t : Ω), 0 ≤ F t) →
              (∀ (t : Ω), F t ≤ omega + ∑ i : ι, r i * h i t) →
                ∫ (t : Ω), F t ∂nu ≤ (M + omega) * nu.real Set.univ - ∑ i : ι, (M - r i) * ∫ (t : Ω), h i t ∂nu
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.finite_integral_envelope_of_counts : ∀ {Ω : Type u_1} {ι : Type u_2} [inst : MeasurableSpace Ω] [inst_1 : Fintype ι] (nu : MeasureTheory.Measure Ω)
  [MeasureTheory.IsFiniteMeasure nu] (h : ι → Ω → ℝ) (r : ι → ℝ) (F : Ω → ℝ) {M omega : ℝ},
  0 ≤ M →
    0 ≤ omega →
      (∀ (i : ι) (t : Ω), 0 ≤ h i t) →
        (∀ (t : Ω), ∑ i : ι, h i t = 1) →
          (∀ (i : ι), 0 ≤ r i ∧ r i ≤ M) →
            (∀ (t : Ω), 0 ≤ F t) →
              (∀ (t : Ω), F t ≤ omega + ∑ i : ι, r i * h i t) →
                ∀ (c : ι → ℝ) {d e : ℝ},
                  0 ≤ d →
                    (∀ (i : ι), |c i - ∫ (t : Ω), h i t ∂nu| ≤ d) →
                      nu.real Set.univ - ∑ i : ι, c i ≤ e →
                        ∫ (t : Ω), F t ∂nu ≤
                          ∑ i : ι, r i * c i + omega * nu.real Set.univ + M * (e + ↑(Fintype.card ι) * d)
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.interval_integral_envelope_of_counts : ∀ {ι : Type u_1} [inst : Fintype ι] (a b : ℝ),
  a ≤ b →
    ∀ (h : ι → ℝ → ℝ) (r : ι → ℝ) (F : ℝ → ℝ) {M omega : ℝ},
      0 ≤ M →
        0 ≤ omega →
          (∀ (i : ι) (t : ℝ), 0 ≤ h i t) →
            (∀ (t : ℝ), ∑ i : ι, h i t = 1) →
              (∀ (i : ι), 0 ≤ r i ∧ r i ≤ M) →
                (∀ (t : ℝ), 0 ≤ F t) →
                  (∀ (t : ℝ), F t ≤ omega + ∑ i : ι, r i * h i t) →
                    ∀ (c : ι → ℝ) {d e : ℝ},
                      0 ≤ d →
                        (∀ (i : ι), |c i - ∫ (t : ℝ) in a..b, h i t| ≤ d) →
                          b - a - ∑ i : ι, c i ≤ e →
                            ∫ (t : ℝ) in a..b, F t ≤
                              ∑ i : ι, r i * c i + omega * (b - a) + M * (e + ↑(Fintype.card ι) * d)
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.mem_timePositions : ∀ {N K : ℕ} {a b : ℝ} {j : Fin K},
  j ∈ RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b ↔
    a < TimeProfile.columnTime N j ∧ TimeProfile.columnTime N j ≤ b
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.mem_timePositions_iff_floor : ∀ {N K : ℕ},
  2 ≤ N →
    ∀ {a b : ℝ},
      0 ≤ a →
        a ≤ b →
          ∀ (j : Fin K),
            j ∈ RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b ↔
              ⌊a * TimeProfile.logScale N⌋₊ < ↑j + 1 ∧ ↑j + 1 ≤ ⌊b * TimeProfile.logScale N⌋₊
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.one_sided_quadrature : ∀ {k N : ℕ} {T rho phi M omega a b : ℝ} (cuts : TimeProfile.Cuts k N (TimeProfile.horizonDepth N T)) (hN : 2 ≤ N)
  (mu : TimeProfile.TimeLaw k) (P : TimeProfile.BorelPartition k) (f : TimeProfile.Simplex k → ℝ),
  0 ≤ T →
    0 < rho →
      0 ≤ phi →
        0 ≤ M →
          0 ≤ omega →
            (∀ (p : TimeProfile.Simplex k), 0 ≤ f p ∧ f p ≤ M) →
              (∀ (p : TimeProfile.Simplex k), |f p - f (P.rep (P.classify p))| ≤ omega) →
                TimeProfile.AlmostLike cuts ⋯ mu P T rho phi →
                  0 ≤ a →
                    a ≤ b →
                      b ≤ T →
                        ∫ (t : ℝ) in a..b, ∫ (p : TimeProfile.Simplex k), f p ∂↑(mu t) ≤
                          (∑
                                j ∈
                                  RiffleLowerV2.ProfileTransfer.Compat.timePositions N (TimeProfile.horizonDepth N T) a
                                    b,
                                f (cuts.profile ⋯ j)) /
                              TimeProfile.logScale N +
                            RiffleLowerV2.ProfileTransfer.Compat.quadratureError N T rho phi P.cellCount M omega
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.one_sided_quadrature_representative : ∀ {k N : ℕ} {T rho phi M omega a b : ℝ} (cuts : TimeProfile.Cuts k N (TimeProfile.horizonDepth N T)) (hN : 2 ≤ N)
  (mu : TimeProfile.TimeLaw k) (P : TimeProfile.BorelPartition k) (f : TimeProfile.Simplex k → ℝ),
  0 ≤ T →
    0 < rho →
      0 ≤ phi →
        0 ≤ M →
          0 ≤ omega →
            (∀ (p : TimeProfile.Simplex k), 0 ≤ f p ∧ f p ≤ M) →
              (∀ (p : TimeProfile.Simplex k), |f p - f (P.rep (P.classify p))| ≤ omega) →
                TimeProfile.AlmostLike cuts ⋯ mu P T rho phi →
                  0 ≤ a →
                    a ≤ b →
                      b ≤ T →
                        ∫ (t : ℝ) in a..b, ∫ (p : TimeProfile.Simplex k), f p ∂↑(mu t) ≤
                          (∑
                                j ∈
                                  RiffleLowerV2.ProfileTransfer.Compat.timePositions N (TimeProfile.horizonDepth N T) a
                                    b,
                                f (P.rep (P.classify (cuts.profile ⋯ j)))) /
                              TimeProfile.logScale N +
                            RiffleLowerV2.ProfileTransfer.Compat.quadratureError N T rho phi P.cellCount M omega
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.probability_integral_bounds : ∀ {k : ℕ} (nu : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k)) (f : TimeProfile.Simplex k → ℝ) {M : ℝ},
  0 ≤ M →
    (∀ (p : TimeProfile.Simplex k), 0 ≤ f p ∧ f p ≤ M) →
      0 ≤ ∫ (p : TimeProfile.Simplex k), f p ∂↑nu ∧ ∫ (p : TimeProfile.Simplex k), f p ∂↑nu ≤ M
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.probability_integral_le_cell_sum : ∀ {k : ℕ} (P : TimeProfile.BorelPartition k) (nu : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k))
  (f : TimeProfile.Simplex k → ℝ) {M omega : ℝ},
  0 ≤ M →
    0 ≤ omega →
      (∀ (p : TimeProfile.Simplex k), 0 ≤ f p ∧ f p ≤ M) →
        (∀ (p : TimeProfile.Simplex k), |f p - f (P.rep (P.classify p))| ≤ omega) →
          ∫ (p : TimeProfile.Simplex k), f p ∂↑nu ≤ omega + ∑ i : Fin P.cellCount, f (P.rep i) * (↑nu (P.cell i)).toReal
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.quadratureError : ℕ → ℝ → ℝ → ℝ → ℕ → ℝ → ℝ → ℝ
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.quadratureError.eq_1 : ∀ (N : ℕ) (T rho phi : ℝ) (m : ℕ) (M omega : ℝ),
  RiffleLowerV2.ProfileTransfer.Compat.quadratureError N T rho phi m M omega =
    2 * omega * T + M * ↑m * phi * T + 2 * M * rho +
      (omega + M + 2 * M * ↑m) * ↑(⌊T / rho⌋₊ + 1) / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.sum_cellMass : ∀ {k : ℕ} (mu : TimeProfile.TimeLaw k) (P : TimeProfile.BorelPartition k) (t : ℝ),
  ∑ i : Fin P.cellCount, TimeProfile.cellMass mu P i t = 1
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.sum_timeCellCount : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (a b : ℝ),
  ∑ i : Fin P.cellCount, RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts hN P a b i =
    (RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b).card
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.sum_timeCellCount_real : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (a b : ℝ),
  ∑ i : Fin P.cellCount,
      ↑(RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts hN P a b i) / TimeProfile.logScale N =
    ↑(RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b).card / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timeCellCount : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → (P : TimeProfile.BorelPartition k) → ℝ → ℝ → Fin P.cellCount → ℕ
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timeCellCount.congr_simp : ∀ {k N K : ℕ} (cuts cuts_1 : TimeProfile.Cuts k N K),
  cuts = cuts_1 →
    ∀ (hN : 0 < N) (P : TimeProfile.BorelPartition k) (a a_1 : ℝ),
      a = a_1 →
        ∀ (b b_1 : ℝ),
          b = b_1 →
            ∀ (i i_1 : Fin P.cellCount),
              i = i_1 →
                RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts hN P a b i =
                  RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts_1 hN P a_1 b_1 i_1
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timeCellCount.eq_1 : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (a b : ℝ)
  (i : Fin P.cellCount),
  RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts hN P a b i =
    {j ∈ RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b | P.classify (cuts.profile hN j) = i}.card
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timeCellCount_closed_bounds : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 2 ≤ N) (P : TimeProfile.BorelPartition k) (a b : ℝ)
  (i : Fin P.cellCount),
  RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts ⋯ P a b i ≤ TimeProfile.intervalCount cuts ⋯ P a b i ∧
    TimeProfile.intervalCount cuts ⋯ P a b i ≤ RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts ⋯ P a b i + 1
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timeCellCount_closed_error : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 2 ≤ N) (P : TimeProfile.BorelPartition k) (a b : ℝ)
  (i : Fin P.cellCount),
  |↑(TimeProfile.intervalCount cuts ⋯ P a b i) / TimeProfile.logScale N -
        ↑(RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts ⋯ P a b i) / TimeProfile.logScale N| ≤
    1 / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timeCellCount_weighted_sum : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (a b : ℝ)
  (weight : Fin P.cellCount → ℝ),
  ∑ i : Fin P.cellCount,
      weight i * (↑(RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts hN P a b i) / TimeProfile.logScale N) =
    (∑ j ∈ RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b, weight (P.classify (cuts.profile hN j))) /
      TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timeCellCount_weighted_sum_raw : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (a b : ℝ)
  (weight : Fin P.cellCount → ℝ),
  ∑ i : Fin P.cellCount, weight i * ↑(RiffleLowerV2.ProfileTransfer.Compat.timeCellCount cuts hN P a b i) =
    ∑ j ∈ RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b, weight (P.classify (cuts.profile hN j))
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timePositions : ℕ → (K : ℕ) → ℝ → ℝ → Finset (Fin K)
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timePositions.eq_1 : ∀ (N K : ℕ) (a b : ℝ),
  RiffleLowerV2.ProfileTransfer.Compat.timePositions N K a b =
    {j : Fin K | a < TimeProfile.columnTime N j ∧ TimeProfile.columnTime N j ≤ b}
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timePositions_card : ∀ {N : ℕ},
  2 ≤ N →
    ∀ {T a b : ℝ},
      0 ≤ a →
        a ≤ b →
          b ≤ T →
            (RiffleLowerV2.ProfileTransfer.Compat.timePositions N (TimeProfile.horizonDepth N T) a b).card =
              ⌊b * TimeProfile.logScale N⌋₊ - ⌊a * TimeProfile.logScale N⌋₊
```

```lean
RiffleLowerV2.ProfileTransfer.Compat.timePositions_count_error : ∀ {N : ℕ},
  2 ≤ N →
    ∀ {T a b : ℝ},
      0 ≤ a →
        a ≤ b →
          b ≤ T →
            |↑(RiffleLowerV2.ProfileTransfer.Compat.timePositions N (TimeProfile.horizonDepth N T) a b).card /
                    TimeProfile.logScale N -
                  (b - a)| ≤
              1 / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.alphaDomain_nonempty : (Set.Icc 3 4).Nonempty
```

```lean
RiffleLowerV2.ProfileTransfer.alphaInf_bounds : ∀ (f : ℝ → ℝ) (C : ℝ), (∀ a ∈ Set.Icc 3 4, |f a| ≤ C) → -C ≤ sInf (f '' Set.Icc 3 4) ∧ sInf (f '' Set.Icc 3 4) ≤ C
```

```lean
RiffleLowerV2.ProfileTransfer.alphaInf_le_add : ∀ (f g : ℝ → ℝ) (C d : ℝ),
  (∀ a ∈ Set.Icc 3 4, |f a| ≤ C) →
    (∀ a ∈ Set.Icc 3 4, f a ≤ g a + d) → sInf (f '' Set.Icc 3 4) ≤ sInf (g '' Set.Icc 3 4) + d
```

```lean
RiffleLowerV2.ProfileTransfer.columnFraction_mono : ∀ {K N : ℕ}, 2 ≤ N → ∀ (j : Fin K), Monotone (RiffleLowerV2.columnFraction N j)
```

```lean
RiffleLowerV2.ProfileTransfer.columnFraction_sum : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {t : ℝ},
      0 ≤ t →
        t ≤ RiffleLowerV2.horizon N K → ∑ j : Fin K, RiffleLowerV2.columnFraction N j t = t * TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.continuousOn_empiricalIntegral_param : ∀ {K N : ℕ} {D : Set ℝ} {f : ℝ → Fin K → ℝ},
  (∀ (j : Fin K), ContinuousOn (fun (a : ℝ) => f a j) D) →
    ∀ (r s : ℝ), ContinuousOn (fun (a : ℝ) => RiffleLowerV2.empiricalIntegral N (f a) r s) D
```

```lean
RiffleLowerV2.ProfileTransfer.continuous_columnFraction : ∀ {K N : ℕ} (j : Fin K), Continuous (RiffleLowerV2.columnFraction N j)
```

```lean
RiffleLowerV2.ProfileTransfer.continuous_empiricalIntegral : ∀ {K N : ℕ} (f : Fin K → ℝ), Continuous fun (rs : ℝ × ℝ) => RiffleLowerV2.empiricalIntegral N f rs.1 rs.2
```

```lean
RiffleLowerV2.ProfileTransfer.continuous_maxCost : ∀ {k : ℕ}, Continuous TimeProfile.maxCost
```

```lean
RiffleLowerV2.ProfileTransfer.continuous_pileMax : ∀ {k : ℕ}, Continuous TimeProfile.pileMax
```

```lean
RiffleLowerV2.ProfileTransfer.continuous_prob : ∀ {k : ℕ} (l : Fin k), Continuous fun (p : TimeProfile.Simplex k) => TimeProfile.prob p l
```

```lean
RiffleLowerV2.ProfileTransfer.continuous_psi : ∀ {k : ℕ} {α : ℝ}, α ∈ Set.Icc 2 4 → Continuous fun (p : TimeProfile.Simplex k) => TimeProfile.psi p α
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_abs_le : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f : Fin K → ℝ} {M r s : ℝ},
      (∀ (j : Fin K), |f j| ≤ M) →
        r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
          s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) → |RiffleLowerV2.empiricalIntegral N f r s| ≤ |s - r| * M
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_const : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ (c : ℝ) {r s : ℝ},
      r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
        s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
          RiffleLowerV2.empiricalIntegral N (fun (x : Fin K) => c) r s = (s - r) * c
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_endpoint_bound : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f : Fin K → ℝ} {M r s r' s' : ℝ},
      (∀ (j : Fin K), |f j| ≤ M) →
        r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
          s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
            r' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
              s' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                |RiffleLowerV2.empiricalIntegral N f r s - RiffleLowerV2.empiricalIntegral N f r' s'| ≤
                  (|r - r'| + |s - s'|) * M
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_le : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f : Fin K → ℝ} {M r s : ℝ},
      (∀ (j : Fin K), f j ≤ M) →
        0 ≤ r → r ≤ s → s ≤ RiffleLowerV2.horizon N K → RiffleLowerV2.empiricalIntegral N f r s ≤ (s - r) * M
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_linear : ∀ {K N : ℕ} (f g : Fin K → ℝ) (a r s : ℝ),
  RiffleLowerV2.empiricalIntegral N (fun (j : Fin K) => a * f j - g j) r s =
    a * RiffleLowerV2.empiricalIntegral N f r s - RiffleLowerV2.empiricalIntegral N g r s
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_mono : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f g : Fin K → ℝ},
      (∀ (j : Fin K), f j ≤ g j) →
        ∀ {r s : ℝ}, r ≤ s → RiffleLowerV2.empiricalIntegral N f r s ≤ RiffleLowerV2.empiricalIntegral N g r s
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_nonneg : ∀ {K N : ℕ},
  2 ≤ N → ∀ {f : Fin K → ℝ}, (∀ (j : Fin K), 0 ≤ f j) → ∀ {r s : ℝ}, r ≤ s → 0 ≤ RiffleLowerV2.empiricalIntegral N f r s
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_sample_error : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f : Fin K → ℝ} {M r s : ℝ},
      0 ≤ M →
        (∀ (j : Fin K), |f j| ≤ M) →
          0 ≤ r →
            r ≤ s →
              s ≤ RiffleLowerV2.horizon N K →
                |RiffleLowerV2.empiricalIntegral N f r s -
                      (∑ j : Fin K with r < TimeProfile.columnTime N j ∧ TimeProfile.columnTime N j ≤ s, f j) /
                        TimeProfile.logScale N| ≤
                  2 * M / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.empiricalIntegral_swap : ∀ {K N : ℕ} (f : Fin K → ℝ) (r s : ℝ),
  RiffleLowerV2.empiricalIntegral N f s r = -RiffleLowerV2.empiricalIntegral N f r s
```

```lean
RiffleLowerV2.ProfileTransfer.genericQuadrature : RiffleLowerV2.Targets.GenericQuadrature
```

```lean
RiffleLowerV2.ProfileTransfer.gridTime_floor_bounds : ∀ {N K : ℕ},
  2 ≤ N →
    ∀ {t : ℝ},
      0 ≤ t →
        t ≤ RiffleLowerV2.horizon N K →
          RiffleLowerV2.gridTime N ⌊t * TimeProfile.logScale N⌋₊ ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) ∧
            0 ≤ t - RiffleLowerV2.gridTime N ⌊t * TimeProfile.logScale N⌋₊ ∧
              t - RiffleLowerV2.gridTime N ⌊t * TimeProfile.logScale N⌋₊ ≤ 1 / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.integrable_maxCost : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (ν : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k)), MeasureTheory.Integrable TimeProfile.maxCost ↑ν
```

```lean
RiffleLowerV2.ProfileTransfer.integrable_of_continuous_bounded : ∀ {k : ℕ} (ν : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k)) (f : TimeProfile.Simplex k → ℝ) {M : ℝ},
  Continuous f → (∀ (p : TimeProfile.Simplex k), 0 ≤ f p ∧ f p ≤ M) → MeasureTheory.Integrable f ↑ν
```

```lean
RiffleLowerV2.ProfileTransfer.integrable_psi : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (ν : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k)) {α : ℝ},
      α ∈ Set.Icc 2 4 → MeasureTheory.Integrable (fun (p : TimeProfile.Simplex k) => TimeProfile.psi p α) ↑ν
```

```lean
RiffleLowerV2.ProfileTransfer.jointPsiContinuity : RiffleLowerV2.Targets.JointPsiContinuity
```

```lean
RiffleLowerV2.ProfileTransfer.marginTransfer : RiffleLowerV2.Targets.MarginTransferTarget
```

```lean
RiffleLowerV2.ProfileTransfer.profileMaxCost_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (μ : TimeProfile.TimeLaw k) (t : ℝ),
      0 ≤ TimeProfile.profileMaxCost μ t ∧ TimeProfile.profileMaxCost μ t ≤ Real.log ↑k
```

```lean
RiffleLowerV2.ProfileTransfer.profilePsi_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (μ : TimeProfile.TimeLaw k) (t : ℝ) {α : ℝ},
      α ∈ Set.Icc 2 4 → 0 ≤ TimeProfile.profilePsi μ t α ∧ TimeProfile.profilePsi μ t α ≤ 4 * Real.log ↑k
```

```lean
RiffleLowerV2.ProfileTransfer.profileTransfer : RiffleLowerV2.Targets.ProfileTransferTarget
```

```lean
RiffleLowerV2.ProfileTransfer.quadrature_budget : ∀ {N m : ℕ},
  2 ≤ N →
    1 ≤ m →
      ∀ {T rho phi omega M : ℝ},
        0 ≤ T →
          0 < rho →
            0 ≤ phi →
              0 ≤ omega →
                0 ≤ M →
                  RiffleLowerV2.ProfileTransfer.Compat.quadratureError N T rho phi m M (min omega M) +
                      3 * M / TimeProfile.logScale N ≤
                    2 * T * omega + M * ↑m * phi * T + 4 * M * rho +
                      (4 * M * ↑m * (T / rho + 2) + 6 * M) / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.sampledQuadrature : ∀ {k N : ℕ} (hN : 2 ≤ N) {T rho phi omega M : ℝ},
  0 < T →
    0 < rho →
      0 ≤ phi →
        0 ≤ omega →
          0 ≤ M →
            ∀ (P : TimeProfile.BorelPartition k) (μ : TimeProfile.TimeLaw k) (f : TimeProfile.Simplex k → ℝ),
              Continuous f →
                (∀ (p : TimeProfile.Simplex k), 0 ≤ f p ∧ f p ≤ M) →
                  (∀ (i : Fin P.cellCount) (p q : TimeProfile.Simplex k),
                      P.classify p = i → P.classify q = i → |f p - f q| ≤ omega) →
                    IntervalIntegrable (fun (t : ℝ) => ∫ (p : TimeProfile.Simplex k), f p ∂↑(μ t)) MeasureTheory.volume
                        0 T →
                      ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T),
                        TimeProfile.AlmostLike cuts ⋯ μ P T rho phi →
                          ∀ {r s : ℝ},
                            0 ≤ r →
                              r ≤ s →
                                s ≤ T →
                                  |(∑
                                            j ∈
                                              RiffleLowerV2.ProfileTransfer.Compat.timePositions N
                                                (TimeProfile.horizonDepth N T) r s,
                                            f (TimeProfile.Cuts.profile cuts ⋯ j)) /
                                          TimeProfile.logScale N -
                                        ∫ (t : ℝ) in r..s, ∫ (p : TimeProfile.Simplex k), f p ∂↑(μ t)| ≤
                                    RiffleLowerV2.ProfileTransfer.Compat.quadratureError N T rho phi P.cellCount M
                                        (min omega M) +
                                      M / TimeProfile.logScale N
```

```lean
RiffleLowerV2.ProfileTransfer.scalar_integral_bounds : ∀ {k : ℕ} (ν : MeasureTheory.ProbabilityMeasure (TimeProfile.Simplex k)) (f : TimeProfile.Simplex k → ℝ) {M : ℝ},
  MeasureTheory.Integrable f ↑ν →
    (∀ (p : TimeProfile.Simplex k), 0 ≤ f p ∧ f p ≤ M) →
      0 ≤ ∫ (p : TimeProfile.Simplex k), f p ∂↑ν ∧ ∫ (p : TimeProfile.Simplex k), f p ∂↑ν ≤ M
```

```lean
RiffleLowerV2.ProfileTransfer.transferChi : ℕ → ℝ → ℝ → ℝ
```

```lean
RiffleLowerV2.ProfileTransfer.transferChi_spec : ∀ {k : ℕ},
  2 ≤ k →
    ∀ {T e : ℝ},
      0 < T →
        0 < e →
          0 < RiffleLowerV2.ProfileTransfer.transferChi k T e ∧
            RiffleLowerV2.ProfileTransfer.transferChi k T e < 1 / ↑k ∧
              2 * T * RiffleLowerV2.ProfileTransfer.transferChi k T e ≤ e / 4
```

```lean
RiffleLowerV2.ProfileTransfer.transferPhi : ℕ → ℝ → ℝ → ℝ → ℝ
```

```lean
RiffleLowerV2.ProfileTransfer.transferPhi_spec : ∀ (m : ℕ) {T M e : ℝ},
  0 < T →
    0 ≤ M →
      0 < e →
        0 < RiffleLowerV2.ProfileTransfer.transferPhi m T M e ∧
          ∀ (phi : ℝ), 0 < phi → phi ≤ RiffleLowerV2.ProfileTransfer.transferPhi m T M e → M * ↑m * phi * T ≤ e / 4
```

```lean
RiffleLowerV2.ProfileTransfer.transferRho : ℝ → ℝ → ℝ → ℝ
```

```lean
RiffleLowerV2.ProfileTransfer.transferRho_spec : ∀ {M e rhoCeiling : ℝ},
  0 ≤ M →
    0 < e →
      0 < rhoCeiling →
        0 < RiffleLowerV2.ProfileTransfer.transferRho M e rhoCeiling ∧
          RiffleLowerV2.ProfileTransfer.transferRho M e rhoCeiling ≤ rhoCeiling ∧
            ∀ (rho : ℝ), 0 < rho → rho ≤ RiffleLowerV2.ProfileTransfer.transferRho M e rhoCeiling → 4 * M * rho ≤ e / 4
```

```lean
RiffleLowerV2.ProfileTransfer.transferRounding : ℕ → ℝ → ℝ → ℝ → ℝ
```

```lean
RiffleLowerV2.ProfileTransfer.transferThreshold : ℝ → ℝ → ℕ
```

```lean
RiffleLowerV2.ProfileTransfer.transferThreshold_spec : ∀ (C : ℝ) {e : ℝ},
  0 < e →
    2 ≤ RiffleLowerV2.ProfileTransfer.transferThreshold C e ∧
      ∀ (N : ℕ), RiffleLowerV2.ProfileTransfer.transferThreshold C e ≤ N → C / TimeProfile.logScale N ≤ e / 4
```

```lean
RiffleLowerV2.ProfileTransfer.transfer_error_budget : ∀ {N m : ℕ} {T M e chi rho phi : ℝ},
  0 < e →
    2 * T * chi ≤ e / 4 →
      4 * M * rho ≤ e / 4 →
        M * ↑m * phi * T ≤ e / 4 →
          RiffleLowerV2.ProfileTransfer.transferThreshold (RiffleLowerV2.ProfileTransfer.transferRounding m T M rho) e ≤
              N →
            2 * T * chi + M * ↑m * phi * T + 4 * M * rho +
                (4 * M * ↑m * (T / rho + 2) + 6 * M) / TimeProfile.logScale N ≤
              e
```

```lean
RiffleLowerV2.ProfileTransfer.variational_le_of_lift : ∀ (f g : ℝ → ℝ → ℝ → ℝ) (D E : Set (ℝ × ℝ)) (C d : ℝ),
  D.Nonempty →
    (∀ su ∈ D, ∀ a ∈ Set.Icc 3 4, |f a su.1 su.2| ≤ C) →
      (∀ su ∈ E, ∀ a ∈ Set.Icc 3 4, |g a su.1 su.2| ≤ C) →
        (∀ su ∈ D, ∃ tv ∈ E, ∀ a ∈ Set.Icc 3 4, f a su.1 su.2 ≤ g a tv.1 tv.2 + d) →
          sSup ((fun (su : ℝ × ℝ) => sInf ((fun (a : ℝ) => f a su.1 su.2) '' Set.Icc 3 4)) '' D) ≤
            sSup ((fun (su : ℝ × ℝ) => sInf ((fun (a : ℝ) => g a su.1 su.2) '' Set.Icc 3 4)) '' E) + d
```

