# Exact checked LB05 exports, version 1

All entries below are checked declarations imported by `RiffleLowerV2.Witness.Main`. The four required target proofs have no additional binders.

## RiffleLowerV2.Witness.A_bounds

RiffleLowerV2/Witness/EmpiricalTilt.lean:18

```lean
RiffleLowerV2.Witness.A_bounds : ∀ {k N K : ℕ},
  2 ≤ k →
    2 ≤ N →
      ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {r s : ℝ},
        0 ≤ r →
          r ≤ s →
            s ≤ RiffleLowerV2.horizon N K →
              0 ≤ RiffleLowerV2.A cuts hpos r s ∧ RiffleLowerV2.A cuts hpos r s ≤ (s - r) * Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.A_endpoint_bound

RiffleLowerV2/Witness/EmpiricalTilt.lean:128

```lean
RiffleLowerV2.Witness.A_endpoint_bound : ∀ {k N K : ℕ},
  2 ≤ k →
    2 ≤ N →
      ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {r s r' s' : ℝ},
        r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
          s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
            r' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
              s' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                |RiffleLowerV2.A cuts hpos r s - RiffleLowerV2.A cuts hpos r' s'| ≤ (|r - r'| + |s - s'|) * Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.A_le_J

RiffleLowerV2/Witness/EmpiricalTilt.lean:58

```lean
RiffleLowerV2.Witness.A_le_J : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s : ℝ},
          a ∈ Set.Icc 2 4 → r ≤ s → RiffleLowerV2.A cuts hpos r s ≤ RiffleLowerV2.J cuts hpos a r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.B_bounds

RiffleLowerV2/Witness/EmpiricalTilt.lean:41

```lean
RiffleLowerV2.Witness.B_bounds : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s : ℝ},
          a ∈ Set.Icc 2 4 →
            0 ≤ r →
              r ≤ s →
                s ≤ RiffleLowerV2.horizon N K →
                  0 ≤ RiffleLowerV2.B cuts hpos a r s ∧
                    RiffleLowerV2.B cuts hpos a r s ≤ (s - r) * ((a - 1) * Real.log ↑k)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.B_endpoint_bound

RiffleLowerV2/Witness/EmpiricalTilt.lean:146

```lean
RiffleLowerV2.Witness.B_endpoint_bound : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s r' s' : ℝ},
          a ∈ Set.Icc 2 4 →
            r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
              s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                r' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                  s' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                    |RiffleLowerV2.B cuts hpos a r s - RiffleLowerV2.B cuts hpos a r' s'| ≤
                      (|r - r'| + |s - s'|) * ((a - 1) * Real.log ↑k)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.B_four_ge_two

RiffleLowerV2/Witness/EmpiricalTilt.lean:74

```lean
RiffleLowerV2.Witness.B_four_ge_two : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {r s : ℝ},
          r ≤ s → 2 * RiffleLowerV2.B cuts hpos 2 r s ≤ RiffleLowerV2.B cuts hpos 4 r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.B_two_le_A

RiffleLowerV2/Witness/EmpiricalTilt.lean:64

```lean
RiffleLowerV2.Witness.B_two_le_A : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {r s : ℝ},
          r ≤ s → RiffleLowerV2.B cuts hpos 2 r s ≤ 2 * RiffleLowerV2.A cuts hpos r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.B_two_le_J

RiffleLowerV2/Witness/EmpiricalTilt.lean:86

```lean
RiffleLowerV2.Witness.B_two_le_J : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s : ℝ},
          a ∈ Set.Icc 2 4 → r ≤ s → RiffleLowerV2.B cuts hpos 2 r s ≤ 2 * RiffleLowerV2.J cuts hpos a r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.F_move_eq

RiffleLowerV2/Witness/Continuous.lean:27

```lean
RiffleLowerV2.Witness.F_move_eq : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (a s v u : ℝ),
  RiffleLowerV2.F cuts hN a s v - RiffleLowerV2.F cuts hN a s u =
    RiffleLowerV2.B cuts hN a v u - 2 * RiffleLowerV2.B cuts hN 2 v u
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.H_bounds

RiffleLowerV2/Witness/EmpiricalTilt.lean:34

```lean
RiffleLowerV2.Witness.H_bounds : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s : ℝ},
          a ∈ Set.Icc 2 4 →
            r ≤ s →
              0 ≤ RiffleLowerV2.H cuts hpos a r s ∧ RiffleLowerV2.H cuts hpos a r s ≤ RiffleLowerV2.J cuts hpos a r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.H_endpoint_bound

RiffleLowerV2/Witness/EmpiricalTilt.lean:156

```lean
RiffleLowerV2.Witness.H_endpoint_bound : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s r' s' : ℝ},
          a ∈ Set.Icc 2 4 →
            r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
              s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                r' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                  s' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                    |RiffleLowerV2.H cuts hpos a r s - RiffleLowerV2.H cuts hpos a r' s'| ≤
                      (|r - r'| + |s - s'|) * Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.H_identity

RiffleLowerV2/Witness/EmpiricalTilt.lean:50

```lean
RiffleLowerV2.Witness.H_identity : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a : ℝ},
        a ∈ Set.Icc 2 4 →
          ∀ (r s : ℝ),
            RiffleLowerV2.H cuts hpos a r s = a * RiffleLowerV2.J cuts hpos a r s - RiffleLowerV2.B cuts hpos a r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.J_bounds

RiffleLowerV2/Witness/EmpiricalTilt.lean:25

```lean
RiffleLowerV2.Witness.J_bounds : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s : ℝ},
          a ∈ Set.Icc 2 4 →
            0 ≤ r →
              r ≤ s →
                s ≤ RiffleLowerV2.horizon N K →
                  0 ≤ RiffleLowerV2.J cuts hpos a r s ∧ RiffleLowerV2.J cuts hpos a r s ≤ (s - r) * Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.J_endpoint_bound

RiffleLowerV2/Witness/EmpiricalTilt.lean:136

```lean
RiffleLowerV2.Witness.J_endpoint_bound : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {a r s r' s' : ℝ},
          a ∈ Set.Icc 2 4 →
            r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
              s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                r' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                  s' ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
                    |RiffleLowerV2.J cuts hpos a r s - RiffleLowerV2.J cuts hpos a r' s'| ≤
                      (|r - r'| + |s - s'|) * Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.antitoneOn_J_alpha

RiffleLowerV2/Witness/EmpiricalTilt.lean:108

```lean
RiffleLowerV2.Witness.antitoneOn_J_alpha : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      2 ≤ N →
        ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) {r s : ℝ},
          r ≤ s → AntitoneOn (fun (a : ℝ) => RiffleLowerV2.J cuts hpos a r s) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.antitoneOn_tiltedCost

RiffleLowerV2/Witness/OneColumn.lean:131

```lean
RiffleLowerV2.Witness.antitoneOn_tiltedCost : ∀ {k : ℕ} (p : TimeProfile.Simplex k), AntitoneOn (TimeProfile.tiltedCost p) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.coldWitness

RiffleLowerV2/Witness/Main.lean:10

```lean
RiffleLowerV2.Witness.coldWitness : RiffleLowerV2.Targets.ColdWitnessTarget
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.cold_identity

RiffleLowerV2/Witness/Selection.lean:84

```lean
RiffleLowerV2.Witness.cold_identity : ∀ (b theta jp jt hp ht bp bt : ℝ),
  hp = theta * jp - bp →
    ht = 2 * jt - bt →
      2 * (2 * b - 2 * jp - 2 * jt + hp + ht) - (b - jp + hp) =
        (theta + 3) / 2 * b - bp - 2 * bt + (theta - 3) * (jp - b / 2)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.columnFraction_mono

RiffleLowerV2/Witness/Empirical.lean:24

```lean
RiffleLowerV2.Witness.columnFraction_mono : ∀ {K N : ℕ}, 2 ≤ N → ∀ (j : Fin K), Monotone (RiffleLowerV2.columnFraction N j)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.columnFraction_sum

RiffleLowerV2/Witness/Empirical.lean:30

```lean
RiffleLowerV2.Witness.columnFraction_sum : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {t : ℝ},
      0 ≤ t →
        t ≤ RiffleLowerV2.horizon N K → ∑ j : Fin K, RiffleLowerV2.columnFraction N j t = t * TimeProfile.logScale N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_B_alpha

RiffleLowerV2/Witness/EmpiricalTilt.lean:98

```lean
RiffleLowerV2.Witness.continuousOn_B_alpha : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) (r s : ℝ),
        ContinuousOn (fun (a : ℝ) => RiffleLowerV2.B cuts hpos a r s) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_H_alpha

RiffleLowerV2/Witness/EmpiricalTilt.lean:103

```lean
RiffleLowerV2.Witness.continuousOn_H_alpha : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) (r s : ℝ),
        ContinuousOn (fun (a : ℝ) => RiffleLowerV2.H cuts hpos a r s) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_J_alpha

RiffleLowerV2/Witness/EmpiricalTilt.lean:93

```lean
RiffleLowerV2.Witness.continuousOn_J_alpha : RiffleLowerV2.Targets.OneColumnTiltTarget →
  ∀ {k N K : ℕ},
    2 ≤ k →
      ∀ (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) (r s : ℝ),
        ContinuousOn (fun (a : ℝ) => RiffleLowerV2.J cuts hpos a r s) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_empiricalIntegral_param

RiffleLowerV2/Witness/Empirical.lean:144

```lean
RiffleLowerV2.Witness.continuousOn_empiricalIntegral_param : ∀ {K N : ℕ} {D : Set ℝ} {f : ℝ → Fin K → ℝ},
  (∀ (j : Fin K), ContinuousOn (fun (a : ℝ) => f a j) D) →
    ∀ (r s : ℝ), ContinuousOn (fun (a : ℝ) => RiffleLowerV2.empiricalIntegral N (f a) r s) D
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_powerSum

RiffleLowerV2/Witness/OneColumn.lean:237

```lean
RiffleLowerV2.Witness.continuousOn_powerSum : ∀ {k : ℕ} (p : TimeProfile.Simplex k), ContinuousOn (TimeProfile.powerSum p) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_psi

RiffleLowerV2/Witness/OneColumn.lean:243

```lean
RiffleLowerV2.Witness.continuousOn_psi : ∀ {k : ℕ} (p : TimeProfile.Simplex k), ContinuousOn (TimeProfile.psi p) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_tiltedCost

RiffleLowerV2/Witness/OneColumn.lean:248

```lean
RiffleLowerV2.Witness.continuousOn_tiltedCost : ∀ {k : ℕ} (p : TimeProfile.Simplex k), ContinuousOn (TimeProfile.tiltedCost p) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousOn_tiltedEntropy

RiffleLowerV2/Witness/OneColumn.lean:263

```lean
RiffleLowerV2.Witness.continuousOn_tiltedEntropy : ∀ {k : ℕ} (p : TimeProfile.Simplex k), ContinuousOn (TimeProfile.tiltedEntropy p) (Set.Icc 2 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuousWitness

RiffleLowerV2/Witness/Continuous.lean:48

```lean
RiffleLowerV2.Witness.continuousWitness : ∀ {k N K : ℕ},
  2 ≤ k →
    2 ≤ N →
      ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {eta : ℝ},
        0 < eta →
          eta ≤ RiffleLowerV2.lambda1 cuts hN →
            ∃ (s : ℝ) (u : ℝ) (theta : ℝ),
              (s, u) ∈ RiffleLowerV2.triangle (RiffleLowerV2.horizon N K) ∧
                theta ∈ Set.Icc 3 4 ∧
                  eta / 4 ≤ RiffleLowerV2.beta cuts hN s ∧
                    RiffleLowerV2.J cuts hN theta s u ≤ RiffleLowerV2.beta cuts hN s / 2 - 4 * RiffleLowerV2.kappa eta ∧
                      (theta = 3 ∨
                          RiffleLowerV2.J cuts hN theta s u =
                            RiffleLowerV2.beta cuts hN s / 2 - 4 * RiffleLowerV2.kappa eta) ∧
                        7 * eta / 8 - 16 * RiffleLowerV2.kappa eta ≤ RiffleLowerV2.F cuts hN theta s u
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuous_B_time

RiffleLowerV2/Witness/EmpiricalTilt.lean:120

```lean
RiffleLowerV2.Witness.continuous_B_time : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) (a r : ℝ), Continuous (RiffleLowerV2.B cuts hpos a r)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuous_H_time

RiffleLowerV2/Witness/EmpiricalTilt.lean:124

```lean
RiffleLowerV2.Witness.continuous_H_time : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) (a r : ℝ), Continuous (RiffleLowerV2.H cuts hpos a r)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuous_J_time

RiffleLowerV2/Witness/EmpiricalTilt.lean:116

```lean
RiffleLowerV2.Witness.continuous_J_time : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hpos : 0 < N) (a r : ℝ), Continuous (RiffleLowerV2.J cuts hpos a r)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuous_columnFraction

RiffleLowerV2/Witness/Empirical.lean:131

```lean
RiffleLowerV2.Witness.continuous_columnFraction : ∀ {K N : ℕ} (j : Fin K), Continuous (RiffleLowerV2.columnFraction N j)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.continuous_empiricalIntegral

RiffleLowerV2/Witness/Empirical.lean:136

```lean
RiffleLowerV2.Witness.continuous_empiricalIntegral : ∀ {K N : ℕ} (f : Fin K → ℝ), Continuous fun (rs : ℝ × ℝ) => RiffleLowerV2.empiricalIntegral N f rs.1 rs.2
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_abs_le

RiffleLowerV2/Witness/Empirical.lean:93

```lean
RiffleLowerV2.Witness.empiricalIntegral_abs_le : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f : Fin K → ℝ} {M r s : ℝ},
      (∀ (j : Fin K), |f j| ≤ M) →
        r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
          s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) → |RiffleLowerV2.empiricalIntegral N f r s| ≤ |s - r| * M
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_const

RiffleLowerV2/Witness/Empirical.lean:51

```lean
RiffleLowerV2.Witness.empiricalIntegral_const : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ (c : ℝ) {r s : ℝ},
      r ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
        s ∈ Set.Icc 0 (RiffleLowerV2.horizon N K) →
          RiffleLowerV2.empiricalIntegral N (fun (x : Fin K) => c) r s = (s - r) * c
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_endpoint_bound

RiffleLowerV2/Witness/Empirical.lean:113

```lean
RiffleLowerV2.Witness.empiricalIntegral_endpoint_bound : ∀ {K N : ℕ},
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

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_le

RiffleLowerV2/Witness/Empirical.lean:76

```lean
RiffleLowerV2.Witness.empiricalIntegral_le : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f : Fin K → ℝ} {M r s : ℝ},
      (∀ (j : Fin K), f j ≤ M) →
        0 ≤ r → r ≤ s → s ≤ RiffleLowerV2.horizon N K → RiffleLowerV2.empiricalIntegral N f r s ≤ (s - r) * M
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_linear

RiffleLowerV2/Witness/Empirical.lean:152

```lean
RiffleLowerV2.Witness.empiricalIntegral_linear : ∀ {K N : ℕ} (f g : Fin K → ℝ) (a r s : ℝ),
  RiffleLowerV2.empiricalIntegral N (fun (j : Fin K) => a * f j - g j) r s =
    a * RiffleLowerV2.empiricalIntegral N f r s - RiffleLowerV2.empiricalIntegral N g r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_mono

RiffleLowerV2/Witness/Empirical.lean:59

```lean
RiffleLowerV2.Witness.empiricalIntegral_mono : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ {f g : Fin K → ℝ},
      (∀ (j : Fin K), f j ≤ g j) →
        ∀ {r s : ℝ}, r ≤ s → RiffleLowerV2.empiricalIntegral N f r s ≤ RiffleLowerV2.empiricalIntegral N g r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_nonneg

RiffleLowerV2/Witness/Empirical.lean:68

```lean
RiffleLowerV2.Witness.empiricalIntegral_nonneg : ∀ {K N : ℕ},
  2 ≤ N → ∀ {f : Fin K → ℝ}, (∀ (j : Fin K), 0 ≤ f j) → ∀ {r s : ℝ}, r ≤ s → 0 ≤ RiffleLowerV2.empiricalIntegral N f r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalIntegral_swap

RiffleLowerV2/Witness/Empirical.lean:85

```lean
RiffleLowerV2.Witness.empiricalIntegral_swap : ∀ {K N : ℕ} (f : Fin K → ℝ) (r s : ℝ),
  RiffleLowerV2.empiricalIntegral N f s r = -RiffleLowerV2.empiricalIntegral N f r s
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalTilt

RiffleLowerV2/Witness/EmpiricalTilt.lean:172

```lean
RiffleLowerV2.Witness.empiricalTilt : RiffleLowerV2.Targets.EmpiricalTiltTarget
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.empiricalTiltFrom

RiffleLowerV2/Witness/EmpiricalTilt.lean:166

```lean
RiffleLowerV2.Witness.empiricalTiltFrom : RiffleLowerV2.Targets.OneColumnTiltTarget → RiffleLowerV2.Targets.EmpiricalTiltTarget
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.endpoint_error_algebra

RiffleLowerV2/Witness/Selection.lean:156

```lean
RiffleLowerV2.Witness.endpoint_error_algebra : ∀ {theta b b0 j j0 bp bp0 bt bt0 r e : ℝ},
  theta ∈ Set.Icc 3 4 →
    0 ≤ r →
      0 ≤ e →
        |b - b0| ≤ e →
          |j - j0| ≤ r + 3 * e →
            |bp - bp0| ≤ 3 * (r + 3 * e) →
              |bt - bt0| ≤ r + 2 * e →
                |j - b / 2 - (j0 - b0 / 2)| ≤ r + 4 * e ∧
                  |(theta + 3) / 2 * b - bp - 2 * bt - ((theta + 3) / 2 * b0 - bp0 - 2 * bt0)| ≤ 5 * r + 20 * e
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.entropy_eq_cost

RiffleLowerV2/Witness/OneColumn.lean:42

```lean
RiffleLowerV2.Witness.entropy_eq_cost : ∀ {k : ℕ} (p : TimeProfile.Simplex k),
  TimeProfile.shannonEntropy (TimeProfile.prob p) =
    ∑ l : Fin k, TimeProfile.prob p l * TimeProfile.digitCost (TimeProfile.prob p l)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.entropy_eq_gibbs

RiffleLowerV2/Witness/OneColumn.lean:50

```lean
RiffleLowerV2.Witness.entropy_eq_gibbs : ∀ {k : ℕ} (q : Fin k → ℝ),
  (∀ (l : Fin k), 0 ≤ q l) →
    ∑ l : Fin k, q l = 1 →
      TimeProfile.shannonEntropy q = ∑ l : Fin k, if 0 < q l then q l * Real.log ((∑ i : Fin k, q i) / q l) else 0
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.exists_logScale_gt

RiffleLowerV2/Witness/Rounding.lean:28

```lean
RiffleLowerV2.Witness.exists_logScale_gt : ∀ (B : ℝ), ∃ (N0 : ℕ), 2 ≤ N0 ∧ ∀ (N : ℕ), N0 ≤ N → B < TimeProfile.logScale N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.exists_logScale_threshold

RiffleLowerV2/Witness/Rounding.lean:12

```lean
RiffleLowerV2.Witness.exists_logScale_threshold : ∀ (B epsilon : ℝ), 0 < epsilon → ∃ (N0 : ℕ), 2 ≤ N0 ∧ ∀ (N : ℕ), N0 ≤ N → B / TimeProfile.logScale N ≤ epsilon / 16
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.final_margins

RiffleLowerV2/Witness/Selection.lean:112

```lean
RiffleLowerV2.Witness.final_margins : ∀ {eta b theta jp jt hp ht bp bt : ℝ},
  0 < eta →
    theta ∈ Set.Icc 3 4 →
      0 ≤ jp →
        0 ≤ hp →
          hp ≤ jp →
            jp ≤ b / 2 - 3 * RiffleLowerV2.kappa eta →
              theta = 3 ∨ b / 2 - 5 * RiffleLowerV2.kappa eta ≤ jp →
                eta / 2 ≤ (theta + 3) / 2 * b - bp - 2 * bt →
                  hp = theta * jp - bp →
                    ht = 2 * jt - bt →
                      RiffleLowerV2.kappa eta ≤ b - jp + hp ∧
                        hp ≤ b - jp - RiffleLowerV2.kappa eta ∧
                          RiffleLowerV2.kappa eta ≤ 2 * b - 2 * jp - 2 * jt + hp + ht - (b - jp + hp) / 2
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.finite_gibbs

RiffleLowerV2/Witness/OneColumnBasic.lean:74

```lean
RiffleLowerV2.Witness.finite_gibbs : ∀ {k : ℕ} (p : TimeProfile.Simplex k) (c : Fin k → ℝ),
  (∀ (l : Fin k), 0 ≤ c l) →
    ∀ {theta : ℝ},
      1 ≤ theta →
        (∀ (l : Fin k), 0 < c l → 0 < TimeProfile.prob p l) →
          (∑ l : Fin k, if 0 < c l then c l * Real.log ((∑ i : Fin k, c i) / c l) else 0) ≤
            theta * ∑ l : Fin k, c l * TimeProfile.digitCost (TimeProfile.prob p l) +
              (∑ l : Fin k, c l) * Real.log (TimeProfile.powerSum p theta)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.floor_grid_error

RiffleLowerV2/Witness/Rounding.lean:37

```lean
RiffleLowerV2.Witness.floor_grid_error : ∀ {L s : ℝ}, 0 < L → 0 ≤ s → 0 ≤ s - ↑⌊s * L⌋₊ / L ∧ s - ↑⌊s * L⌋₊ / L < 1 / L
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.good_bridge_columns

RiffleLowerV2/Witness/Rounding.lean:114

```lean
RiffleLowerV2.Witness.good_bridge_columns : ∀ {k N K mu : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {rho chi density T : ℝ},
  0 < TimeProfile.logScale N →
    0 < rho →
      mu + ⌈2 * rho * TimeProfile.logScale N⌉₊ ≤ K →
        RiffleLowerV2.horizon N K ≤ T →
          3 < density * rho * TimeProfile.logScale N →
            TimeProfile.LocalGood cuts hN chi density rho 0 T →
              ∃ (gL : Fin K) (gR : Fin K),
                mu ≤ ↑gL ∧
                  ↑gL < ↑gR ∧
                    ↑gR < mu + ⌈2 * rho * TimeProfile.logScale N⌉₊ ∧
                      TimeProfile.GoodColumn (cuts.profile hN gL) chi ∧ TimeProfile.GoodColumn (cuts.profile hN gR) chi
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.lB05

RiffleLowerV2/Witness/Main.lean:37

```lean
RiffleLowerV2.Witness.lB05 : RiffleLowerV2.Targets.LB05Target
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.maxCost_bounds

RiffleLowerV2/Witness/OneColumnBasic.lean:29

```lean
RiffleLowerV2.Witness.maxCost_bounds : ∀ {k : ℕ}, 2 ≤ k → ∀ (p : TimeProfile.Simplex k), 0 ≤ TimeProfile.maxCost p ∧ TimeProfile.maxCost p ≤ Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.maxCost_le_tiltedCost

RiffleLowerV2/Witness/OneColumn.lean:175

```lean
RiffleLowerV2.Witness.maxCost_le_tiltedCost : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ}, 1 ≤ alpha → TimeProfile.maxCost p ≤ TimeProfile.tiltedCost p alpha
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.oneColumnTilt

RiffleLowerV2/Witness/OneColumn.lean:269

```lean
RiffleLowerV2.Witness.oneColumnTilt : RiffleLowerV2.Targets.OneColumnTiltTarget
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.powerSum_le_one

RiffleLowerV2/Witness/OneColumnBasic.lean:19

```lean
RiffleLowerV2.Witness.powerSum_le_one : ∀ {k : ℕ}, 2 ≤ k → ∀ (p : TimeProfile.Simplex k) {theta : ℝ}, theta ∈ Set.Icc 2 4 → TimeProfile.powerSum p theta ≤ 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.powerSum_pos

RiffleLowerV2/Witness/OneColumnBasic.lean:12

```lean
RiffleLowerV2.Witness.powerSum_pos : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {theta : ℝ}, 1 ≤ theta → 0 < TimeProfile.powerSum p theta
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.psi_bounds

RiffleLowerV2/Witness/OneColumnBasic.lean:42

```lean
RiffleLowerV2.Witness.psi_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (p : TimeProfile.Simplex k) {theta : ℝ},
      theta ∈ Set.Icc 2 4 → 0 ≤ TimeProfile.psi p theta ∧ TimeProfile.psi p theta ≤ 4 * Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.psi_four_ge_two

RiffleLowerV2/Witness/OneColumn.lean:218

```lean
RiffleLowerV2.Witness.psi_four_ge_two : ∀ {k : ℕ} (p : TimeProfile.Simplex k), 2 * TimeProfile.psi p 2 ≤ TimeProfile.psi p 4
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.psi_sharp_bounds

RiffleLowerV2/Witness/OneColumn.lean:191

```lean
RiffleLowerV2.Witness.psi_sharp_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (p : TimeProfile.Simplex k) {alpha : ℝ},
      alpha ∈ Set.Icc 2 4 → 0 ≤ TimeProfile.psi p alpha ∧ TimeProfile.psi p alpha ≤ (alpha - 1) * Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.psi_two_le_maxCost

RiffleLowerV2/Witness/OneColumn.lean:204

```lean
RiffleLowerV2.Witness.psi_two_le_maxCost : ∀ {k : ℕ} (p : TimeProfile.Simplex k), TimeProfile.psi p 2 ≤ 2 * TimeProfile.maxCost p
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.roundWitness

RiffleLowerV2/Witness/Finite.lean:13

```lean
RiffleLowerV2.Witness.roundWitness : ∀ {k N K : ℕ},
  2 ≤ k →
    2 ≤ N →
      ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {eta rho chi density T s0 u0 theta : ℝ},
        0 < eta →
          0 < rho →
            2 * rho * Real.log ↑k ≤ RiffleLowerV2.kappa eta / 100 →
              Real.log ↑k / TimeProfile.logScale N ≤ RiffleLowerV2.kappa eta / 1000 →
                RiffleLowerV2.horizon N K ≤ T →
                  3 < density * rho * TimeProfile.logScale N →
                    TimeProfile.LocalGood cuts hN chi density rho 0 T →
                      RiffleLowerV2.beta cuts hN (RiffleLowerV2.horizon N K) < RiffleLowerV2.kappa0 eta →
                        (s0, u0) ∈ RiffleLowerV2.triangle (RiffleLowerV2.horizon N K) →
                          theta ∈ Set.Icc 3 4 →
                            eta / 4 ≤ RiffleLowerV2.beta cuts hN s0 →
                              RiffleLowerV2.J cuts hN theta s0 u0 ≤
                                  RiffleLowerV2.beta cuts hN s0 / 2 - 4 * RiffleLowerV2.kappa eta →
                                theta = 3 ∨
                                    RiffleLowerV2.J cuts hN theta s0 u0 =
                                      RiffleLowerV2.beta cuts hN s0 / 2 - 4 * RiffleLowerV2.kappa eta →
                                  7 * eta / 8 - 16 * RiffleLowerV2.kappa eta ≤ RiffleLowerV2.F cuts hN theta s0 u0 →
                                    ∃ (W : RiffleLowerV2.ColdWitnessData),
                                      RiffleLowerV2.WitnessSpec cuts hN eta rho chi W
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.rounded_indices

RiffleLowerV2/Witness/Rounding.lean:48

```lean
RiffleLowerV2.Witness.rounded_indices : ∀ {K : ℕ} {L rho s u : ℝ},
  0 < L →
    0 < rho →
      0 ≤ s →
        s ≤ u →
          u ≤ ↑K / L →
            s + 2 * rho + 2 / L < ↑K / L →
              have b := ⌈2 * rho * L⌉₊;
              have ms := ⌊s * L⌋₊;
              have mu := min ⌊u * L⌋₊ (K - b);
              ms ≤ mu ∧
                mu + b ≤ K ∧ 0 ≤ s - ↑ms / L ∧ s - ↑ms / L < 1 / L ∧ 0 ≤ u - ↑mu / L ∧ u - ↑mu / L ≤ 2 * rho + 2 / L
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.rounding_margins

RiffleLowerV2/Witness/Selection.lean:92

```lean
RiffleLowerV2.Witness.rounding_margins : ∀ {eta theta j0 b0 f0 j b f : ℝ},
  0 < eta →
    j0 ≤ b0 / 2 - 4 * RiffleLowerV2.kappa eta →
      theta = 3 ∨ j0 = b0 / 2 - 4 * RiffleLowerV2.kappa eta →
        7 * eta / 8 - 16 * RiffleLowerV2.kappa eta ≤ f0 →
          |j - b / 2 - (j0 - b0 / 2)| ≤ RiffleLowerV2.kappa eta / 10 →
            |f - f0| ≤ RiffleLowerV2.kappa eta / 10 →
              eta / 2 ≤ f ∧
                j ≤ b / 2 - 3 * RiffleLowerV2.kappa eta ∧ (theta = 3 ∨ b / 2 - 5 * RiffleLowerV2.kappa eta ≤ j)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.rounding_terminal_clearance

RiffleLowerV2/Witness/Rounding.lean:98

```lean
RiffleLowerV2.Witness.rounding_terminal_clearance : ∀ {S s rho eta ell L b betaS Aend : ℝ},
  0 < eta →
    0 < ell →
      0 < L →
        eta / 4 ≤ b →
          betaS < RiffleLowerV2.kappa0 eta →
            Aend = b - betaS →
              Aend ≤ (S - s) * ell →
                2 * rho * ell ≤ RiffleLowerV2.kappa eta / 100 →
                  ell / L ≤ RiffleLowerV2.kappa eta / 400 → s + 2 * rho + 2 / L < S
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.select_tilt

RiffleLowerV2/Witness/Selection.lean:36

```lean
RiffleLowerV2.Witness.select_tilt : ∀ (j : ℝ → ℝ) (c : ℝ),
  ContinuousOn j (Set.Icc 3 4) → ∃ theta ∈ Set.Icc 3 4, (theta = 3 ∨ c ≤ j theta) ∧ (theta = 4 ∨ j theta ≤ c)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.shannonEntropy_le_log

RiffleLowerV2/Witness/OneColumn.lean:73

```lean
RiffleLowerV2.Witness.shannonEntropy_le_log : ∀ {k : ℕ}, 2 ≤ k → ∀ (p : TimeProfile.Simplex k), TimeProfile.shannonEntropy (TimeProfile.prob p) ≤ Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.shannonEntropy_nonneg

RiffleLowerV2/Witness/OneColumn.lean:62

```lean
RiffleLowerV2.Witness.shannonEntropy_nonneg : ∀ {k : ℕ} (p : TimeProfile.Simplex k), 0 ≤ TimeProfile.shannonEntropy (TimeProfile.prob p)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.shorten_selection

RiffleLowerV2/Witness/Selection.lean:50

```lean
RiffleLowerV2.Witness.shorten_selection : ∀ (j f : ℝ → ℝ → ℝ) (s u b eta : ℝ),
  0 < eta →
    s ≤ u →
      eta / 4 ≤ b →
        ContinuousOn (fun (a : ℝ) => j a u) (Set.Icc 3 4) →
          (∀ a ∈ Set.Icc 3 4, ContinuousOn (j a) (Set.Icc s u)) →
            (∀ a ∈ Set.Icc 3 4, j a s = 0) →
              (∀ a ∈ Set.Icc 3 4, 7 * eta / 8 ≤ f a u) →
                (∀ a ∈ Set.Icc 3 4, ∀ v ∈ Set.Icc s u, -4 * (j a u - j a v) ≤ f a v - f a u) →
                  (∀ v ∈ Set.Icc s u, f 4 u ≤ f 4 v) →
                    ∃ theta ∈ Set.Icc 3 4,
                      ∃ v ∈ Set.Icc s u,
                        j theta v ≤ b / 2 - 4 * RiffleLowerV2.kappa eta ∧
                          (theta = 3 ∨ j theta v = b / 2 - 4 * RiffleLowerV2.kappa eta) ∧
                            7 * eta / 8 - 16 * RiffleLowerV2.kappa eta ≤ f theta v
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.sum_tiltedWeight

RiffleLowerV2/Witness/OneColumn.lean:29

```lean
RiffleLowerV2.Witness.sum_tiltedWeight : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ}, 1 ≤ alpha → ∑ l : Fin k, TimeProfile.tiltedWeight p alpha l = 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.terminal_clearance

RiffleLowerV2/Witness/Selection.lean:137

```lean
RiffleLowerV2.Witness.terminal_clearance : ∀ {s S rb eta M L b betaS : ℝ},
  0 < eta →
    0 < M →
      0 < L →
        eta / 4 ≤ b →
          betaS < RiffleLowerV2.kappa0 eta →
            b - betaS ≤ (S - s) * M →
              rb * M ≤ RiffleLowerV2.kappa eta / 100 → M / L ≤ RiffleLowerV2.kappa eta / 1000 → s + rb + 2 / L < S
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedCost_antitone

RiffleLowerV2/Witness/OneColumn.lean:120

```lean
RiffleLowerV2.Witness.tiltedCost_antitone : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha beta : ℝ},
  1 ≤ alpha → alpha ≤ beta → TimeProfile.tiltedCost p beta ≤ TimeProfile.tiltedCost p alpha
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedCost_bounds

RiffleLowerV2/Witness/OneColumn.lean:155

```lean
RiffleLowerV2.Witness.tiltedCost_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (p : TimeProfile.Simplex k) {alpha : ℝ},
      alpha ∈ Set.Icc 2 4 → 0 ≤ TimeProfile.tiltedCost p alpha ∧ TimeProfile.tiltedCost p alpha ≤ Real.log ↑k
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedCost_eq_sum

RiffleLowerV2/Witness/OneColumn.lean:34

```lean
RiffleLowerV2.Witness.tiltedCost_eq_sum : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ},
  1 ≤ alpha →
    TimeProfile.tiltedCost p alpha =
      ∑ l : Fin k, TimeProfile.tiltedWeight p alpha l * TimeProfile.digitCost (TimeProfile.prob p l)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedCost_nonneg

RiffleLowerV2/Witness/OneColumn.lean:145

```lean
RiffleLowerV2.Witness.tiltedCost_nonneg : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ}, 1 ≤ alpha → 0 ≤ TimeProfile.tiltedCost p alpha
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedCost_one

RiffleLowerV2/Witness/OneColumn.lean:140

```lean
RiffleLowerV2.Witness.tiltedCost_one : ∀ {k : ℕ} (p : TimeProfile.Simplex k), TimeProfile.tiltedCost p 1 = TimeProfile.shannonEntropy (TimeProfile.prob p)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedEntropy_bounds

RiffleLowerV2/Witness/OneColumn.lean:164

```lean
RiffleLowerV2.Witness.tiltedEntropy_bounds : ∀ {k : ℕ},
  2 ≤ k →
    ∀ (p : TimeProfile.Simplex k) {alpha : ℝ},
      alpha ∈ Set.Icc 2 4 →
        0 ≤ TimeProfile.tiltedEntropy p alpha ∧ TimeProfile.tiltedEntropy p alpha ≤ TimeProfile.tiltedCost p alpha
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedEntropy_identity

RiffleLowerV2/Witness/OneColumn.lean:87

```lean
RiffleLowerV2.Witness.tiltedEntropy_identity : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ},
  1 ≤ alpha → TimeProfile.tiltedEntropy p alpha = alpha * TimeProfile.tiltedCost p alpha - TimeProfile.psi p alpha
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedWeight_nonneg

RiffleLowerV2/Witness/OneColumn.lean:9

```lean
RiffleLowerV2.Witness.tiltedWeight_nonneg : ∀ {k : ℕ} (p : TimeProfile.Simplex k) (alpha : ℝ) (l : Fin k), 0 ≤ TimeProfile.tiltedWeight p alpha l
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedWeight_one

RiffleLowerV2/Witness/OneColumn.lean:136

```lean
RiffleLowerV2.Witness.tiltedWeight_one : ∀ {k : ℕ} (p : TimeProfile.Simplex k) (l : Fin k), TimeProfile.tiltedWeight p 1 l = TimeProfile.prob p l
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedWeight_pos

RiffleLowerV2/Witness/OneColumn.lean:18

```lean
RiffleLowerV2.Witness.tiltedWeight_pos : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ},
  1 ≤ alpha → ∀ {l : Fin k}, 0 < TimeProfile.prob p l → 0 < TimeProfile.tiltedWeight p alpha l
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedWeight_support

RiffleLowerV2/Witness/OneColumn.lean:22

```lean
RiffleLowerV2.Witness.tiltedWeight_support : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ},
  1 ≤ alpha → ∀ {l : Fin k}, 0 < TimeProfile.tiltedWeight p alpha l → 0 < TimeProfile.prob p l
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tiltedWeight_zero

RiffleLowerV2/Witness/OneColumn.lean:14

```lean
RiffleLowerV2.Witness.tiltedWeight_zero : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha : ℝ},
  1 ≤ alpha → ∀ {l : Fin k}, TimeProfile.prob p l = 0 → TimeProfile.tiltedWeight p alpha l = 0
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.tilted_gibbs

RiffleLowerV2/Witness/OneColumn.lean:111

```lean
RiffleLowerV2.Witness.tilted_gibbs : ∀ {k : ℕ} (p : TimeProfile.Simplex k) {alpha beta : ℝ},
  1 ≤ alpha →
    1 ≤ beta → TimeProfile.tiltedEntropy p alpha ≤ beta * TimeProfile.tiltedCost p alpha - TimeProfile.psi p beta
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Witness.variational_pair

RiffleLowerV2/Witness/Selection.lean:9

```lean
RiffleLowerV2.Witness.variational_pair : ∀ (f : ℝ → ℝ → ℝ → ℝ) (T eta M : ℝ),
  0 ≤ T →
    0 < eta →
      (∀ su ∈ RiffleLowerV2.triangle T, ContinuousOn (fun (a : ℝ) => f a su.1 su.2) (Set.Icc 3 4)) →
        (∀ su ∈ RiffleLowerV2.triangle T, f 3 su.1 su.2 ≤ M) →
          eta ≤
              sSup
                ((fun (su : ℝ × ℝ) => sInf ((fun (a : ℝ) => f a su.1 su.2) '' Set.Icc 3 4)) ''
                  RiffleLowerV2.triangle T) →
            ∃ (s : ℝ) (u : ℝ), (s, u) ∈ RiffleLowerV2.triangle T ∧ ∀ a ∈ Set.Icc 3 4, 7 * eta / 8 ≤ f a s u
```

Axiom closure: propext, Classical.choice, Quot.sound.
