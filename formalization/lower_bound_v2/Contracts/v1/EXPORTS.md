# Exact compiled exports — LB-00 v1

Generated from the compiled Lean environment. **A definition of a proposition is only a checked statement, not a proof.** Every downstream target below remains pending. Theorems listed here are routine shared foundation adapters only.

## RiffleLowerV2.A

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:26`.

```lean
RiffleLowerV2.A : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.B

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:28`.

```lean
RiffleLowerV2.B : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ → ℝ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.BridgeSpec

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:228`.

```lean
RiffleLowerV2.BridgeSpec : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      ℝ →
        ℝ →
          {P : TimeProfile.BorelPartition k} →
            {W : RiffleLowerV2.ColdWitnessData} → RiffleLowerV2.ColdGeometryData K P W → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.ColdGeometryData

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:150`.

```lean
RiffleLowerV2.ColdGeometryData : {k : ℕ} → ℕ → TimeProfile.BorelPartition k → RiffleLowerV2.ColdWitnessData → Type
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.ColdLocalization

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:288`.

```lean
RiffleLowerV2.ColdLocalization : {k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → RiffleLowerV2.Sample cuts → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.ColdWitnessData

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:31`.

```lean
RiffleLowerV2.ColdWitnessData : Type
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.ColdWitnessData.s

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:37`.

```lean
RiffleLowerV2.ColdWitnessData.s : RiffleLowerV2.ColdWitnessData → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.ColdWitnessData.u

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:38`.

```lean
RiffleLowerV2.ColdWitnessData.u : RiffleLowerV2.ColdWitnessData → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.F

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:36`.

```lean
RiffleLowerV2.F : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ → ℝ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.GeometrySpec

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:245`.

```lean
RiffleLowerV2.GeometrySpec : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      ℝ →
        ℝ →
          ℝ →
            ℝ →
              (P : TimeProfile.BorelPartition k) →
                (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.H

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:32`.

```lean
RiffleLowerV2.H : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ → ℝ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.HasIncreasingRun

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:68`.

```lean
RiffleLowerV2.HasIncreasingRun : {N : ℕ} → RiffleLowerV2.Permutation N → ℕ → Prop
```

Axiom closure: `Quot.sound`.

## RiffleLowerV2.IsCanonicalMaxWord

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:224`.

```lean
RiffleLowerV2.IsCanonicalMaxWord : {k N K : ℕ} → TimeProfile.Cuts k N K → RiffleLowerV2.Word k K → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.J

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:30`.

```lean
RiffleLowerV2.J : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ → ℝ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.PathEdges

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:9`.

```lean
RiffleLowerV2.PathEdges : ℕ → Type
```

Axiom closure: `Quot.sound`, `propext`.

## RiffleLowerV2.Permutation

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:12`.

```lean
RiffleLowerV2.Permutation : ℕ → Type
```

Axiom closure: none.

## RiffleLowerV2.Prefix

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:11`.

```lean
RiffleLowerV2.Prefix : ℕ → ℕ → Type
```

Axiom closure: none.

## RiffleLowerV2.RoundedTypeData

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:70`.

```lean
RiffleLowerV2.RoundedTypeData : {k : ℕ} → TimeProfile.BorelPartition k → Type
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.RowPrescription

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:20`.

```lean
RiffleLowerV2.RowPrescription : ℕ → ℕ → ℕ → ℕ → Type
```

Axiom closure: none.

## RiffleLowerV2.Sample

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:13`.

```lean
RiffleLowerV2.Sample : {k N K : ℕ} → TimeProfile.Cuts k N K → Type
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.ScalarIntegrable

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:54`.

```lean
RiffleLowerV2.ScalarIntegrable : {k : ℕ} → TimeProfile.TimeLaw k → TimeProfile.BorelPartition k → ℝ → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.AllPrefixConcentration

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:55`.

```lean
RiffleLowerV2.Targets.AllPrefixConcentration : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ N →
    ∀ (ε : ℝ),
      0 < ε →
        (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
            ¬RiffleLowerV2.allPrefixEvent ε ω) ≤
          RiffleLowerV2.prefixFailure N k K ε
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.BernoulliMGF

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:58`.

```lean
RiffleLowerV2.Targets.BernoulliMGF : Prop
-- Target statement:
∀ (Ω : Type) [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop) (t : ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (t * ((if A ω then 1 else 0) - RiffleLowerV2.probability P A))) ≤
    Real.exp (t ^ 2 / 8)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.BonferroniProduct

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:31`.

```lean
RiffleLowerV2.Targets.BonferroniProduct : Prop
-- Target statement:
∀ (m : ℕ),
  2 ≤ m →
    Even m →
      ∀ (x y : ℕ),
        (0 ≤ RiffleLowerV2.bonferroni m x * RiffleLowerV2.bonferroni m y - if 2 ≤ x ∧ 2 ≤ y then 1 else 0) ∧
          (RiffleLowerV2.bonferroni m x * RiffleLowerV2.bonferroni m y - if 2 ≤ x ∧ 2 ≤ y then 1 else 0) ≤
            RiffleLowerV2.bonferroniRemainder m x + RiffleLowerV2.bonferroniRemainder m y +
              RiffleLowerV2.bonferroniRemainder m x * RiffleLowerV2.bonferroniRemainder m y
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.BonferroniSandwich

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:26`.

```lean
RiffleLowerV2.Targets.BonferroniSandwich : Prop
-- Target statement:
∀ (m : ℕ),
  2 ≤ m →
    Even m →
      ∀ (n : ℕ),
        (0 ≤ RiffleLowerV2.bonferroni m n - if 2 ≤ n then 1 else 0) ∧
          (RiffleLowerV2.bonferroni m n - if 2 ≤ n then 1 else 0) ≤ RiffleLowerV2.bonferroniRemainder m n
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.BoundaryAscentProbability

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:53`.

```lean
RiffleLowerV2.Targets.BoundaryAscentProbability : Prop
-- Target statement:
∀ (N : ℕ) (A B : Finset (Fin N)),
  Disjoint A B →
    (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        ∀ x ∈ A, ∀ y ∈ B, π x < π y) =
      1 / ↑((A.card + B.card).choose A.card)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.CentralComparison

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:38`.

```lean
RiffleLowerV2.Targets.CentralComparison : Prop
-- Target statement:
∀ (Ω : Type) [inst : Fintype Ω] (P : PMF Ω) (X Y : Ω → ℕ) (μ ν ε : ℝ) (m : ℕ),
  0 < μ →
    0 < ν →
      0 ≤ ε →
        ε ≤ 1 →
          2 ≤ m →
            Even m →
              (∀ (r s : ℕ),
                  r + s ≤ 2 * m →
                    |(RiffleLowerV2.expect P fun (ω : Ω) =>
                            RiffleLowerV2.falling (X ω) r * RiffleLowerV2.falling (Y ω) s) -
                          μ ^ r * ν ^ s| ≤
                      ε * μ ^ r * ν ^ s) →
                |(RiffleLowerV2.probability P fun (ω : Ω) => 2 ≤ X ω ∧ 2 ≤ Y ω) -
                      RiffleLowerV2.poissonCollision μ * RiffleLowerV2.poissonCollision ν| ≤
                  ε * (1 + μ) * (1 + ν) * Real.exp (μ + ν) +
                    3 *
                      (RiffleLowerV2.poissonRemainder m μ + RiffleLowerV2.poissonRemainder m ν +
                        RiffleLowerV2.poissonRemainder m μ * RiffleLowerV2.poissonRemainder m ν)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.CentralComparisonOne

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:47`.

```lean
RiffleLowerV2.Targets.CentralComparisonOne : Prop
-- Target statement:
∀ (Ω : Type) [inst : Fintype Ω] (P : PMF Ω) (X : Ω → ℕ) (μ ε : ℝ) (m : ℕ),
  0 < μ →
    0 ≤ ε →
      ε ≤ 1 →
        2 ≤ m →
          Even m →
            (∀ r ≤ m, |(RiffleLowerV2.expect P fun (ω : Ω) => RiffleLowerV2.falling (X ω) r) - μ ^ r| ≤ ε * μ ^ r) →
              |(RiffleLowerV2.probability P fun (ω : Ω) => 2 ≤ X ω) - RiffleLowerV2.poissonCollision μ| ≤
                ε * (1 + μ) * Real.exp μ + 3 * RiffleLowerV2.poissonRemainder m μ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:41`.

```lean
RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T eta rho chiGood density : ℝ),
      0 < T →
        0 < eta →
          0 < rho →
            0 < chiGood →
              0 < density →
                2 * rho * Real.log ↑k ≤ RiffleLowerV2.kappa0 eta / 100 →
                  ∃ (xi : ℝ),
                    0 < xi ∧
                      xi < 1 / (4 * ↑k) ∧
                        ∃ (P : TimeProfile.BorelPartition k),
                          P.IsRegular xi 1 ∧
                            ∀ (epsilon : ℝ),
                              0 < epsilon →
                                ∃ (N0 : ℕ),
                                  2 ≤ N0 ∧
                                    ∀ (N : ℕ),
                                      N0 ≤ N →
                                        ∀ (cuts : TimeProfile.Cuts k N (TimeProfile.horizonDepth N T)) (hN : 0 < N),
                                          eta ≤ RiffleLowerV2.lambda1 cuts hN →
                                            RiffleLowerV2.beta cuts hN
                                                  (RiffleLowerV2.horizon N (TimeProfile.horizonDepth N T)) <
                                                RiffleLowerV2.kappa0 eta →
                                              TimeProfile.LocalGood cuts hN chiGood density rho 0 T →
                                                ∃ (W : RiffleLowerV2.ColdWitnessData) (G :
                                                  RiffleLowerV2.ColdGeometryData (TimeProfile.horizonDepth N T) P W),
                                                  RiffleLowerV2.WitnessSpec cuts hN eta rho chiGood W ∧
                                                    RiffleLowerV2.GeometrySpec cuts hN eta rho chiGood xi P W G ∧
                                                      1 - epsilon ≤
                                                        RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                                          (RiffleLowerV2.ColdLocalization hN P W G)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ColdOnlyTarget

PENDING target; statement checked. Source: `Contracts/v1/Endpoints.lean:88`.

```lean
RiffleLowerV2.Targets.ColdOnlyTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T etaCold : ℝ),
      0 < T →
        0 < etaCold →
          ∀ (chiGood gamma rho : ℝ),
            RiffleLowerV2.Targets.ColdParameters k etaCold chiGood gamma rho →
              ∀ (epsilon : ℝ),
                0 < epsilon →
                  ∃ (N0 : ℕ),
                    2 ≤ N0 ∧
                      ∀ (N : ℕ) (hN : 2 ≤ N),
                        N0 ≤ N →
                          ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T),
                            TimeProfile.LocalGood cuts ⋯ chiGood gamma rho 0 T →
                              etaCold ≤ RiffleLowerV2.lambda1 cuts ⋯ →
                                RiffleLowerV2.beta cuts ⋯ (RiffleLowerV2.horizon N (TimeProfile.horizonDepth N T)) <
                                    RiffleLowerV2.kappa0 etaCold →
                                  1 - epsilon ≤
                                    RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts)
                                      (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ColdParameters

DEFINED and type checked. Source: `Contracts/v1/Endpoints.lean:69`.

```lean
RiffleLowerV2.Targets.ColdParameters : ℕ → ℝ → ℝ → ℝ → ℝ → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ColdWitnessTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:10`.

```lean
RiffleLowerV2.Targets.ColdWitnessTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T eta rho chiGood density : ℝ),
      0 < T →
        0 < eta →
          0 < rho →
            0 < chiGood →
              0 < density →
                2 * rho * Real.log ↑k ≤ RiffleLowerV2.kappa eta / 100 →
                  ∃ (N0 : ℕ),
                    2 ≤ N0 ∧
                      ∀ (N : ℕ),
                        N0 ≤ N →
                          ∀ (cuts : TimeProfile.Cuts k N (TimeProfile.horizonDepth N T)) (hN : 0 < N),
                            eta ≤ RiffleLowerV2.lambda1 cuts hN →
                              RiffleLowerV2.beta cuts hN (RiffleLowerV2.horizon N (TimeProfile.horizonDepth N T)) <
                                  RiffleLowerV2.kappa0 eta →
                                TimeProfile.LocalGood cuts hN chiGood density rho 0 T →
                                  ∃ (W : RiffleLowerV2.ColdWitnessData),
                                    RiffleLowerV2.WitnessSpec cuts hN eta rho chiGood W
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.CollisionChebyshev

PENDING target; statement checked. Source: `Contracts/v1/AssemblyInputs.lean:25`.

```lean
RiffleLowerV2.Targets.CollisionChebyshev : Prop
-- Target statement:
∀ (c C : ℝ),
  0 < c →
    0 < C →
      ∃ (D : ℝ),
        0 < D ∧
          ∃ (N0 : ℕ),
            ∀ N ≥ N0,
              ∀ (k K : ℕ),
                ↑K ≤ C * TimeProfile.logScale N →
                  ∀ (cuts : TimeProfile.Cuts k N K) (W : Finset (RiffleLowerV2.Word k K)),
                    RiffleLowerV2.selectedPiles cuts W c →
                      ∀ (t : ℝ),
                        0 < t →
                          0 < RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.collisionCount W) →
                            (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                fun (ω : TimeProfile.ShuffleSample cuts) =>
                                t *
                                    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
                                      (RiffleLowerV2.collisionCount W) ≤
                                  |RiffleLowerV2.collisionCount W ω -
                                      RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
                                        (RiffleLowerV2.collisionCount W)|) ≤
                              1 /
                                  (t ^ 2 *
                                    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
                                      (RiffleLowerV2.collisionCount W)) +
                                D * ↑N ^ (-1 / 100) / t ^ 2
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ColumnIndependence

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:10`.

```lean
RiffleLowerV2.Targets.ColumnIndependence : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (f : (j : Fin K) → TimeProfile.ColumnAssignments cuts j → ℝ),
  (RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      ∏ j : Fin K, f j (ω j)) =
    ∏ j : Fin K, RiffleLowerV2.expect (TimeProfile.columnPMF cuts j) (f j)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ComponentComparison

PENDING target; statement checked. Source: `Contracts/v1/Ascent.lean:25`.

```lean
RiffleLowerV2.Targets.ComponentComparison : Prop
-- Target statement:
∀ (N : ℕ) (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) (M s : ℝ),
  0 < M →
    ↑H.card ≤ M →
      0 < s →
        have Δ := ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges H)) / 6 - ↑(RiffleLowerV2.boundary H).card - s;
        0 < Δ →
          (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
              ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π)) ≤
                ↑(Finset.card (RiffleLowerV2.internalEdges H)) / 2 + s) ≤
            Real.exp (-Δ ^ 2 / M)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ComponentConcentration

PENDING target; statement checked. Source: `Contracts/v1/Ascent.lean:8`.

```lean
RiffleLowerV2.Targets.ComponentConcentration : Prop
-- Target statement:
∀ (N : ℕ) (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) (M t : ℝ),
  0 < M →
    ↑H.card ≤ M →
      0 < t →
        have X := fun (π : RiffleLowerV2.Permutation N) =>
          ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π));
        have E := RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) X;
        (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
              t ≤ X π - E) ≤
            Real.exp (-t ^ 2 / M) ∧
          (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
              X π - E ≤ -t) ≤
            Real.exp (-t ^ 2 / M)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ComponentConcentrationTwoSided

PENDING target; statement checked. Source: `Contracts/v1/AssemblyInputs.lean:10`.

```lean
RiffleLowerV2.Targets.ComponentConcentrationTwoSided : Prop
-- Target statement:
∀ (N : ℕ) (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) (M t : ℝ),
  0 < M →
    ↑H.card ≤ M →
      0 < t →
        have X := fun (π : RiffleLowerV2.Permutation N) =>
          ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π));
        (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
            t ≤ |X π - RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) X|) ≤
          2 * Real.exp (-t ^ 2 / M)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ComponentExpectation

PENDING target; statement checked. Source: `Contracts/v1/Ascent.lean:16`.

```lean
RiffleLowerV2.Targets.ComponentExpectation : Prop
-- Target statement:
∀ (N : ℕ) (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
      ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π))) ≥
    ↑(Finset.card (RiffleLowerV2.internalEdges H)) / 2 + ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges H)) / 6 -
      ↑(RiffleLowerV2.boundary H).card
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ConditionalCollisionStability

PENDING target; statement checked. Source: `Contracts/v1/TransferFinite.lean:62`.

```lean
RiffleLowerV2.Targets.ConditionalCollisionStability : Prop
-- Target statement:
∀ (c C : ℝ),
  0 < c →
    0 < C →
      ∀ (b0 : ℕ),
        ∃ (D : ℝ),
          0 < D ∧
            ∃ (N0 : ℕ),
              b0 < N0 ∧
                2 ≤ N0 ∧
                  ∀ N ≥ N0,
                    ∀ (k K b : ℕ),
                      b ≤ b0 →
                        ↑K ≤ C * TimeProfile.logScale N →
                          ∀ (cuts : TimeProfile.Cuts k N K) (p : RiffleLowerV2.RowPrescription N k K b)
                            (w : RiffleLowerV2.Word k K),
                            Function.Injective p.row →
                              0 <
                                  RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                    (RiffleLowerV2.prescriptionEvent p) →
                                (∀ (j : Fin K), c * ↑N ≤ ↑(cuts.count j (List.Vector.get w j))) →
                                  |RiffleLowerV2.conditionalProbability (TimeProfile.fixedCountPMF cuts)
                                          (fun (ω : TimeProfile.ShuffleSample cuts) =>
                                            2 ≤ RiffleLowerV2.wordCount w ω - {q : Fin b | p.word q = w}.card)
                                          (RiffleLowerV2.prescriptionEvent p) -
                                        RiffleLowerV2.poissonCollision (↑N * RiffleLowerV2.wordMass cuts w)| ≤
                                    D * ↑N ^ (-1 / 100) *
                                      RiffleLowerV2.poissonCollision (↑N * RiffleLowerV2.wordMass cuts w)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.DeterministicColdGeometryTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:100`.

```lean
RiffleLowerV2.Targets.DeterministicColdGeometryTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T eta rho chiGood : ℝ),
      0 < T →
        0 < eta →
          0 < rho →
            0 < chiGood →
              2 * rho * Real.log ↑k ≤ RiffleLowerV2.kappa0 eta / 100 →
                ∃ (xi : ℝ),
                  0 < xi ∧
                    xi < 1 / (4 * ↑k) ∧
                      ∃ (P : TimeProfile.BorelPartition k),
                        P.IsRegular xi 1 ∧
                          ∃ (N0 : ℕ),
                            2 ≤ N0 ∧
                              ∀ (N : ℕ),
                                N0 ≤ N →
                                  ∀ (cuts : TimeProfile.Cuts k N (TimeProfile.horizonDepth N T)) (hN : 0 < N)
                                    (W : RiffleLowerV2.ColdWitnessData),
                                    RiffleLowerV2.WitnessSpec cuts hN eta rho chiGood W →
                                      ∃ (G : RiffleLowerV2.ColdGeometryData (TimeProfile.horizonDepth N T) P W),
                                        RiffleLowerV2.GeometrySpec cuts hN eta rho chiGood xi P W G
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.EmpiricalAlternative

DEFINED and type checked. Source: `Contracts/v1/Endpoints.lean:106`.

```lean
RiffleLowerV2.Targets.EmpiricalAlternative : {k N : ℕ} → (T : ℝ) → RiffleLowerV2.Targets.HorizonCuts k N T → 0 < N → ℝ → ℝ → ℝ → ℝ → ℝ → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.EmpiricalCombinedTarget

PENDING target; statement checked. Source: `Contracts/v1/Endpoints.lean:116`.

```lean
RiffleLowerV2.Targets.EmpiricalCombinedTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T etaLargest etaCold : ℝ),
      0 < T →
        0 < etaLargest →
          0 < etaCold →
            ∀ (chiGood gamma rho epsilon : ℝ),
              0 < epsilon →
                ∃ (N0 : ℕ),
                  2 ≤ N0 ∧
                    ∀ (N : ℕ) (hN : 2 ≤ N),
                      N0 ≤ N →
                        ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T),
                          RiffleLowerV2.Targets.EmpiricalAlternative T cuts ⋯ etaLargest etaCold chiGood gamma rho →
                            1 - epsilon ≤
                              RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts)
                                (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.EmpiricalTiltTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:68`.

```lean
RiffleLowerV2.Targets.EmpiricalTiltTarget : Prop
-- Target statement:
∀ (k N K : ℕ),
  2 ≤ k →
    2 ≤ N →
      ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
        ∀ alpha ∈ Set.Icc 2 4,
          ∀ (r s : ℝ),
            0 ≤ r →
              r ≤ s →
                s ≤ RiffleLowerV2.horizon N K →
                  0 ≤ RiffleLowerV2.J cuts hN alpha r s ∧
                    RiffleLowerV2.J cuts hN alpha r s ≤ (s - r) * Real.log ↑k ∧
                      0 ≤ RiffleLowerV2.H cuts hN alpha r s ∧
                        RiffleLowerV2.H cuts hN alpha r s ≤ RiffleLowerV2.J cuts hN alpha r s ∧
                          RiffleLowerV2.H cuts hN alpha r s =
                            alpha * RiffleLowerV2.J cuts hN alpha r s - RiffleLowerV2.B cuts hN alpha r s
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ExactJointFactorial

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:10`.

```lean
RiffleLowerV2.Targets.ExactJointFactorial : Prop
-- Target statement:
∀ {k N K d : ℕ} (cuts : TimeProfile.Cuts k N K) (w : Fin d → RiffleLowerV2.Word k K) (r : Fin d → ℕ),
  Function.Injective w →
    ∑ i : Fin d, r i ≤ N →
      RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.factorialProduct w r) =
        RiffleLowerV2.exactFactorial cuts w r
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.FiniteLargestWordTV

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:70`.

```lean
RiffleLowerV2.Targets.FiniteLargestWordTV : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (m : ℕ),
  2 ≤ m →
    m ≤ N →
      ↑m ≤ RiffleLowerV2.maximalMean cuts hN / 2 →
        1 - Real.exp (-RiffleLowerV2.chernoffConstant * RiffleLowerV2.maximalMean cuts hN) -
            ↑(N - m + 1) / ↑m.factorial ≤
          RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.GenericQuadrature

PENDING target; statement checked. Source: `Contracts/v1/TransferFinite.lean:11`.

```lean
RiffleLowerV2.Targets.GenericQuadrature : Prop
-- Target statement:
∀ (k N : ℕ) (hN : 2 ≤ N) (T rho phi omega M : ℝ),
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
                    (∀ (i : Fin P.cellCount),
                        IntervalIntegrable (TimeProfile.cellMass μ P i) MeasureTheory.volume 0 T) →
                      IntervalIntegrable (fun (t : ℝ) => ∫ (p : TimeProfile.Simplex k), f p ∂↑(μ t))
                          MeasureTheory.volume 0 T →
                        ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T),
                          TimeProfile.AlmostLike cuts ⋯ μ P T rho phi →
                            ∀ (r s : ℝ),
                              0 ≤ r →
                                r ≤ s →
                                  s ≤ RiffleLowerV2.horizon N (TimeProfile.horizonDepth N T) →
                                    |RiffleLowerV2.empiricalIntegral N
                                            (fun (j : Fin (TimeProfile.horizonDepth N T)) =>
                                              f (TimeProfile.Cuts.profile cuts ⋯ j))
                                            r s -
                                          ∫ (t : ℝ) in r..s, ∫ (p : TimeProfile.Simplex k), f p ∂↑(μ t)| ≤
                                      2 * T * omega + M * ↑P.cellCount * phi * T + 4 * M * rho +
                                        (4 * M * ↑P.cellCount * (T / rho + 2) + 6 * M) / TimeProfile.logScale N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.GraphEventIdentity

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:19`.

```lean
RiffleLowerV2.Targets.GraphEventIdentity : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (A : RiffleLowerV2.Permutation N → Prop),
  RiffleLowerV2.probability (RiffleLowerV2.matrixLaw cuts) A =
    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        A (RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) π)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.GraphRepresentation

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:16`.

```lean
RiffleLowerV2.Targets.GraphRepresentation : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), RiffleLowerV2.matrixLaw cuts = RiffleLowerV2.graphMixtureLaw cuts
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.HorizonCuts

DEFINED and type checked. Source: `Contracts/v1/Endpoints.lean:14`.

```lean
RiffleLowerV2.Targets.HorizonCuts : ℕ → ℕ → ℝ → Type
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.HypergeometricTransform

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:26`.

```lean
RiffleLowerV2.Targets.HypergeometricTransform : Prop
-- Target statement:
∀ (M x m : ℕ),
  0 < M →
    x ≤ M →
      m ≤ M →
        ∀ (s : ℝ),
          0 < s →
            (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation M) fun (σ : RiffleLowerV2.Permutation M) =>
                s ^ {i : Fin M | ↑i < x ∧ ↑((Equiv.symm σ) i) < m}.card) ≤
              (1 - ↑m / ↑M + ↑m / ↑M * s) ^ x
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.InversionTV

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:28`.

```lean
RiffleLowerV2.Targets.InversionTV : Prop
-- Target statement:
∀ (N : ℕ) (P : PMF (RiffleLowerV2.Permutation N)),
  RiffleLowerV2.tv (PMF.map Equiv.symm P) (RiffleLowerV2.uniformPermutation N) =
    RiffleLowerV2.tv P (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.JointPsiContinuity

PENDING target; statement checked. Source: `Contracts/v1/TransferFinite.lean:27`.

```lean
RiffleLowerV2.Targets.JointPsiContinuity : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k → ContinuousOn (fun (z : TimeProfile.Simplex k × ℝ) => TimeProfile.psi z.1 z.2) (Set.univ ×ˢ Set.Icc 2 4)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.LB05Target

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:76`.

```lean
RiffleLowerV2.Targets.LB05Target : Prop
-- Target statement:
RiffleLowerV2.Targets.OneColumnTiltTarget ∧
  RiffleLowerV2.Targets.EmpiricalTiltTarget ∧ RiffleLowerV2.Targets.ColdWitnessTarget
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.LB09Target

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:112`.

```lean
RiffleLowerV2.Targets.LB09Target : Prop
-- Target statement:
RiffleLowerV2.Targets.RelativeEndpointTarget ∧
  RiffleLowerV2.Targets.DeterministicColdGeometryTarget ∧
    RiffleLowerV2.Targets.LocalizationTarget ∧ RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.LargestOnlyTarget

PENDING target; statement checked. Source: `Contracts/v1/Endpoints.lean:75`.

```lean
RiffleLowerV2.Targets.LargestOnlyTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T etaLargest : ℝ),
      0 < T →
        0 < etaLargest →
          ∀ (epsilon : ℝ),
            0 < epsilon →
              ∃ (N0 : ℕ),
                2 ≤ N0 ∧
                  ∀ (N : ℕ) (hN : 2 ≤ N),
                    N0 ≤ N →
                      ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T),
                        etaLargest ≤
                            RiffleLowerV2.beta cuts ⋯ (RiffleLowerV2.horizon N (TimeProfile.horizonDepth N T)) →
                          1 - epsilon ≤
                            RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts)
                              (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.LeastSuccessfulTranslate

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:63`.

```lean
RiffleLowerV2.Targets.LeastSuccessfulTranslate : Prop
-- Target statement:
∀ (N : ℕ) (H0 : Finset ℤ) (G : RiffleLowerV2.PathEdges N) (r : ℝ),
  (∃ (q : Fin (N + 1)), r ≤ ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q)))) →
    ∃ (q : Fin (N + 1)),
      r ≤ ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q))) ∧
        ∀ q' < q, ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q'))) < r
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.LocalizationTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:31`.

```lean
RiffleLowerV2.Targets.LocalizationTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T eta rho chiGood xi : ℝ),
      0 < T →
        0 < eta →
          0 < rho →
            0 < chiGood →
              0 < xi →
                ∀ (P : TimeProfile.BorelPartition k) (epsilon : ℝ),
                  0 < epsilon →
                    ∃ (N0 : ℕ),
                      2 ≤ N0 ∧
                        ∀ (N : ℕ),
                          N0 ≤ N →
                            ∀ (cuts : TimeProfile.Cuts k N (TimeProfile.horizonDepth N T)) (hN : 0 < N)
                              (W : RiffleLowerV2.ColdWitnessData)
                              (G : RiffleLowerV2.ColdGeometryData (TimeProfile.horizonDepth N T) P W),
                              RiffleLowerV2.WitnessSpec cuts hN eta rho chiGood W →
                                RiffleLowerV2.GeometrySpec cuts hN eta rho chiGood xi P W G →
                                  1 - epsilon ≤
                                    RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                      (RiffleLowerV2.ColdLocalization hN P W G)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.MacroscopicIntegrableTarget

PENDING target; statement checked. Source: `Contracts/v1/Endpoints.lean:138`.

```lean
RiffleLowerV2.Targets.MacroscopicIntegrableTarget : Prop
-- Target statement:
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
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ManyEdgesTarget

PENDING target; statement checked. Source: `Contracts/v1/AssemblyInputs.lean:37`.

```lean
RiffleLowerV2.Targets.ManyEdgesTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T eta rho chiGood xi : ℝ),
      0 < T →
        0 < eta →
          0 < rho →
            0 < chiGood →
              0 < xi →
                ∀ (P : TimeProfile.BorelPartition k) (epsilon : ℝ),
                  0 < epsilon →
                    ∃ (N0 : ℕ),
                      2 ≤ N0 ∧
                        ∀ (N : ℕ),
                          N0 ≤ N →
                            ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T) (hN : 0 < N)
                              (W : RiffleLowerV2.ColdWitnessData)
                              (G : RiffleLowerV2.ColdGeometryData (TimeProfile.horizonDepth N T) P W),
                              RiffleLowerV2.WitnessSpec cuts hN eta rho chiGood W →
                                RiffleLowerV2.GeometrySpec cuts hN eta rho chiGood xi P W G →
                                  have Hrel := RiffleLowerV2.coldRelativeSet cuts hN P W G;
                                  1 - epsilon ≤
                                    RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                      fun (ω : TimeProfile.ShuffleSample cuts) =>
                                      ↑Hrel.card ^ (1 / 2 + RiffleLowerV2.kappa eta / 5) ≤
                                        ↑(Finset.card
                                            (RiffleLowerV2.shuffleEdges ω ∩
                                              RiffleLowerV2.internalEdges
                                                (RiffleLowerV2.clipTranslate N Hrel
                                                  ↑(RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt W.ms G.ambient)
                                                      ω))))
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.MarginTransferTarget

PENDING target; statement checked. Source: `Contracts/v1/Endpoints.lean:40`.

```lean
RiffleLowerV2.Targets.MarginTransferTarget : Prop
-- Target statement:
∀ (k N : ℕ),
  2 ≤ k →
    ∀ (hN : 2 ≤ N) (T : ℝ),
      0 < T →
        ∀ (P : TimeProfile.BorelPartition k) (μ : TimeProfile.TimeLaw k),
          RiffleLowerV2.ScalarIntegrable μ P T →
            ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T) (e : ℝ),
              0 ≤ e →
                RiffleLowerV2.Targets.ProfileIntervalErrors T cuts ⋯ μ e →
                  RiffleLowerV2.Targets.ProfileMarginErrors T cuts ⋯ μ e
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.MaximalMeanIdentity

PENDING target; statement checked. Source: `Contracts/v1/AssemblyInputs.lean:18`.

```lean
RiffleLowerV2.Targets.MaximalMeanIdentity : Prop
-- Target statement:
∀ (k N K : ℕ),
  2 ≤ k →
    ∀ (hN : 2 ≤ N) (cuts : TimeProfile.Cuts k N K),
      ∃ (w : RiffleLowerV2.Word k K),
        RiffleLowerV2.IsCanonicalMaxWord cuts w ∧
          ↑N * RiffleLowerV2.wordMass cuts w = RiffleLowerV2.maximalMean cuts ⋯ ∧
            RiffleLowerV2.maximalMean cuts ⋯ = ↑N ^ RiffleLowerV2.beta cuts ⋯ (RiffleLowerV2.horizon N K)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.OneColumnTiltTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:55`.

```lean
RiffleLowerV2.Targets.OneColumnTiltTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (p : TimeProfile.Simplex k),
      ContinuousOn (TimeProfile.tiltedCost p) (Set.Icc 2 4) ∧
        AntitoneOn (TimeProfile.tiltedCost p) (Set.Icc 2 4) ∧
          ContinuousOn (TimeProfile.tiltedEntropy p) (Set.Icc 2 4) ∧
            ContinuousOn (TimeProfile.psi p) (Set.Icc 2 4) ∧
              (∀ alpha ∈ Set.Icc 2 4,
                  0 ≤ TimeProfile.tiltedEntropy p alpha ∧
                    TimeProfile.tiltedEntropy p alpha ≤ TimeProfile.tiltedCost p alpha ∧
                      TimeProfile.tiltedCost p alpha ≤ Real.log ↑k ∧
                        TimeProfile.maxCost p ≤ TimeProfile.tiltedCost p alpha ∧
                          0 ≤ TimeProfile.psi p alpha ∧
                            TimeProfile.psi p alpha ≤ (alpha - 1) * Real.log ↑k ∧
                              TimeProfile.tiltedEntropy p alpha =
                                alpha * TimeProfile.tiltedCost p alpha - TimeProfile.psi p alpha) ∧
                TimeProfile.psi p 2 ≤ 2 * TimeProfile.maxCost p ∧ 2 * TimeProfile.psi p 2 ≤ TimeProfile.psi p 4
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.PhysicalMatrixBridge

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:25`.

```lean
RiffleLowerV2.Targets.PhysicalMatrixBridge : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), RiffleLowerV2.physicalInverseLaw cuts = RiffleLowerV2.matrixLaw cuts
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.PrefixFailureUniform

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:59`.

```lean
RiffleLowerV2.Targets.PrefixFailureUniform : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T ε δ : ℝ),
      0 < T →
        0 < ε →
          0 < δ →
            ∃ (N0 : ℕ), ∀ N ≥ N0, ∀ (K : ℕ), ↑K ≤ T * TimeProfile.logScale N → RiffleLowerV2.prefixFailure N k K ε ≤ δ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.PrefixRanks

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:19`.

```lean
RiffleLowerV2.Targets.PrefixRanks : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (ω : RiffleLowerV2.Sample cuts) (w : RiffleLowerV2.Prefix k K),
  (∀ (i : Fin N),
      List.take (↑w.fst) (List.Vector.toList (RiffleLowerV2.sortedWord ω i)) = List.Vector.toList w.snd ↔
        RiffleLowerV2.lowerRank w ω ≤ ↑i ∧ ↑i < RiffleLowerV2.upperRank w ω) ∧
    RiffleLowerV2.upperRank w ω - RiffleLowerV2.lowerRank w ω = RiffleLowerV2.prefixCount w ω
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.PrefixTails

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:45`.

```lean
RiffleLowerV2.Targets.PrefixTails : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ (w : RiffleLowerV2.Prefix k K),
      (∀ (t : ℝ),
          0 < t →
            (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
                t ≤ |↑(RiffleLowerV2.prefixCount w ω) - RiffleLowerV2.prefixMean cuts w|) ≤
              2 * Real.exp (-t ^ 2 / (4 * (RiffleLowerV2.prefixMean cuts w + t)))) ∧
        (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
              ↑(RiffleLowerV2.prefixCount w ω) ≤ RiffleLowerV2.prefixMean cuts w / 2) ≤
            Real.exp (-RiffleLowerV2.chernoffConstant * RiffleLowerV2.prefixMean cuts w) ∧
          (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
              RiffleLowerV2.prefixCount w ω < 2) ≤
            2 * Real.exp (-RiffleLowerV2.prefixMean cuts w / 2)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ProfileIntervalErrors

DEFINED and type checked. Source: `Contracts/v1/Endpoints.lean:17`.

```lean
RiffleLowerV2.Targets.ProfileIntervalErrors : {k N : ℕ} → (T : ℝ) → RiffleLowerV2.Targets.HorizonCuts k N T → 0 < N → TimeProfile.TimeLaw k → ℝ → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ProfileMarginErrors

DEFINED and type checked. Source: `Contracts/v1/Endpoints.lean:26`.

```lean
RiffleLowerV2.Targets.ProfileMarginErrors : {k N : ℕ} → (T : ℝ) → RiffleLowerV2.Targets.HorizonCuts k N T → 0 < N → TimeProfile.TimeLaw k → ℝ → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ProfileTransferTarget

PENDING target; statement checked. Source: `Contracts/v1/Endpoints.lean:51`.

```lean
RiffleLowerV2.Targets.ProfileTransferTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T e rhoCeiling : ℝ),
      0 < T →
        0 < e →
          0 < rhoCeiling →
            ∃ (chiPartition : ℝ),
              0 < chiPartition ∧
                chiPartition < 1 / ↑k ∧
                  ∃ (P : TimeProfile.BorelPartition k),
                    P.IsRegular chiPartition 1 ∧
                      ∃ (rho0 : ℝ),
                        0 < rho0 ∧
                          rho0 ≤ rhoCeiling ∧
                            ∀ (rho : ℝ),
                              0 < rho →
                                rho ≤ rho0 →
                                  ∃ (phi0 : ℝ),
                                    0 < phi0 ∧
                                      ∀ (phi : ℝ),
                                        0 < phi →
                                          phi ≤ phi0 →
                                            ∀ (μ : TimeProfile.TimeLaw k),
                                              RiffleLowerV2.ScalarIntegrable μ P T →
                                                ∃ (N0 : ℕ),
                                                  2 ≤ N0 ∧
                                                    ∀ (N : ℕ) (hN : 2 ≤ N),
                                                      N0 ≤ N →
                                                        ∀ (cuts : RiffleLowerV2.Targets.HorizonCuts k N T),
                                                          TimeProfile.AlmostLike cuts ⋯ μ P T rho phi →
                                                            RiffleLowerV2.Targets.ProfileIntervalErrors T cuts ⋯ μ e ∧
                                                              RiffleLowerV2.Targets.ProfileMarginErrors T cuts ⋯ μ e
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.RareSandwich

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:54`.

```lean
RiffleLowerV2.Targets.RareSandwich : Prop
-- Target statement:
∀ (Ω : Type) [inst : Fintype Ω] (P : PMF Ω) (X : Ω → ℕ),
  ((RiffleLowerV2.expect P fun (ω : Ω) => RiffleLowerV2.falling (X ω) 2) / 2 -
        (RiffleLowerV2.expect P fun (ω : Ω) => RiffleLowerV2.falling (X ω) 3) / 3 ≤
      RiffleLowerV2.probability P fun (ω : Ω) => 2 ≤ X ω) ∧
    (RiffleLowerV2.probability P fun (ω : Ω) => 2 ≤ X ω) ≤
      (RiffleLowerV2.expect P fun (ω : Ω) => RiffleLowerV2.falling (X ω) 2) / 2
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.RelativeEndpointTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:78`.

```lean
RiffleLowerV2.Targets.RelativeEndpointTarget : Prop
-- Target statement:
∀ (k N K : ℕ) (cuts : TimeProfile.Cuts k N K) (a : RiffleLowerV2.Word k K) (l m : ℕ),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (omega : RiffleLowerV2.Sample cuts),
        have muA := RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a);
        have tx := RiffleLowerV2.relativeMassBefore cuts x;
        have dx := RiffleLowerV2.massOn cuts x;
        ↑(RiffleLowerV2.relativeLowerCount a l m x omega) - muA * tx =
            ∑ j : ↥(RiffleLowerV2.columnSet K l m),
              ∑ d : Fin k with d < x j,
                (↑(RiffleLowerV2.prefixCount (RiffleLowerV2.sidePrefix a l m x j d) omega) -
                  RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d)) ∧
          ↑(RiffleLowerV2.relativeUpperCount a l m x omega) - muA * (tx + dx) =
              ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.prefixAt l a) omega) - muA -
                ∑ j : ↥(RiffleLowerV2.columnSet K l m),
                  ∑ d : Fin k with x j < d,
                    (↑(RiffleLowerV2.prefixCount (RiffleLowerV2.sidePrefix a l m x j d) omega) -
                      RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d)) ∧
            ∀ (A : ℝ),
              0 < A →
                (∀ (v : RiffleLowerV2.Prefix k K),
                    |↑(RiffleLowerV2.prefixCount v omega) - RiffleLowerV2.prefixMean cuts v| ≤
                      A * (√(RiffleLowerV2.prefixMean cuts v) + 1)) →
                  |↑(RiffleLowerV2.relativeLowerCount a l m x omega) - muA * tx| +
                      |↑(RiffleLowerV2.relativeUpperCount a l m x omega) - muA * (tx + dx)| ≤
                    A * ((2 * √(↑k * ↑K) + 1) * √muA + 2 * ↑k * ↑K + 1)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.RelativeJointFactorial

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:15`.

```lean
RiffleLowerV2.Targets.RelativeJointFactorial : Prop
-- Target statement:
∀ (c C : ℝ),
  0 < c →
    0 < C →
      ∃ (D : ℝ),
        0 < D ∧
          ∃ (N0 : ℕ),
            ∀ N ≥ N0,
              ∀ (k K d : ℕ),
                ↑K ≤ C * TimeProfile.logScale N →
                  ∀ (cuts : TimeProfile.Cuts k N K) (w : Fin d → RiffleLowerV2.Word k K) (r : Fin d → ℕ),
                    Function.Injective w →
                      (∀ (i : Fin d) (j : Fin K), c * ↑N ≤ ↑(cuts.count j (List.Vector.get (w i) j))) →
                        ∑ i : Fin d, ↑(r i) ≤ ↑N ^ (1 / 5) →
                          |RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.factorialProduct w r) -
                                ∏ i : Fin d, (↑N * RiffleLowerV2.wordMass cuts (w i)) ^ r i| ≤
                            D * (↑K + 1) * (∑ i : Fin d, ↑(r i)) ^ 2 / ↑N *
                              ∏ i : Fin d, (↑N * RiffleLowerV2.wordMass cuts (w i)) ^ r i
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.RelativeOrderIndependence

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:46`.

```lean
RiffleLowerV2.Targets.RelativeOrderIndependence : Prop
-- Target statement:
∀ (N d : ℕ) (A : Fin d → Finset (Fin N)),
  (∀ (i j : Fin d), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (τ : Fin d → RiffleLowerV2.Permutation N),
      (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
          ∀ (i : Fin d), ∀ x ∈ A i, ∀ y ∈ A i, π x < π y ↔ (τ i) x < (τ i) y) =
        ∏ i : Fin d, 1 / ↑(A i).card.factorial
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ResidualJointFactorial

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:33`.

```lean
RiffleLowerV2.Targets.ResidualJointFactorial : Prop
-- Target statement:
∀ {k N K b d : ℕ} (cuts : TimeProfile.Cuts k N K) (p : RiffleLowerV2.RowPrescription N k K b),
  b < N →
    Function.Injective p.row →
      0 < RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent p) →
        ∀ (w : Fin d → RiffleLowerV2.Word k K) (r : Fin d → ℕ),
          Function.Injective w →
            ∑ i : Fin d, r i ≤ N - b →
              RiffleLowerV2.conditionalExpect (TimeProfile.fixedCountPMF cuts)
                  (fun (ω : TimeProfile.ShuffleSample cuts) =>
                    ∏ i : Fin d,
                      RiffleLowerV2.falling (RiffleLowerV2.wordCount (w i) ω - {q : Fin b | p.word q = w i}.card) (r i))
                  (RiffleLowerV2.prescriptionEvent p) =
                RiffleLowerV2.falling (N - b) (∑ i : Fin d, r i) *
                  ∏ j : Fin K,
                    (∏ a : Fin k,
                        RiffleLowerV2.falling (cuts.count j a - RiffleLowerV2.usedCount p j a)
                          (RiffleLowerV2.requestedCount w r j a)) /
                      RiffleLowerV2.falling (N - b) (∑ i : Fin d, r i)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ResidualLaw

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:65`.

```lean
RiffleLowerV2.Targets.ResidualLaw : Prop
-- Target statement:
∀ {k N K b : ℕ} (cuts : TimeProfile.Cuts k N K) (r : RiffleLowerV2.RowPrescription N k K b),
  b < N →
    Function.Injective r.row →
      0 < RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r) →
        ∃ (residual : TimeProfile.Cuts k (N - b) K),
          (∀ (j : Fin K) (a : Fin k), residual.count j a = cuts.count j a - RiffleLowerV2.usedCount r j a) ∧
            ∀ (e : Fin (N - b) → Fin N),
              Function.Injective e →
                (∀ (i : Fin N), (∃ (q : Fin (N - b)), e q = i) ↔ ¬∃ (q : Fin b), r.row q = i) →
                  ∀ (rows : Fin (N - b) → Fin K → Fin k),
                    RiffleLowerV2.conditionalProbability (TimeProfile.fixedCountPMF cuts)
                        (fun (ω : TimeProfile.ShuffleSample cuts) =>
                          ∀ (q : Fin (N - b)) (j : Fin K), TimeProfile.sampleEntry ω (e q) j = rows q j)
                        (RiffleLowerV2.prescriptionEvent r) =
                      ((PMF.map TimeProfile.sampleRow (TimeProfile.fixedCountPMF residual)) rows).toReal
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ResidualMeanComparison

PENDING target; statement checked. Source: `Contracts/v1/TransferFinite.lean:51`.

```lean
RiffleLowerV2.Targets.ResidualMeanComparison : Prop
-- Target statement:
∀ (c C : ℝ),
  0 < c →
    0 < C →
      ∀ (b0 : ℕ),
        ∃ (D : ℝ),
          0 < D ∧
            ∃ (N0 : ℕ),
              b0 < N0 ∧
                2 ≤ N0 ∧
                  ∀ N ≥ N0,
                    ∀ (k K b : ℕ),
                      b ≤ b0 →
                        ↑K ≤ C * TimeProfile.logScale N →
                          ∀ (cuts : TimeProfile.Cuts k N K) (p : RiffleLowerV2.RowPrescription N k K b)
                            (w : RiffleLowerV2.Word k K),
                            Function.Injective p.row →
                              0 <
                                  RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                    (RiffleLowerV2.prescriptionEvent p) →
                                (∀ (j : Fin K), c * ↑N ≤ ↑(cuts.count j (List.Vector.get w j))) →
                                  |RiffleLowerV2.Targets.residualWordMean cuts p w -
                                        ↑N * RiffleLowerV2.wordMass cuts w| ≤
                                    D * (↑K + 1) * ↑b / ↑N * (↑N * RiffleLowerV2.wordMass cuts w)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.ResidualRelativeFactorial

PENDING target; statement checked. Source: `Contracts/v1/TransferFinite.lean:36`.

```lean
RiffleLowerV2.Targets.ResidualRelativeFactorial : Prop
-- Target statement:
∀ (c C : ℝ),
  0 < c →
    0 < C →
      ∀ (b0 : ℕ),
        ∃ (D : ℝ),
          0 < D ∧
            ∃ (N0 : ℕ),
              b0 < N0 ∧
                2 ≤ N0 ∧
                  ∀ N ≥ N0,
                    ∀ (k K b d : ℕ),
                      b ≤ b0 →
                        ↑K ≤ C * TimeProfile.logScale N →
                          ∀ (cuts : TimeProfile.Cuts k N K) (p : RiffleLowerV2.RowPrescription N k K b),
                            Function.Injective p.row →
                              0 <
                                  RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                    (RiffleLowerV2.prescriptionEvent p) →
                                ∀ (w : Fin d → RiffleLowerV2.Word k K) (r : Fin d → ℕ),
                                  Function.Injective w →
                                    (∀ (i : Fin d) (j : Fin K), c * ↑N ≤ ↑(cuts.count j (List.Vector.get (w i) j))) →
                                      ∑ i : Fin d, ↑(r i) ≤ ↑N ^ (1 / 5) →
                                        |RiffleLowerV2.conditionalExpect (TimeProfile.fixedCountPMF cuts)
                                                (fun (ω : TimeProfile.ShuffleSample cuts) =>
                                                  ∏ i : Fin d,
                                                    RiffleLowerV2.falling
                                                      (RiffleLowerV2.wordCount (w i) ω -
                                                        {q : Fin b | p.word q = w i}.card)
                                                      (r i))
                                                (RiffleLowerV2.prescriptionEvent p) -
                                              ∏ i : Fin d, RiffleLowerV2.Targets.residualWordMean cuts p (w i) ^ r i| ≤
                                          D * (↑K + 1) * (∑ i : Fin d, ↑(r i)) ^ 2 / ↑N *
                                            ∏ i : Fin d, RiffleLowerV2.Targets.residualWordMean cuts p (w i) ^ r i
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.RoundedTypeTarget

PENDING target; statement checked. Source: `Contracts/v1/WitnessGeometry.lean:20`.

```lean
RiffleLowerV2.Targets.RoundedTypeTarget : Prop
-- Target statement:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (C : ℝ),
      0 ≤ C →
        ∃ (Ctype : ℝ),
          0 < Ctype ∧
            ∀ (T xi : ℝ),
              0 < T →
                0 < xi →
                  xi < 1 / (4 * ↑k) →
                    ∀ (m : ℕ),
                      ∃ (Cround : ℝ),
                        0 < Cround ∧
                          ∃ (N0 : ℕ),
                            2 ≤ N0 ∧
                              ∀ (N K : ℕ),
                                N0 ≤ N →
                                  ∀ (P : TimeProfile.BorelPartition k),
                                    P.cellCount = m →
                                      P.IsRegular xi C →
                                        ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (I : Finset (Fin K)),
                                          ↑I.card ≤ T * TimeProfile.logScale N →
                                            ∀ alpha ∈ Set.Icc 2 4,
                                              ∃ (D : RiffleLowerV2.RoundedTypeData P),
                                                RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha D ∧
                                                  RiffleLowerV2.TypeApproximation cuts hN P I alpha
                                                    (Ctype * T * xi * Real.log (1 / xi) +
                                                      Cround * (Real.log (TimeProfile.logScale N) + 1) /
                                                        TimeProfile.logScale N)
                                                    D
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.RowRelabeling

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:11`.

```lean
RiffleLowerV2.Targets.RowRelabeling : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (σ : RiffleLowerV2.Permutation N),
  PMF.map (fun (ω : TimeProfile.ShuffleSample cuts) (i : Fin N) => TimeProfile.sampleRow ω (σ i))
      (TimeProfile.fixedCountPMF cuts) =
    PMF.map TimeProfile.sampleRow (TimeProfile.fixedCountPMF cuts)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.StableTie

PENDING target; statement checked. Source: `Contracts/v1/AdditionalFinite.lean:15`.

```lean
RiffleLowerV2.Targets.StableTie : Prop
-- Target statement:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (ω : RiffleLowerV2.Sample cuts) (i j : Fin N),
  i < j →
    RiffleLowerV2.sortedWord ω i = RiffleLowerV2.sortedWord ω j →
      (RiffleLowerV2.stableSort ω) i < (RiffleLowerV2.stableSort ω) j
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.SuccessiveThinning

PENDING target; statement checked. Source: `Contracts/v1/ModelThinning.lean:38`.

```lean
RiffleLowerV2.Targets.SuccessiveThinning : Prop
-- Target statement:
∀ (M d : ℕ),
  0 < M →
    ∀ (m : Fin d → ℕ),
      (∀ (j : Fin d), m j ≤ M) →
        ∀ (s : ℝ),
          0 < s →
            (RiffleLowerV2.expect (PMF.uniformOfFintype (Fin d → RiffleLowerV2.Permutation M))
                  fun (ω : Fin d → RiffleLowerV2.Permutation M) => s ^ RiffleLowerV2.Targets.thinningCount m ω) ≤
                (1 - RiffleLowerV2.Targets.thinningQ M m + RiffleLowerV2.Targets.thinningQ M m * s) ^ M ∧
              (1 - RiffleLowerV2.Targets.thinningQ M m + RiffleLowerV2.Targets.thinningQ M m * s) ^ M ≤
                Real.exp (↑M * RiffleLowerV2.Targets.thinningQ M m * (s - 1))
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.UniformGraphScan

PENDING target; statement checked. Source: `Contracts/v1/Ascent.lean:34`.

```lean
RiffleLowerV2.Targets.UniformGraphScan : Prop
-- Target statement:
∀ (a δ D ε : ℝ),
  0 < a →
    0 < δ →
      0 ≤ D →
        0 < ε →
          ∃ (N0 : ℕ),
            ∀ N ≥ N0,
              ∀ (H0 : Finset ℤ) (G : RiffleLowerV2.PathEdges N),
                ↑N ^ a ≤ ↑H0.card →
                  (∀ (q : Fin (N + 1)),
                      ↑(RiffleLowerV2.boundary (RiffleLowerV2.clipTranslate N H0 ↑↑q)).card ≤ D * √↑H0.card) →
                    (∃ (q : Fin (N + 1)),
                        ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q))) ≥
                          ↑H0.card ^ (1 / 2 + δ)) →
                      (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N)
                          fun (π : RiffleLowerV2.Permutation N) =>
                          RiffleLowerV2.scan H0 (↑H0.card ^ (1 / 2 + δ / 2)) (RiffleLowerV2.componentSort G π)) ≥
                        1 - ε
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.UniformOccupancy

PENDING target; statement checked. Source: `Contracts/v1/FactorialOccupancy.lean:61`.

```lean
RiffleLowerV2.Targets.UniformOccupancy : Prop
-- Target statement:
∀ (c C : ℝ),
  0 < c →
    0 < C →
      ∃ (D : ℝ),
        0 < D ∧
          ∃ (N0 : ℕ),
            ∀ N ≥ N0,
              ∀ (k K : ℕ),
                ↑K ≤ C * TimeProfile.logScale N →
                  ∀ (cuts : TimeProfile.Cuts k N K) (W : Finset (RiffleLowerV2.Word k K)),
                    RiffleLowerV2.selectedPiles cuts W c →
                      (∀ w ∈ W,
                          |RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.collisionEvent w) -
                                RiffleLowerV2.poissonCollision (↑N * RiffleLowerV2.wordMass cuts w)| ≤
                            D * ↑N ^ (-1 / 100) * RiffleLowerV2.poissonCollision (↑N * RiffleLowerV2.wordMass cuts w)) ∧
                        (∀ w ∈ W,
                            ∀ v ∈ W,
                              w ≠ v →
                                |(RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                        fun (ω : TimeProfile.ShuffleSample cuts) =>
                                        RiffleLowerV2.collisionEvent w ω ∧ RiffleLowerV2.collisionEvent v ω) -
                                      RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                          (RiffleLowerV2.collisionEvent w) *
                                        RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                          (RiffleLowerV2.collisionEvent v)| ≤
                                  D * ↑N ^ (-1 / 100) *
                                      RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                        (RiffleLowerV2.collisionEvent w) *
                                    RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                      (RiffleLowerV2.collisionEvent v)) ∧
                          RiffleLowerV2.variance (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.collisionCount W) ≤
                            RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.collisionCount W) +
                              D * ↑N ^ (-1 / 100) *
                                RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.collisionCount W) ^
                                  2
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.UniformScan

PENDING target; statement checked. Source: `Contracts/v1/Ascent.lean:21`.

```lean
RiffleLowerV2.Targets.UniformScan : Prop
-- Target statement:
∀ (N : ℕ) (H0 : Finset ℤ) (s : ℝ),
  0 < H0.card →
    0 < s →
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) (RiffleLowerV2.scan H0 s) ≤
        (↑N + 1) * Real.exp (-s ^ 2 / ↑H0.card)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.deckPos

PROVED shared adapter. Source: `Contracts/v1/Endpoints.lean:11`.

```lean
RiffleLowerV2.Targets.deckPos : ∀ {N : ℕ}, 2 ≤ N → 0 < N
```

Axiom closure: `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.residualWordMean

DEFINED and type checked. Source: `Contracts/v1/TransferFinite.lean:32`.

```lean
RiffleLowerV2.Targets.residualWordMean : {k N K b : ℕ} → TimeProfile.Cuts k N K → RiffleLowerV2.RowPrescription N k K b → RiffleLowerV2.Word k K → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.thinningCount

DEFINED and type checked. Source: `Contracts/v1/ModelThinning.lean:33`.

```lean
RiffleLowerV2.Targets.thinningCount : {M d : ℕ} → (Fin d → ℕ) → (Fin d → RiffleLowerV2.Permutation M) → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Targets.thinningQ

DEFINED and type checked. Source: `Contracts/v1/ModelThinning.lean:36`.

```lean
RiffleLowerV2.Targets.thinningQ : {d : ℕ} → ℕ → (Fin d → ℕ) → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.TypeApproximation

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:135`.

```lean
RiffleLowerV2.TypeApproximation : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N → (P : TimeProfile.BorelPartition k) → Finset (Fin K) → ℝ → ℝ → RiffleLowerV2.RoundedTypeData P → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.TypeDataSpec

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:111`.

```lean
RiffleLowerV2.TypeDataSpec : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N → (P : TimeProfile.BorelPartition k) → Finset (Fin K) → ℝ → ℝ → RiffleLowerV2.RoundedTypeData P → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.WitnessSpec

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:40`.

```lean
RiffleLowerV2.WitnessSpec : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ → ℝ → ℝ → RiffleLowerV2.ColdWitnessData → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Word

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:10`.

```lean
RiffleLowerV2.Word : ℕ → ℕ → Type
```

Axiom closure: none.

## RiffleLowerV2.WordOn

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:13`.

```lean
RiffleLowerV2.WordOn : ℕ → {K : ℕ} → Finset (Fin K) → Type
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.allPrefixEvent

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:12`.

```lean
RiffleLowerV2.allPrefixEvent : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → ℝ → RiffleLowerV2.Sample cuts → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.ascentCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:43`.

```lean
RiffleLowerV2.ascentCount : {N : ℕ} → Finset (Fin N) → RiffleLowerV2.Permutation N → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.beta

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:34`.

```lean
RiffleLowerV2.beta : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.bonferroni

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:51`.

```lean
RiffleLowerV2.bonferroni : ℕ → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.bonferroniRemainder

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:53`.

```lean
RiffleLowerV2.bonferroniRemainder : ℕ → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.boundary

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:22`.

```lean
RiffleLowerV2.boundary : {N : ℕ} → Finset (Fin N) → Finset ℤ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.bridgeColumns

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:147`.

```lean
RiffleLowerV2.bridgeColumns : (K : ℕ) → RiffleLowerV2.ColdWitnessData → Finset (Fin K)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.cellPositionCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:79`.

```lean
RiffleLowerV2.cellPositionCount : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → (P : TimeProfile.BorelPartition k) → Finset (Fin K) → Fin P.cellCount → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.chernoffConstant

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:10`.

```lean
RiffleLowerV2.chernoffConstant : ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.clipTranslate

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:25`.

```lean
RiffleLowerV2.clipTranslate : (N : ℕ) → Finset ℤ → ℤ → Finset (Fin N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.clipTranslate_card_le

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:64`.

```lean
RiffleLowerV2.clipTranslate_card_le : ∀ (N : ℕ) (H0 : Finset ℤ) (q : ℤ), (RiffleLowerV2.clipTranslate N H0 q).card ≤ H0.card
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.coldFullFamily

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:182`.

```lean
RiffleLowerV2.coldFullFamily : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → Finset (RiffleLowerV2.Word k K)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.coldPrefixFamily

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:160`.

```lean
RiffleLowerV2.coldPrefixFamily : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) →
          RiffleLowerV2.ColdGeometryData K P W → Finset (RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.coldRelativeSet

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:195`.

```lean
RiffleLowerV2.coldRelativeSet : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → Finset ℤ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.coldTailFamily

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:164`.

```lean
RiffleLowerV2.coldTailFamily : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) →
          RiffleLowerV2.ColdGeometryData K P W → Finset (RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W))
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.collisionCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:62`.

```lean
RiffleLowerV2.collisionCount : {N k K : ℕ} → {cuts : TimeProfile.Cuts k N K} → Finset (RiffleLowerV2.Word k K) → RiffleLowerV2.Sample cuts → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.collisionEvent

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:56`.

```lean
RiffleLowerV2.collisionEvent : {N k K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Word k K → RiffleLowerV2.Sample cuts → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.columnFraction

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:16`.

```lean
RiffleLowerV2.columnFraction : {K : ℕ} → ℕ → Fin K → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.columnFraction_grid

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:19`.

```lean
RiffleLowerV2.columnFraction_grid : ∀ {K N : ℕ},
  2 ≤ N → ∀ (j : Fin K) (m : ℕ), RiffleLowerV2.columnFraction N j (RiffleLowerV2.gridTime N m) = if ↑j < m then 1 else 0
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.columnSet

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:11`.

```lean
RiffleLowerV2.columnSet : (K : ℕ) → ℕ → ℕ → Finset (Fin K)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.componentIndex

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:32`.

```lean
RiffleLowerV2.componentIndex : {N : ℕ} → RiffleLowerV2.PathEdges N → Fin N → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.componentSort

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:36`.

```lean
RiffleLowerV2.componentSort : {N : ℕ} → RiffleLowerV2.PathEdges N → RiffleLowerV2.Permutation N → RiffleLowerV2.Permutation N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.conditionalExpect

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:33`.

```lean
RiffleLowerV2.conditionalExpect : {Ω : Type u_1} → [Fintype Ω] → PMF Ω → (Ω → ℝ) → (Ω → Prop) → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.conditionalProbability

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:30`.

```lean
RiffleLowerV2.conditionalProbability : {Ω : Type u_1} → [Fintype Ω] → PMF Ω → (Ω → Prop) → (Ω → Prop) → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.edgeLeft

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:10`.

```lean
RiffleLowerV2.edgeLeft : {N : ℕ} → Fin (N - 1) → Fin N
```

Axiom closure: `Quot.sound`, `propext`.

## RiffleLowerV2.edgeRight

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:11`.

```lean
RiffleLowerV2.edgeRight : {N : ℕ} → Fin (N - 1) → Fin N
```

Axiom closure: `Quot.sound`, `propext`.

## RiffleLowerV2.empiricalIntegral

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:20`.

```lean
RiffleLowerV2.empiricalIntegral : {K : ℕ} → ℕ → (Fin K → ℝ) → ℝ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.empiricalIntegral_add

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Empirical.lean:62`.

```lean
RiffleLowerV2.empiricalIntegral_add : ∀ {K : ℕ} (N : ℕ) (f : Fin K → ℝ) (r s t : ℝ),
  RiffleLowerV2.empiricalIntegral N f r t =
    RiffleLowerV2.empiricalIntegral N f r s + RiffleLowerV2.empiricalIntegral N f s t
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.empiricalIntegral_grid

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:33`.

```lean
RiffleLowerV2.empiricalIntegral_grid : ∀ {K N : ℕ},
  2 ≤ N →
    ∀ (f : Fin K → ℝ) (a b : ℕ),
      a ≤ b →
        RiffleLowerV2.empiricalIntegral N f (RiffleLowerV2.gridTime N a) (RiffleLowerV2.gridTime N b) =
          RiffleLowerV2.gridSum N f a b
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.empiricalIntegral_self

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Empirical.lean:59`.

```lean
RiffleLowerV2.empiricalIntegral_self : ∀ {K : ℕ} (N : ℕ) (f : Fin K → ℝ) (r : ℝ), RiffleLowerV2.empiricalIntegral N f r r = 0
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.emptyPrefix_count

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:74`.

```lean
RiffleLowerV2.emptyPrefix_count : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.prefixCount ⟨⟨0, ⋯⟩, RiffleShuffle.emptyWord k⟩ ω = N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.emptyPrefix_mass

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:48`.

```lean
RiffleLowerV2.emptyPrefix_mass : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), RiffleLowerV2.prefixMass cuts ⟨⟨0, ⋯⟩, RiffleShuffle.emptyWord k⟩ = 1
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.exactFactorial

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:45`.

```lean
RiffleLowerV2.exactFactorial : {N k K d : ℕ} → TimeProfile.Cuts k N K → (Fin d → RiffleLowerV2.Word k K) → (Fin d → ℕ) → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.expect

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:16`.

```lean
RiffleLowerV2.expect : {Ω : Type u_1} → [Fintype Ω] → PMF Ω → (Ω → ℝ) → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.expect_eq_integral

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:8`.

```lean
RiffleLowerV2.expect_eq_integral : ∀ {Ω : Type u_1} [inst : Fintype Ω] [inst_1 : MeasurableSpace Ω] [MeasurableSingletonClass Ω] (P : PMF Ω) (f : Ω → ℝ),
  RiffleLowerV2.expect P f = ∫ (ω : Ω), f ω ∂P.toMeasure
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.factorialProduct

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:41`.

```lean
RiffleLowerV2.factorialProduct : {N k K d : ℕ} →
  {cuts : TimeProfile.Cuts k N K} → (Fin d → RiffleLowerV2.Word k K) → (Fin d → ℕ) → RiffleLowerV2.Sample cuts → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.falling

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:36`.

```lean
RiffleLowerV2.falling : ℕ → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.fixed_expect_eq_average

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:14`.

```lean
RiffleLowerV2.fixed_expect_eq_average : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (f : RiffleLowerV2.Sample cuts → ℝ),
  RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) f =
    (∑ ω : RiffleLowerV2.Sample cuts, f ω) / ↑(Fintype.card (RiffleLowerV2.Sample cuts))
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.fullPrefix

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:77`.

```lean
RiffleLowerV2.fullPrefix : {k K : ℕ} → RiffleLowerV2.Word k K → RiffleLowerV2.Prefix k K
```

Axiom closure: none.

## RiffleLowerV2.geometryEllB

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:210`.

```lean
RiffleLowerV2.geometryEllB : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    {P : TimeProfile.BorelPartition k} → {W : RiffleLowerV2.ColdWitnessData} → RiffleLowerV2.ColdGeometryData K P W → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.geometryEllP

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:202`.

```lean
RiffleLowerV2.geometryEllP : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.geometryG

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:218`.

```lean
RiffleLowerV2.geometryG : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.geometryH

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:206`.

```lean
RiffleLowerV2.geometryH : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.geometryZ

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:214`.

```lean
RiffleLowerV2.geometryZ : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (W : RiffleLowerV2.ColdWitnessData) → RiffleLowerV2.ColdGeometryData K P W → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.graphMixtureLaw

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:39`.

```lean
RiffleLowerV2.graphMixtureLaw : {k N K : ℕ} → TimeProfile.Cuts k N K → PMF (RiffleLowerV2.Permutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.gridSum

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:23`.

```lean
RiffleLowerV2.gridSum : {K : ℕ} → ℕ → (Fin K → ℝ) → ℕ → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.gridTime

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:13`.

```lean
RiffleLowerV2.gridTime : ℕ → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.horizon

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:11`.

```lean
RiffleLowerV2.horizon : ℕ → ℕ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.integerBoundary

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:18`.

```lean
RiffleLowerV2.integerBoundary : Finset ℤ → Finset ℤ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.integerHalfOpen

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:192`.

```lean
RiffleLowerV2.integerHalfOpen : ℝ → ℝ → Finset ℤ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.internalEdges

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:14`.

```lean
RiffleLowerV2.internalEdges : {N : ℕ} → Finset (Fin N) → RiffleLowerV2.PathEdges N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.joinColdWord

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:168`.

```lean
RiffleLowerV2.joinColdWord : {k K : ℕ} →
  {P : TimeProfile.BorelPartition k} →
    {W : RiffleLowerV2.ColdWitnessData} →
      RiffleLowerV2.ColdGeometryData K P W →
        RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W) →
          RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W) →
            RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W) → RiffleLowerV2.Word k K
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.kappa

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:44`.

```lean
RiffleLowerV2.kappa : ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.kappa0

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:45`.

```lean
RiffleLowerV2.kappa0 : ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.lambda1

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:40`.

```lean
RiffleLowerV2.lambda1 : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.lowerRank

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:68`.

```lean
RiffleLowerV2.lowerRank : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Prefix k K → RiffleLowerV2.Sample cuts → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.macroBeta

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:47`.

```lean
RiffleLowerV2.macroBeta : {k : ℕ} → TimeProfile.TimeLaw k → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.macroF

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:48`.

```lean
RiffleLowerV2.macroF : {k : ℕ} → TimeProfile.TimeLaw k → ℝ → ℝ → ℝ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.macroLambda1

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:50`.

```lean
RiffleLowerV2.macroLambda1 : {k : ℕ} → TimeProfile.TimeLaw k → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.manuscriptRank

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:12`.

```lean
RiffleLowerV2.manuscriptRank : {N : ℕ} → Fin N → ℤ
```

Axiom closure: none.

## RiffleLowerV2.massBin

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:94`.

```lean
RiffleLowerV2.massBin : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (I : Finset (Fin K)) → RiffleLowerV2.RoundedTypeData P → ℕ → Finset (RiffleLowerV2.WordOn k I)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.massOn

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:18`.

```lean
RiffleLowerV2.massOn : {k N K : ℕ} → TimeProfile.Cuts k N K → {I : Finset (Fin K)} → RiffleLowerV2.WordOn k I → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.matrixLaw

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:40`.

```lean
RiffleLowerV2.matrixLaw : {k N K : ℕ} → TimeProfile.Cuts k N K → PMF (RiffleLowerV2.Permutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.matrix_graph_adapter

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Adapters.lean:52`.

```lean
RiffleLowerV2.matrix_graph_adapter : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (hN : 0 < N) (hk : 2 ≤ k) (ω : RiffleLowerV2.Sample cuts)
  (e : Fin (N - 1)),
  e ∈ RiffleLowerV2.shuffleEdges ω ↔
    (RiffleLowerV2.toMatrix hN hk ω).shuffleGraph.Adj (RiffleLowerV2.edgeLeft e) (RiffleLowerV2.edgeRight e)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.maximalMean

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:65`.

```lean
RiffleLowerV2.maximalMean : {N k K : ℕ} → TimeProfile.Cuts k N K → 0 < N → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.mem_clipTranslate

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Path.lean:55`.

```lean
RiffleLowerV2.mem_clipTranslate : ∀ {N : ℕ} (H0 : Finset ℤ) (q : ℤ) (i : Fin N),
  i ∈ RiffleLowerV2.clipTranslate N H0 q ↔ RiffleLowerV2.manuscriptRank i - q ∈ H0
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.oneStepForward

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:44`.

```lean
RiffleLowerV2.oneStepForward : {k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} → (j : Fin K) → TimeProfile.ColumnAssignments cuts j → RiffleLowerV2.Permutation N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.physicalForward

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:49`.

```lean
RiffleLowerV2.physicalForward : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Sample cuts → RiffleLowerV2.Permutation N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.physicalForwardLaw

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:55`.

```lean
RiffleLowerV2.physicalForwardLaw : {k N K : ℕ} → TimeProfile.Cuts k N K → PMF (RiffleLowerV2.Permutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.physicalInverse

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:52`.

```lean
RiffleLowerV2.physicalInverse : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Sample cuts → RiffleLowerV2.Permutation N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.physicalInverseLaw

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:58`.

```lean
RiffleLowerV2.physicalInverseLaw : {k N K : ℕ} → TimeProfile.Cuts k N K → PMF (RiffleLowerV2.Permutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.physicalInverseLaw_eq_map

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Model.lean:97`.

```lean
RiffleLowerV2.physicalInverseLaw_eq_map : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  RiffleLowerV2.physicalInverseLaw cuts = PMF.map Equiv.symm (RiffleLowerV2.physicalForwardLaw cuts)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.poissonCollision

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:50`.

```lean
RiffleLowerV2.poissonCollision : ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.poissonRemainder

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:54`.

```lean
RiffleLowerV2.poissonRemainder : ℕ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.prefixAt

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:26`.

```lean
RiffleLowerV2.prefixAt : {k K : ℕ} → ℕ → RiffleLowerV2.Word k K → RiffleLowerV2.Prefix k K
```

Axiom closure: `Quot.sound`, `propext`.

## RiffleLowerV2.prefixColumns

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:146`.

```lean
RiffleLowerV2.prefixColumns : (K : ℕ) → RiffleLowerV2.ColdWitnessData → Finset (Fin K)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.prefixCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:65`.

```lean
RiffleLowerV2.prefixCount : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Prefix k K → RiffleLowerV2.Sample cuts → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.prefixFailure

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:16`.

```lean
RiffleLowerV2.prefixFailure : ℕ → ℕ → ℕ → ℝ → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.prefixMass

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:61`.

```lean
RiffleLowerV2.prefixMass : {k N K : ℕ} → TimeProfile.Cuts k N K → RiffleLowerV2.Prefix k K → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.prefixMean

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:74`.

```lean
RiffleLowerV2.prefixMean : {k N K : ℕ} → TimeProfile.Cuts k N K → RiffleLowerV2.Prefix k K → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.prescriptionEvent

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:24`.

```lean
RiffleLowerV2.prescriptionEvent : {N k K b : ℕ} →
  {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.RowPrescription N k K b → RiffleLowerV2.Sample cuts → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.probability

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:19`.

```lean
RiffleLowerV2.probability : {Ω : Type u_1} → [Fintype Ω] → PMF Ω → (Ω → Prop) → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.rankSet

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:21`.

```lean
RiffleLowerV2.rankSet : {N : ℕ} → Finset (Fin N) → Finset ℤ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.rank_interval_iff

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Path.lean:50`.

```lean
RiffleLowerV2.rank_interval_iff : ∀ {N L U : ℕ} (i : Fin N), L ≤ ↑i ∧ ↑i < U ↔ ↑L < RiffleLowerV2.manuscriptRank i ∧ RiffleLowerV2.manuscriptRank i ≤ ↑U
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.relativeLowerCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:311`.

```lean
RiffleLowerV2.relativeLowerCount : {k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    RiffleLowerV2.Word k K →
      (l m : ℕ) → RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m) → RiffleLowerV2.Sample cuts → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.relativeMassBefore

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:188`.

```lean
RiffleLowerV2.relativeMassBefore : {k N K : ℕ} → TimeProfile.Cuts k N K → {I : Finset (Fin K)} → RiffleLowerV2.WordOn k I → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.relativeUpperCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:317`.

```lean
RiffleLowerV2.relativeUpperCount : {k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    RiffleLowerV2.Word k K →
      (l m : ℕ) → RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m) → RiffleLowerV2.Sample cuts → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.requestedCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:38`.

```lean
RiffleLowerV2.requestedCount : {k K d : ℕ} → (Fin d → RiffleLowerV2.Word k K) → (Fin d → ℕ) → Fin K → Fin k → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.reservePrefix

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:176`.

```lean
RiffleLowerV2.reservePrefix : {k K : ℕ} →
  {P : TimeProfile.BorelPartition k} →
    {W : RiffleLowerV2.ColdWitnessData} →
      RiffleLowerV2.ColdGeometryData K P W →
        RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W) →
          RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W) → RiffleLowerV2.Prefix k K
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.restrictWord

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:22`.

```lean
RiffleLowerV2.restrictWord : {k K : ℕ} → (I : Finset (Fin K)) → RiffleLowerV2.Word k K → RiffleLowerV2.WordOn k I
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.retainedTilt

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:74`.

```lean
RiffleLowerV2.retainedTilt : {k : ℕ} → (P : TimeProfile.BorelPartition k) → ℝ → ℝ → Fin P.cellCount → Fin k → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.roundedClass

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:89`.

```lean
RiffleLowerV2.roundedClass : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (I : Finset (Fin K)) → RiffleLowerV2.RoundedTypeData P → Finset (RiffleLowerV2.WordOn k I)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.rowWord

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:30`.

```lean
RiffleLowerV2.rowWord : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Sample cuts → Fin N → RiffleLowerV2.Word k K
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.rowWord_get

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Model.lean:89`.

```lean
RiffleLowerV2.rowWord_get : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (i : Fin N) (j : Fin K),
  List.Vector.get (RiffleLowerV2.rowWord ω i) j = TimeProfile.sampleEntry ω i j
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.sample_exists

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Smoke.lean:6`.

```lean
RiffleLowerV2.sample_exists : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), Nonempty (TimeProfile.ShuffleSample cuts)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.scan

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:46`.

```lean
RiffleLowerV2.scan : {N : ℕ} → Finset ℤ → ℝ → RiffleLowerV2.Permutation N → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.selectedClass

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:100`.

```lean
RiffleLowerV2.selectedClass : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) →
        (I : Finset (Fin K)) → RiffleLowerV2.RoundedTypeData P → Finset (RiffleLowerV2.WordOn k I)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.selectedPiles

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:59`.

```lean
RiffleLowerV2.selectedPiles : {N k K : ℕ} → TimeProfile.Cuts k N K → Finset (RiffleLowerV2.Word k K) → ℝ → Prop
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.shuffleEdges

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Path.lean:28`.

```lean
RiffleLowerV2.shuffleEdges : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Sample cuts → RiffleLowerV2.PathEdges N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.sidePrefix

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:323`.

```lean
RiffleLowerV2.sidePrefix : {k K : ℕ} →
  RiffleLowerV2.Word k K →
    (l m : ℕ) →
      RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m) →
        ↥(RiffleLowerV2.columnSet K l m) → Fin k → RiffleLowerV2.Prefix k K
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.sortedWord

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:36`.

```lean
RiffleLowerV2.sortedWord : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Sample cuts → Fin N → RiffleLowerV2.Word k K
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.stableSort

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:33`.

```lean
RiffleLowerV2.stableSort : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Sample cuts → RiffleLowerV2.Permutation N
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.tailColumns

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:148`.

```lean
RiffleLowerV2.tailColumns : (K : ℕ) → RiffleLowerV2.ColdWitnessData → Finset (Fin K)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.toMatrix

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:85`.

```lean
RiffleLowerV2.toMatrix : {k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    (hN : 0 < N) →
      (hk : 2 ≤ k) → RiffleLowerV2.Sample cuts → RiffleShuffle.ShuffleMatrix (RiffleLowerV2.toPileProfile cuts hN hk)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.toMatrix_sort

PROVED shared adapter. Source: `RiffleLowerV2/Shared/Model.lean:93`.

```lean
RiffleLowerV2.toMatrix_sort : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (hN : 0 < N) (hk : 2 ≤ k) (ω : RiffleLowerV2.Sample cuts),
  (RiffleLowerV2.toMatrix hN hk ω).sortPerm = RiffleLowerV2.stableSort ω
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.toPileProfile

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:82`.

```lean
RiffleLowerV2.toPileProfile : {k N K : ℕ} → TimeProfile.Cuts k N K → 0 < N → 2 ≤ k → RiffleShuffle.PileProfile N k K
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.triangle

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Empirical.lean:39`.

```lean
RiffleLowerV2.triangle : ℝ → Set (ℝ × ℝ)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.tv

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:25`.

```lean
RiffleLowerV2.tv : {Ω : Type u_1} → [Fintype Ω] → PMF Ω → PMF Ω → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.typeH

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:107`.

```lean
RiffleLowerV2.typeH : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N → (P : TimeProfile.BorelPartition k) → Finset (Fin K) → RiffleLowerV2.RoundedTypeData P → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.typeJ

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:104`.

```lean
RiffleLowerV2.typeJ : {k : ℕ} → {P : TimeProfile.BorelPartition k} → ℕ → RiffleLowerV2.RoundedTypeData P → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.uniformPermutation

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:28`.

```lean
RiffleLowerV2.uniformPermutation : (N : ℕ) → PMF (RiffleLowerV2.Permutation N)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.upperRank

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:71`.

```lean
RiffleLowerV2.upperRank : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Prefix k K → RiffleLowerV2.Sample cuts → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.usedCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Statistics.lean:27`.

```lean
RiffleLowerV2.usedCount : {N k K b : ℕ} → RiffleLowerV2.RowPrescription N k K b → Fin K → Fin k → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.variance

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:22`.

```lean
RiffleLowerV2.variance : {Ω : Type u_1} → [Fintype Ω] → PMF Ω → (Ω → ℝ) → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.wordCellCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:83`.

```lean
RiffleLowerV2.wordCellCount : {k N K : ℕ} →
  TimeProfile.Cuts k N K →
    0 < N →
      (P : TimeProfile.BorelPartition k) → {I : Finset (Fin K)} → RiffleLowerV2.WordOn k I → Fin P.cellCount → Fin k → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.wordCount

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:79`.

```lean
RiffleLowerV2.wordCount : {k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → RiffleLowerV2.Word k K → RiffleLowerV2.Sample cuts → ℕ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.wordMass

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Model.lean:78`.

```lean
RiffleLowerV2.wordMass : {k N K : ℕ} → TimeProfile.Cuts k N K → RiffleLowerV2.Word k K → ℝ
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.wordOnList

DEFINED and type checked. Source: `RiffleLowerV2/Shared/Geometry.lean:15`.

```lean
RiffleLowerV2.wordOnList : {k K : ℕ} → {I : Finset (Fin K)} → RiffleLowerV2.WordOn k I → List (Fin k)
```

Axiom closure: `Classical.choice`, `Quot.sound`, `propext`.
