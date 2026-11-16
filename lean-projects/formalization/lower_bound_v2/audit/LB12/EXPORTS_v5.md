# LB12 exact checked exports

Every row below is a theorem of its immutable target; target bodies are printed from the same compiled environment.

## RiffleLowerV2.Model.columnIndependence

Owner: LB01. Defining module: `RiffleLowerV2.Model.FiniteLaws`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.columnIndependence : RiffleLowerV2.Targets.ColumnIndependence
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (f : (j : Fin K) → TimeProfile.ColumnAssignments cuts j → ℝ),
  (RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      ∏ j : Fin K, f j (ω j)) =
    ∏ j : Fin K, RiffleLowerV2.expect (TimeProfile.columnPMF cuts j) (f j)
```

## RiffleLowerV2.Model.graphRepresentation

Owner: LB01. Defining module: `RiffleLowerV2.Model.GraphLaw`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.graphRepresentation : RiffleLowerV2.Targets.GraphRepresentation
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), RiffleLowerV2.matrixLaw cuts = RiffleLowerV2.graphMixtureLaw cuts
```

## RiffleLowerV2.Model.graphEventIdentity

Owner: LB01. Defining module: `RiffleLowerV2.Model.GraphLaw`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.graphEventIdentity : RiffleLowerV2.Targets.GraphEventIdentity
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (A : RiffleLowerV2.Permutation N → Prop),
  RiffleLowerV2.probability (RiffleLowerV2.matrixLaw cuts) A =
    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        A (RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) π)
```

## RiffleLowerV2.Model.physicalMatrixBridge

Owner: LB01. Defining module: `RiffleLowerV2.Model.Physical`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.physicalMatrixBridge : RiffleLowerV2.Targets.PhysicalMatrixBridge
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), RiffleLowerV2.physicalInverseLaw cuts = RiffleLowerV2.matrixLaw cuts
```

## RiffleLowerV2.Model.inversionTV

Owner: LB01. Defining module: `RiffleLowerV2.Model.FiniteLaws`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.inversionTV : RiffleLowerV2.Targets.InversionTV
-- Frozen target body:
∀ (N : ℕ) (P : PMF (RiffleLowerV2.Permutation N)),
  RiffleLowerV2.tv (PMF.map Equiv.symm P) (RiffleLowerV2.uniformPermutation N) =
    RiffleLowerV2.tv P (RiffleLowerV2.uniformPermutation N)
```

## RiffleLowerV2.Model.rowRelabeling

Owner: LB01. Defining module: `RiffleLowerV2.Model.FiniteLaws`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.rowRelabeling : RiffleLowerV2.Targets.RowRelabeling
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (σ : RiffleLowerV2.Permutation N),
  PMF.map (fun (ω : TimeProfile.ShuffleSample cuts) (i : Fin N) => TimeProfile.sampleRow ω (σ i))
      (TimeProfile.fixedCountPMF cuts) =
    PMF.map TimeProfile.sampleRow (TimeProfile.fixedCountPMF cuts)
```

## RiffleLowerV2.Model.stableTie

Owner: LB01. Defining module: `RiffleLowerV2.Model.Sorting`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.stableTie : RiffleLowerV2.Targets.StableTie
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (ω : RiffleLowerV2.Sample cuts) (i j : Fin N),
  i < j →
    RiffleLowerV2.sortedWord ω i = RiffleLowerV2.sortedWord ω j →
      (RiffleLowerV2.stableSort ω) i < (RiffleLowerV2.stableSort ω) j
```

## RiffleLowerV2.Model.prefixRanks

Owner: LB01. Defining module: `RiffleLowerV2.Model.Sorting`. Source labels: `lem:ub-graph-representation`.

```lean
RiffleLowerV2.Model.prefixRanks : RiffleLowerV2.Targets.PrefixRanks
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (ω : RiffleLowerV2.Sample cuts) (w : RiffleLowerV2.Prefix k K),
  (∀ (i : Fin N),
      List.take (↑w.fst) (List.Vector.toList (RiffleLowerV2.sortedWord ω i)) = List.Vector.toList w.snd ↔
        RiffleLowerV2.lowerRank w ω ≤ ↑i ∧ ↑i < RiffleLowerV2.upperRank w ω) ∧
    RiffleLowerV2.upperRank w ω - RiffleLowerV2.lowerRank w ω = RiffleLowerV2.prefixCount w ω
```

## RiffleLowerV2.Thinning.successiveThinning

Owner: LB02. Defining module: `RiffleLowerV2.Thinning.Process`. Source labels: `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix`.

```lean
RiffleLowerV2.Thinning.successiveThinning : RiffleLowerV2.Targets.SuccessiveThinning
-- Frozen target body:
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

## RiffleLowerV2.Thinning.prefixTails

Owner: LB02. Defining module: `RiffleLowerV2.Thinning.Prefixes`. Source labels: `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix`.

```lean
RiffleLowerV2.Thinning.prefixTails : RiffleLowerV2.Targets.PrefixTails
-- Frozen target body:
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

## RiffleLowerV2.Thinning.allPrefixConcentration

Owner: LB02. Defining module: `RiffleLowerV2.Thinning.Prefixes`. Source labels: `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix`.

```lean
RiffleLowerV2.Thinning.allPrefixConcentration : RiffleLowerV2.Targets.AllPrefixConcentration
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ N →
    ∀ (ε : ℝ),
      0 < ε →
        (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
            ¬RiffleLowerV2.allPrefixEvent ε ω) ≤
          RiffleLowerV2.prefixFailure N k K ε
```

## RiffleLowerV2.Thinning.prefixFailureUniform

Owner: LB02. Defining module: `RiffleLowerV2.Thinning.UniformError`. Source labels: `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix`.

```lean
RiffleLowerV2.Thinning.prefixFailureUniform : RiffleLowerV2.Targets.PrefixFailureUniform
-- Frozen target body:
∀ (k : ℕ),
  2 ≤ k →
    ∀ (T ε δ : ℝ),
      0 < T →
        0 < ε →
          0 < δ →
            ∃ (N0 : ℕ), ∀ N ≥ N0, ∀ (K : ℕ), ↑K ≤ T * TimeProfile.logScale N → RiffleLowerV2.prefixFailure N k K ε ≤ δ
```

## RiffleLowerV2.Thinning.residualLaw

Owner: LB02. Defining module: `RiffleLowerV2.Thinning.Residual`. Source labels: `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix`.

```lean
RiffleLowerV2.Thinning.residualLaw : RiffleLowerV2.Targets.ResidualLaw
-- Frozen target body:
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

## RiffleLowerV2.Thinning.hypergeometricTransform

Owner: LB02. Defining module: `RiffleLowerV2.Thinning.Sampling`. Source labels: `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix`.

```lean
RiffleLowerV2.Thinning.hypergeometricTransform : RiffleLowerV2.Targets.HypergeometricTransform
-- Frozen target body:
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

## RiffleLowerV2.Thinning.maximalMeanIdentity

Owner: LB02. Defining module: `RiffleLowerV2.Thinning.MaximalWord`. Source labels: `lem:successive-thinning-tail`, `cor:iterated-hypergeom`, `prop:largest-prefix`.

```lean
RiffleLowerV2.Thinning.maximalMeanIdentity : RiffleLowerV2.Targets.MaximalMeanIdentity
-- Frozen target body:
∀ (k N K : ℕ),
  2 ≤ k →
    ∀ (hN : 2 ≤ N) (cuts : TimeProfile.Cuts k N K),
      ∃ (w : RiffleLowerV2.Word k K),
        RiffleLowerV2.IsCanonicalMaxWord cuts w ∧
          ↑N * RiffleLowerV2.wordMass cuts w = RiffleLowerV2.maximalMean cuts ⋯ ∧
            RiffleLowerV2.maximalMean cuts ⋯ = ↑N ^ RiffleLowerV2.beta cuts ⋯ (RiffleLowerV2.horizon N K)
```

## RiffleLowerV2.Factorial.exactJointFactorial

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.Exact`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.exactJointFactorial : RiffleLowerV2.Targets.ExactJointFactorial
-- Frozen target body:
∀ {k N K d : ℕ} (cuts : TimeProfile.Cuts k N K) (w : Fin d → RiffleLowerV2.Word k K) (r : Fin d → ℕ),
  Function.Injective w →
    ∑ i : Fin d, r i ≤ N →
      RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.factorialProduct w r) =
        RiffleLowerV2.exactFactorial cuts w r
```

## RiffleLowerV2.Factorial.relativeJointFactorial

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.RelativeTargets`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.relativeJointFactorial : RiffleLowerV2.Targets.RelativeJointFactorial
-- Frozen target body:
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

## RiffleLowerV2.Factorial.bonferroniSandwich

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.Bonferroni`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.bonferroniSandwich : RiffleLowerV2.Targets.BonferroniSandwich
-- Frozen target body:
∀ (m : ℕ),
  2 ≤ m →
    Even m →
      ∀ (n : ℕ),
        (0 ≤ RiffleLowerV2.bonferroni m n - if 2 ≤ n then 1 else 0) ∧
          (RiffleLowerV2.bonferroni m n - if 2 ≤ n then 1 else 0) ≤ RiffleLowerV2.bonferroniRemainder m n
```

## RiffleLowerV2.Factorial.bonferroniProduct

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.Bonferroni`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.bonferroniProduct : RiffleLowerV2.Targets.BonferroniProduct
-- Frozen target body:
∀ (m : ℕ),
  2 ≤ m →
    Even m →
      ∀ (x y : ℕ),
        (0 ≤ RiffleLowerV2.bonferroni m x * RiffleLowerV2.bonferroni m y - if 2 ≤ x ∧ 2 ≤ y then 1 else 0) ∧
          (RiffleLowerV2.bonferroni m x * RiffleLowerV2.bonferroni m y - if 2 ≤ x ∧ 2 ≤ y then 1 else 0) ≤
            RiffleLowerV2.bonferroniRemainder m x + RiffleLowerV2.bonferroniRemainder m y +
              RiffleLowerV2.bonferroniRemainder m x * RiffleLowerV2.bonferroniRemainder m y
```

## RiffleLowerV2.Factorial.centralComparison

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.Central`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.centralComparison : RiffleLowerV2.Targets.CentralComparison
-- Frozen target body:
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

## RiffleLowerV2.Factorial.centralComparisonOne

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.Central`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.centralComparisonOne : RiffleLowerV2.Targets.CentralComparisonOne
-- Frozen target body:
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

## RiffleLowerV2.Factorial.rareSandwich

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.Basic`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.rareSandwich : RiffleLowerV2.Targets.RareSandwich
-- Frozen target body:
∀ (Ω : Type) [inst : Fintype Ω] (P : PMF Ω) (X : Ω → ℕ),
  ((RiffleLowerV2.expect P fun (ω : Ω) => RiffleLowerV2.falling (X ω) 2) / 2 -
        (RiffleLowerV2.expect P fun (ω : Ω) => RiffleLowerV2.falling (X ω) 3) / 3 ≤
      RiffleLowerV2.probability P fun (ω : Ω) => 2 ≤ X ω) ∧
    (RiffleLowerV2.probability P fun (ω : Ω) => 2 ≤ X ω) ≤
      (RiffleLowerV2.expect P fun (ω : Ω) => RiffleLowerV2.falling (X ω) 2) / 2
```

## RiffleLowerV2.Factorial.residualJointFactorial

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.Residual`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.residualJointFactorial : RiffleLowerV2.Targets.ResidualJointFactorial
-- Frozen target body:
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

## RiffleLowerV2.Factorial.residualRelativeFactorial

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.RelativeTargets`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.residualRelativeFactorial : RiffleLowerV2.Targets.ResidualRelativeFactorial
-- Frozen target body:
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

## RiffleLowerV2.Factorial.residualMeanComparison

Owner: LB03. Defining module: `RiffleLowerV2.Factorial.ResidualEstimates`. Source labels: `lem:fixed-column-factorial`, `lem:central-window`.

```lean
RiffleLowerV2.Factorial.residualMeanComparison : RiffleLowerV2.Targets.ResidualMeanComparison
-- Frozen target body:
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

## RiffleLowerV2.Ascent.componentConcentration

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.Concentration`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.componentConcentration : RiffleLowerV2.Targets.ComponentConcentration
-- Frozen target body:
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

## RiffleLowerV2.Ascent.componentExpectation

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.Expectation`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.componentExpectation : RiffleLowerV2.Targets.ComponentExpectation
-- Frozen target body:
∀ (N : ℕ) (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
      ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π))) ≥
    ↑(Finset.card (RiffleLowerV2.internalEdges H)) / 2 + ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges H)) / 6 -
      ↑(RiffleLowerV2.boundary H).card
```

## RiffleLowerV2.Ascent.uniformScan

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.Concentration`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.uniformScan : RiffleLowerV2.Targets.UniformScan
-- Frozen target body:
∀ (N : ℕ) (H0 : Finset ℤ) (s : ℝ),
  0 < H0.card →
    0 < s →
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) (RiffleLowerV2.scan H0 s) ≤
        (↑N + 1) * Real.exp (-s ^ 2 / ↑H0.card)
```

## RiffleLowerV2.Ascent.componentComparison

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.Test`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.componentComparison : RiffleLowerV2.Targets.ComponentComparison
-- Frozen target body:
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

## RiffleLowerV2.Ascent.uniformGraphScan

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.Test`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.uniformGraphScan : RiffleLowerV2.Targets.UniformGraphScan
-- Frozen target body:
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

## RiffleLowerV2.Ascent.relativeOrderIndependence

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.RelativeOrder.Law`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.relativeOrderIndependence : RiffleLowerV2.Targets.RelativeOrderIndependence
-- Frozen target body:
∀ (N d : ℕ) (A : Fin d → Finset (Fin N)),
  (∀ (i j : Fin d), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (τ : Fin d → RiffleLowerV2.Permutation N),
      (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
          ∀ (i : Fin d), ∀ x ∈ A i, ∀ y ∈ A i, π x < π y ↔ (τ i) x < (τ i) y) =
        ∏ i : Fin d, 1 / ↑(A i).card.factorial
```

## RiffleLowerV2.Ascent.boundaryAscentProbability

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.RelativeOrder.Boundary`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.boundaryAscentProbability : RiffleLowerV2.Targets.BoundaryAscentProbability
-- Frozen target body:
∀ (N : ℕ) (A B : Finset (Fin N)),
  Disjoint A B →
    (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        ∀ x ∈ A, ∀ y ∈ B, π x < π y) =
      1 / ↑((A.card + B.card).choose A.card)
```

## RiffleLowerV2.Ascent.bernoulliMGF

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.MGF`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.bernoulliMGF : RiffleLowerV2.Targets.BernoulliMGF
-- Frozen target body:
∀ (Ω : Type) [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop) (t : ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (t * ((if A ω then 1 else 0) - RiffleLowerV2.probability P A))) ≤
    Real.exp (t ^ 2 / 8)
```

## RiffleLowerV2.Ascent.leastSuccessfulTranslate

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.Selection`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.leastSuccessfulTranslate : RiffleLowerV2.Targets.LeastSuccessfulTranslate
-- Frozen target body:
∀ (N : ℕ) (H0 : Finset ℤ) (G : RiffleLowerV2.PathEdges N) (r : ℝ),
  (∃ (q : Fin (N + 1)), r ≤ ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q)))) →
    ∃ (q : Fin (N + 1)),
      r ≤ ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q))) ∧
        ∀ q' < q, ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q'))) < r
```

## RiffleLowerV2.Ascent.componentConcentrationTwoSided

Owner: LB04. Defining module: `RiffleLowerV2.Ascent.Concentration`. Source labels: `lem:relative-order-independence`, `lem:permutation-bd`, `lem:component-ascent-expectation`, `lem:uniform-ascent`, `lem:lalley-comparison`, `lem:lalley`.

```lean
RiffleLowerV2.Ascent.componentConcentrationTwoSided : RiffleLowerV2.Targets.ComponentConcentrationTwoSided
-- Frozen target body:
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

## RiffleLowerV2.Witness.coldWitness

Owner: LB05. Defining module: `RiffleLowerV2.Witness.Main`. Source labels: `lem:cold-witness`.

```lean
RiffleLowerV2.Witness.coldWitness : RiffleLowerV2.Targets.ColdWitnessTarget
-- Frozen target body:
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

## RiffleLowerV2.Witness.oneColumnTilt

Owner: LB05. Defining module: `RiffleLowerV2.Witness.OneColumn`. Source labels: `lem:cold-witness`.

```lean
RiffleLowerV2.Witness.oneColumnTilt : RiffleLowerV2.Targets.OneColumnTiltTarget
-- Frozen target body:
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

## RiffleLowerV2.Witness.empiricalTilt

Owner: LB05. Defining module: `RiffleLowerV2.Witness.EmpiricalTilt`. Source labels: `lem:cold-witness`.

```lean
RiffleLowerV2.Witness.empiricalTilt : RiffleLowerV2.Targets.EmpiricalTiltTarget
-- Frozen target body:
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

## RiffleLowerV2.Witness.lB05

Owner: LB05. Defining module: `RiffleLowerV2.Witness.Main`. Source labels: `lem:cold-witness`.

```lean
RiffleLowerV2.Witness.lB05 : RiffleLowerV2.Targets.LB05Target
-- Frozen target body:
RiffleLowerV2.Targets.OneColumnTiltTarget ∧
  RiffleLowerV2.Targets.EmpiricalTiltTarget ∧ RiffleLowerV2.Targets.ColdWitnessTarget
```

## RiffleLowerV2.Types.roundedType

Owner: LB06. Defining module: `RiffleLowerV2.Types.Main`. Source labels: `lem:type-estimates`.

```lean
RiffleLowerV2.Types.roundedType : RiffleLowerV2.Targets.RoundedTypeTarget
-- Frozen target body:
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

## RiffleLowerV2.ProfileTransfer.marginTransfer

Owner: LB07. Defining module: `RiffleLowerV2.ProfileTransfer.Margin`. Source labels: `lem:lower-profile-transfer`.

```lean
RiffleLowerV2.ProfileTransfer.marginTransfer : RiffleLowerV2.Targets.MarginTransferTarget
-- Frozen target body:
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

## RiffleLowerV2.ProfileTransfer.profileTransfer

Owner: LB07. Defining module: `RiffleLowerV2.ProfileTransfer.Main`. Source labels: `lem:lower-profile-transfer`.

```lean
RiffleLowerV2.ProfileTransfer.profileTransfer : RiffleLowerV2.Targets.ProfileTransferTarget
-- Frozen target body:
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

## RiffleLowerV2.ProfileTransfer.genericQuadrature

Owner: LB07. Defining module: `RiffleLowerV2.ProfileTransfer.Quadrature`. Source labels: `lem:lower-profile-transfer`.

```lean
RiffleLowerV2.ProfileTransfer.genericQuadrature : RiffleLowerV2.Targets.GenericQuadrature
-- Frozen target body:
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

## RiffleLowerV2.ProfileTransfer.jointPsiContinuity

Owner: LB07. Defining module: `RiffleLowerV2.ProfileTransfer.Spatial`. Source labels: `lem:lower-profile-transfer`.

```lean
RiffleLowerV2.ProfileTransfer.jointPsiContinuity : RiffleLowerV2.Targets.JointPsiContinuity
-- Frozen target body:
∀ (k : ℕ),
  2 ≤ k → ContinuousOn (fun (z : TimeProfile.Simplex k × ℝ) => TimeProfile.psi z.1 z.2) (Set.univ ×ˢ Set.Icc 2 4)
```

## RiffleLowerV2.Occupancy.uniformOccupancy

Owner: LB08. Defining module: `RiffleLowerV2.Occupancy.Main`. Source labels: `lem:two-category-poisson`.

```lean
RiffleLowerV2.Occupancy.uniformOccupancy : RiffleLowerV2.Targets.UniformOccupancy
-- Frozen target body:
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

## RiffleLowerV2.Occupancy.conditionalCollisionStability

Owner: LB08. Defining module: `RiffleLowerV2.Occupancy.Conditional`. Source labels: `lem:two-category-poisson`.

```lean
RiffleLowerV2.Occupancy.conditionalCollisionStability : RiffleLowerV2.Targets.ConditionalCollisionStability
-- Frozen target body:
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

## RiffleLowerV2.Occupancy.collisionChebyshev

Owner: LB08. Defining module: `RiffleLowerV2.Occupancy.Main`. Source labels: `lem:two-category-poisson`.

```lean
RiffleLowerV2.Occupancy.collisionChebyshev : RiffleLowerV2.Targets.CollisionChebyshev
-- Frozen target body:
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

## RiffleLowerV2.Localization.localization

Owner: LB09. Defining module: `RiffleLowerV2.Localization.Events`. Source labels: `lem:cold-geometry`, `lem:finite-relative-endpoints`, `lem:localization`.

```lean
RiffleLowerV2.Localization.localization : RiffleLowerV2.Targets.LocalizationTarget
-- Frozen target body:
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

## RiffleLowerV2.Localization.coldGeometryFromEmpirical

Owner: LB09. Defining module: `RiffleLowerV2.Localization.Main`. Source labels: `lem:cold-geometry`, `lem:finite-relative-endpoints`, `lem:localization`.

```lean
RiffleLowerV2.Localization.coldGeometryFromEmpirical : RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget
-- Frozen target body:
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

## RiffleLowerV2.Localization.relativeEndpoint

Owner: LB09. Defining module: `RiffleLowerV2.Localization.Endpoints`. Source labels: `lem:cold-geometry`, `lem:finite-relative-endpoints`, `lem:localization`.

```lean
RiffleLowerV2.Localization.relativeEndpoint : RiffleLowerV2.Targets.RelativeEndpointTarget
-- Frozen target body:
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

## RiffleLowerV2.Localization.deterministicColdGeometry

Owner: LB09. Defining module: `RiffleLowerV2.Localization.Geometry`. Source labels: `lem:cold-geometry`, `lem:finite-relative-endpoints`, `lem:localization`.

```lean
RiffleLowerV2.Localization.deterministicColdGeometry : RiffleLowerV2.Targets.DeterministicColdGeometryTarget
-- Frozen target body:
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

## RiffleLowerV2.Localization.lB09

Owner: LB09. Defining module: `RiffleLowerV2.Localization.Main`. Source labels: `lem:cold-geometry`, `lem:finite-relative-endpoints`, `lem:localization`.

```lean
RiffleLowerV2.Localization.lB09 : RiffleLowerV2.Targets.LB09Target
-- Frozen target body:
RiffleLowerV2.Targets.RelativeEndpointTarget ∧
  RiffleLowerV2.Targets.DeterministicColdGeometryTarget ∧
    RiffleLowerV2.Targets.LocalizationTarget ∧ RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget
```

## RiffleLowerV2.EmpiricalLower.largestOnly

Owner: LB10. Defining module: `RiffleLowerV2.EmpiricalLower.LargestAsymptotic`. Source labels: `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`.

```lean
RiffleLowerV2.EmpiricalLower.largestOnly : RiffleLowerV2.Targets.LargestOnlyTarget
-- Frozen target body:
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

## RiffleLowerV2.EmpiricalLower.coldOnly

Owner: LB10. Defining module: `RiffleLowerV2.EmpiricalLower.Cold`. Source labels: `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`.

```lean
RiffleLowerV2.EmpiricalLower.coldOnly : RiffleLowerV2.Targets.ColdOnlyTarget
-- Frozen target body:
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

## RiffleLowerV2.EmpiricalLower.empiricalCombined

Owner: LB10. Defining module: `RiffleLowerV2.EmpiricalLower.Main`. Source labels: `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`.

```lean
RiffleLowerV2.EmpiricalLower.empiricalCombined : RiffleLowerV2.Targets.EmpiricalCombinedTarget
-- Frozen target body:
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

## RiffleLowerV2.EmpiricalLower.finiteLargestWordTV

Owner: LB10. Defining module: `RiffleLowerV2.EmpiricalLower.LargestFinite`. Source labels: `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`.

```lean
RiffleLowerV2.EmpiricalLower.finiteLargestWordTV : RiffleLowerV2.Targets.FiniteLargestWordTV
-- Frozen target body:
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (m : ℕ),
  2 ≤ m →
    m ≤ N →
      ↑m ≤ RiffleLowerV2.maximalMean cuts hN / 2 →
        1 - Real.exp (-RiffleLowerV2.chernoffConstant * RiffleLowerV2.maximalMean cuts hN) -
            ↑(N - m + 1) / ↑m.factorial ≤
          RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N)
```

## RiffleLowerV2.EmpiricalLower.manyEdges

Owner: LB10. Defining module: `RiffleLowerV2.EmpiricalLower.ManyEdges`. Source labels: `prop:largest-prefix`, `lem:many-edges`, `lem:lalley`, `prop:cold-lower`.

```lean
RiffleLowerV2.EmpiricalLower.manyEdges : RiffleLowerV2.Targets.ManyEdgesTarget
-- Frozen target body:
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

## RiffleLowerV2.MacroscopicLower.macroscopicIntegrable

Owner: LB11. Defining module: `RiffleLowerV2.MacroscopicLower.Main`. Source labels: `thm:buffered-reduced-lower-bound`, `lem:lower-profile-transfer`, `prop:cold-lower`.

```lean
RiffleLowerV2.MacroscopicLower.macroscopicIntegrable : RiffleLowerV2.Targets.MacroscopicIntegrableTarget
-- Frozen target body:
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
