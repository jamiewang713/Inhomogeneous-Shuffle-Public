# LB10 exact checked exports v1

Every required entry below is an actual theorem. The exact frozen types were checked in the elaborated Lean environment. Target bodies are reproduced from the unchanged LB00 compiled registry for readability; definitions of targets are not used as proofs.

## RiffleLowerV2.EmpiricalLower.largestOnly

```lean
RiffleLowerV2.EmpiricalLower.largestOnly : RiffleLowerV2.Targets.LargestOnlyTarget
```

Frozen target body:

```lean
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

Transitive axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.coldOnly

```lean
RiffleLowerV2.EmpiricalLower.coldOnly : RiffleLowerV2.Targets.ColdOnlyTarget
```

Frozen target body:

```lean
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

Transitive axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.empiricalCombined

```lean
RiffleLowerV2.EmpiricalLower.empiricalCombined : RiffleLowerV2.Targets.EmpiricalCombinedTarget
```

Frozen target body:

```lean
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

Transitive axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.finiteLargestWordTV

```lean
RiffleLowerV2.EmpiricalLower.finiteLargestWordTV : RiffleLowerV2.Targets.FiniteLargestWordTV
```

Frozen target body:

```lean
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (m : ℕ),
  2 ≤ m →
    m ≤ N →
      ↑m ≤ RiffleLowerV2.maximalMean cuts hN / 2 →
        1 - Real.exp (-RiffleLowerV2.chernoffConstant * RiffleLowerV2.maximalMean cuts hN) -
            ↑(N - m + 1) / ↑m.factorial ≤
          RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N)
```

Transitive axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.manyEdges

```lean
RiffleLowerV2.EmpiricalLower.manyEdges : RiffleLowerV2.Targets.ManyEdgesTarget
```

Frozen target body:

```lean
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

Transitive axiom closure: propext, Classical.choice, Quot.sound.

# Additional public declarations

Full generated and private declarations, direct dependencies, and transitive closures are retained in `compiled-declarations-v1.json`.

## RiffleLowerV2.EmpiricalLower.coldMeanConstant

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:12`.

```lean
RiffleLowerV2.EmpiricalLower.coldMeanConstant : ℝ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.coldMeanConstant_pos

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:14`.

```lean
RiffleLowerV2.EmpiricalLower.coldMeanConstant_pos : 0 < RiffleLowerV2.EmpiricalLower.coldMeanConstant
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.coldMeanConstant_eq

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:18`.

```lean
RiffleLowerV2.EmpiricalLower.coldMeanConstant_eq : RiffleLowerV2.EmpiricalLower.coldMeanConstant = Real.exp (-5) / 4
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.cold_min_mean

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:25`.

```lean
RiffleLowerV2.EmpiricalLower.cold_min_mean : ∀ {N : ℕ},
  1 ≤ N →
    ∀ {z u κ₀ : ℝ},
      0 ≤ κ₀ → z ≤ 2 * κ₀ → Real.exp (-2) * ↑N ^ z ≤ u → Real.exp (-2) ^ 2 * ↑N ^ (2 * z - 4 * κ₀) ≤ min (u ^ 2) 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.geometry_selectedPiles

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:54`.

```lean
RiffleLowerV2.EmpiricalLower.geometry_selectedPiles : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {eta rho chi xi : ℝ} (P : TimeProfile.BorelPartition k)
  (W : RiffleLowerV2.ColdWitnessData) (G : RiffleLowerV2.ColdGeometryData K P W),
  RiffleLowerV2.GeometrySpec cuts hN eta rho chi xi P W G →
    RiffleLowerV2.selectedPiles cuts (RiffleLowerV2.coldFullFamily cuts hN P W G) (min xi (min chi (1 / ↑k)))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.cold_collision_mean_lower

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:63`.

```lean
RiffleLowerV2.EmpiricalLower.cold_collision_mean_lower : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {eta rho chi xi D : ℝ},
  0 < eta →
    ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData) (G : RiffleLowerV2.ColdGeometryData K P W),
      RiffleLowerV2.GeometrySpec cuts hN eta rho chi xi P W G →
        D * ↑N ^ (-1 / 100) ≤ 1 / 2 →
          (∀ y ∈ RiffleLowerV2.coldFullFamily cuts hN P W G,
              |RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) (RiffleLowerV2.collisionEvent y) -
                    RiffleLowerV2.poissonCollision (↑N * RiffleLowerV2.wordMass cuts y)| ≤
                D * ↑N ^ (-1 / 100) * RiffleLowerV2.poissonCollision (↑N * RiffleLowerV2.wordMass cuts y)) →
            RiffleLowerV2.EmpiricalLower.coldMeanConstant *
                ↑N ^ (RiffleLowerV2.geometryG cuts hN P W G - 4 * RiffleLowerV2.kappa0 eta) ≤
              RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
                (RiffleLowerV2.collisionCount (RiffleLowerV2.coldFullFamily cuts hN P W G))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.cold_exponent_slack

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:111`.

```lean
RiffleLowerV2.EmpiricalLower.cold_exponent_slack : ∀ {eta g h : ℝ},
  RiffleLowerV2.kappa eta / 2 ≤ g - h / 2 →
    h / 2 + RiffleLowerV2.kappa eta / 3 + 19 * RiffleLowerV2.kappa eta / 150 ≤ g - 4 * RiffleLowerV2.kappa0 eta
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.exists_cold_mean_threshold

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:118`.

```lean
RiffleLowerV2.EmpiricalLower.exists_cold_mean_threshold : ∀ (eta : ℝ),
  0 < eta →
    ∃ (N0 : ℕ),
      2 ≤ N0 ∧
        ∀ (N : ℕ),
          N0 ≤ N →
            2 / RiffleLowerV2.EmpiricalLower.coldMeanConstant ≤ ↑N ^ (19 * RiffleLowerV2.kappa eta / 150) ∧
              2 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 12)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.cold_mean_dominates

Source: `RiffleLowerV2/EmpiricalLower/CollisionMean.lean:130`.

```lean
RiffleLowerV2.EmpiricalLower.cold_mean_dominates : ∀ {N : ℕ},
  1 ≤ N →
    ∀ {eta M h g E : ℝ},
      0 < eta →
        0 ≤ M →
          M ≤ 2 * ↑N ^ h →
            RiffleLowerV2.kappa eta / 2 ≤ g - h / 2 →
              2 / RiffleLowerV2.EmpiricalLower.coldMeanConstant ≤ ↑N ^ (19 * RiffleLowerV2.kappa eta / 150) →
                RiffleLowerV2.EmpiricalLower.coldMeanConstant * ↑N ^ (g - 4 * RiffleLowerV2.kappa0 eta) ≤ E →
                  √M * ↑N ^ (RiffleLowerV2.kappa eta / 3) ≤ E
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.largestRunLength

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:11`.

```lean
RiffleLowerV2.EmpiricalLower.largestRunLength : ℕ → ℝ → ℕ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.largestRunError

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:14`.

```lean
RiffleLowerV2.EmpiricalLower.largestRunError : ℕ → ℝ → ℝ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.two_pow_le_two_factorial

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:18`.

```lean
RiffleLowerV2.EmpiricalLower.two_pow_le_two_factorial : ∀ (m : ℕ), 2 ^ m ≤ 2 * ↑m.factorial
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.half_le_nat_floor

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:30`.

```lean
RiffleLowerV2.EmpiricalLower.half_le_nat_floor : ∀ {x : ℝ}, 2 ≤ x → x / 2 ≤ ↑⌊x⌋₊
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.floor_factorial_ratio_le

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:37`.

```lean
RiffleLowerV2.EmpiricalLower.floor_factorial_ratio_le : ∀ {N : ℕ} {x : ℝ}, 2 ≤ x → ↑N / ↑⌊x⌋₊.factorial ≤ 2 * ↑N * Real.exp (-(Real.log 2 / 2) * x)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.power_mul_stretchedExp_tendsto

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:58`.

```lean
RiffleLowerV2.EmpiricalLower.power_mul_stretchedExp_tendsto : ∀ (a r c : ℝ), 0 < r → 0 < c → Filter.Tendsto (fun (N : ℕ) => ↑N ^ a * Real.exp (-c * ↑N ^ r)) Filter.atTop (nhds 0)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.largestRunError_tendsto

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:71`.

```lean
RiffleLowerV2.EmpiricalLower.largestRunError_tendsto : ∀ (b : ℝ),
  0 < b → Filter.Tendsto (fun (N : ℕ) => RiffleLowerV2.EmpiricalLower.largestRunError N b) Filter.atTop (nhds 0)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.largestChernoffError_tendsto

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:93`.

```lean
RiffleLowerV2.EmpiricalLower.largestChernoffError_tendsto : ∀ (b : ℝ),
  0 < b → Filter.Tendsto (fun (N : ℕ) => Real.exp (-RiffleLowerV2.chernoffConstant * ↑N ^ b)) Filter.atTop (nhds 0)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.largestRunLength_eventually_admissible

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:99`.

```lean
RiffleLowerV2.EmpiricalLower.largestRunLength_eventually_admissible : ∀ (b : ℝ),
  0 < b →
    b ≤ 1 →
      ∀ᶠ (N : ℕ) in Filter.atTop,
        2 ≤ RiffleLowerV2.EmpiricalLower.largestRunLength N b ∧
          RiffleLowerV2.EmpiricalLower.largestRunLength N b ≤ N ∧
            ↑(RiffleLowerV2.EmpiricalLower.largestRunLength N b) ≤ ↑N ^ b / 2
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.maximalMean_le_population

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:121`.

```lean
RiffleLowerV2.EmpiricalLower.maximalMean_le_population : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N), RiffleLowerV2.maximalMean cuts hN ≤ ↑N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.largestMean_uniform_scales

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic/Numerical.lean:131`.

```lean
RiffleLowerV2.EmpiricalLower.largestMean_uniform_scales : ∀ (b epsilon : ℝ),
  0 < b →
    0 < epsilon →
      ∃ (N0 : ℕ),
        2 ≤ N0 ∧
          ∀ N ≥ N0,
            ∀ (mu : ℝ),
              ↑N ^ b ≤ mu →
                mu ≤ ↑N →
                  2 ≤ RiffleLowerV2.EmpiricalLower.largestRunLength N b ∧
                    RiffleLowerV2.EmpiricalLower.largestRunLength N b ≤ N ∧
                      ↑(RiffleLowerV2.EmpiricalLower.largestRunLength N b) ≤ mu / 2 ∧
                        Real.exp (-RiffleLowerV2.chernoffConstant * mu) +
                            RiffleLowerV2.EmpiricalLower.largestRunError N b ≤
                          epsilon
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.largestMean_uniform

Source: `RiffleLowerV2/EmpiricalLower/LargestAsymptotic.lean:10`.

```lean
RiffleLowerV2.EmpiricalLower.largestMean_uniform : ∀ (b epsilon : ℝ),
  0 < b →
    0 < epsilon →
      ∃ (N0 : ℕ),
        2 ≤ N0 ∧
          ∀ N ≥ N0,
            ∀ (k K : ℕ) (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
              ↑N ^ b ≤ RiffleLowerV2.maximalMean cuts hN →
                1 - epsilon ≤
                  RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.probability_increasingRun_le

Source: `RiffleLowerV2/EmpiricalLower/LargestFinite.lean:143`.

```lean
RiffleLowerV2.EmpiricalLower.probability_increasingRun_le : ∀ {N m : ℕ},
  m ≤ N →
    (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        RiffleLowerV2.HasIncreasingRun π m) ≤
      ↑(N - m + 1) / ↑m.factorial
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.fullWord_forces_increasingRun

Source: `RiffleLowerV2/EmpiricalLower/LargestFinite.lean:173`.

```lean
RiffleLowerV2.EmpiricalLower.fullWord_forces_increasingRun : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (w : RiffleLowerV2.Word k K) (m : ℕ),
  1 ≤ m → m ≤ RiffleLowerV2.wordCount w ω → RiffleLowerV2.HasIncreasingRun (RiffleLowerV2.stableSort ω) m
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.probability_intersection_lower

Source: `RiffleLowerV2/EmpiricalLower/ManyEdges.lean:11`.

```lean
RiffleLowerV2.EmpiricalLower.probability_intersection_lower : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A B : Ω → Prop),
  RiffleLowerV2.probability P A + RiffleLowerV2.probability P B - 1 ≤
    RiffleLowerV2.probability P fun (ω : Ω) => A ω ∧ B ω
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.collisionCount_eq_card

Source: `RiffleLowerV2/EmpiricalLower/ManyEdges.lean:25`.

```lean
RiffleLowerV2.EmpiricalLower.collisionCount_eq_card : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (Y : Finset (RiffleLowerV2.Word k K)) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.collisionCount Y ω = ↑{y ∈ Y | 2 ≤ RiffleLowerV2.wordCount y ω}.card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.cold_mean_power_lower

Source: `RiffleLowerV2/EmpiricalLower/ManyEdges.lean:34`.

```lean
RiffleLowerV2.EmpiricalLower.cold_mean_power_lower : ∀ {N : ℕ},
  0 < N →
    ∀ {eta M E : ℝ},
      ↑N ^ (RiffleLowerV2.kappa eta / 3) ≤ M →
        √M * ↑N ^ (RiffleLowerV2.kappa eta / 3) ≤ E → ↑N ^ (RiffleLowerV2.kappa eta / 2) ≤ E
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.cold_half_mean_threshold

Source: `RiffleLowerV2/EmpiricalLower/ManyEdges.lean:51`.

```lean
RiffleLowerV2.EmpiricalLower.cold_half_mean_threshold : ∀ {N : ℕ},
  0 < N →
    ∀ {eta M E : ℝ},
      2 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 12) →
        √M * ↑N ^ (RiffleLowerV2.kappa eta / 3) ≤ E → √M * ↑N ^ (RiffleLowerV2.kappa eta / 4) ≤ E / 2
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.cold_edges_threshold

Source: `RiffleLowerV2/EmpiricalLower/ManyEdges.lean:67`.

```lean
RiffleLowerV2.EmpiricalLower.cold_edges_threshold : ∀ {N : ℕ},
  1 ≤ N →
    ∀ {eta M : ℝ},
      0 < eta → 0 < M → M ≤ ↑N → M ^ (1 / 2 + RiffleLowerV2.kappa eta / 5) ≤ √M * ↑N ^ (RiffleLowerV2.kappa eta / 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.actualGraphLaw

Source: `RiffleLowerV2/EmpiricalLower/Scan.lean:10`.

```lean
RiffleLowerV2.EmpiricalLower.actualGraphLaw : {k N K : ℕ} → TimeProfile.Cuts k N K → PMF (RiffleLowerV2.PathEdges N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.physical_eq_actualGraphMixture

Source: `RiffleLowerV2/EmpiricalLower/Scan.lean:14`.

```lean
RiffleLowerV2.EmpiricalLower.physical_eq_actualGraphMixture : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  RiffleLowerV2.physicalInverseLaw cuts =
    RiffleLowerV2.Ascent.pathGraphMixture (RiffleLowerV2.EmpiricalLower.actualGraphLaw cuts)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.probability_actualGraphLaw

Source: `RiffleLowerV2/EmpiricalLower/Scan.lean:20`.

```lean
RiffleLowerV2.EmpiricalLower.probability_actualGraphLaw : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (A : RiffleLowerV2.PathEdges N → Prop),
  RiffleLowerV2.probability (RiffleLowerV2.EmpiricalLower.actualGraphLaw cuts) A =
    RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      A (RiffleLowerV2.shuffleEdges ω)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.physical_scan_success

Source: `RiffleLowerV2/EmpiricalLower/Scan.lean:29`.

```lean
RiffleLowerV2.EmpiricalLower.physical_scan_success : ∀ (a δ D ε : ℝ),
  0 < a →
    0 < δ →
      0 ≤ D →
        0 < ε →
          ∃ (N0 : ℕ),
            ∀ N ≥ N0,
              ∀ (k K : ℕ) (cuts : TimeProfile.Cuts k N K) (H0 : Finset ℤ),
                ↑N ^ a ≤ ↑H0.card →
                  (∀ (q : Fin (N + 1)),
                      ↑(RiffleLowerV2.boundary (RiffleLowerV2.clipTranslate N H0 ↑↑q)).card ≤ D * √↑H0.card) →
                    (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                          fun (ω : TimeProfile.ShuffleSample cuts) =>
                          RiffleLowerV2.Ascent.graphScanSuccess H0 δ (RiffleLowerV2.shuffleEdges ω)) -
                        ε ≤
                      RiffleLowerV2.probability (RiffleLowerV2.physicalInverseLaw cuts)
                        (RiffleLowerV2.scan H0 (↑H0.card ^ (1 / 2 + δ / 2)))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.physical_lalley_test

Source: `RiffleLowerV2/EmpiricalLower/Scan.lean:53`.

```lean
RiffleLowerV2.EmpiricalLower.physical_lalley_test : ∀ (a δ D ε : ℝ),
  0 < a →
    0 < δ →
      0 ≤ D →
        0 < ε →
          ∃ (N0 : ℕ),
            1 ≤ N0 ∧
              ∀ N ≥ N0,
                ∀ (k K : ℕ) (cuts : TimeProfile.Cuts k N K) (H0 : Finset ℤ),
                  ↑N ^ a ≤ ↑H0.card →
                    (∀ (q : Fin (N + 1)),
                        ↑(RiffleLowerV2.boundary (RiffleLowerV2.clipTranslate N H0 ↑↑q)).card ≤ D * √↑H0.card) →
                      (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                            fun (ω : TimeProfile.ShuffleSample cuts) =>
                            RiffleLowerV2.Ascent.graphScanSuccess H0 δ (RiffleLowerV2.shuffleEdges ω)) -
                          ε ≤
                        RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.localized_edge_event_implies_scan

Source: `RiffleLowerV2/EmpiricalLower/Scan.lean:71`.

```lean
RiffleLowerV2.EmpiricalLower.localized_edge_event_implies_scan : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (H0 : Finset ℤ) (w : RiffleLowerV2.Prefix k K) (δ : ℝ)
  (ω : RiffleLowerV2.Sample cuts),
  ↑H0.card ^ (1 / 2 + δ) ≤
      ↑(Finset.card
          (RiffleLowerV2.shuffleEdges ω ∩
            RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑(RiffleLowerV2.lowerRank w ω)))) →
    RiffleLowerV2.Ascent.graphScanSuccess H0 δ (RiffleLowerV2.shuffleEdges ω)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.EmpiricalLower.coldGeometry_scan_test

Source: `RiffleLowerV2/EmpiricalLower/Scan.lean:82`.

```lean
RiffleLowerV2.EmpiricalLower.coldGeometry_scan_test : ∀ (k : ℕ) (eta ε : ℝ),
  0 < eta →
    0 < ε →
      ∃ (N0 : ℕ),
        1 ≤ N0 ∧
          ∀ N ≥ N0,
            ∀ (K : ℕ) (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (rho chi xi : ℝ) (P : TimeProfile.BorelPartition k)
              (W : RiffleLowerV2.ColdWitnessData) (G : RiffleLowerV2.ColdGeometryData K P W),
              RiffleLowerV2.GeometrySpec cuts hN eta rho chi xi P W G →
                (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
                      ↑(RiffleLowerV2.coldRelativeSet cuts hN P W G).card ^ (1 / 2 + RiffleLowerV2.kappa eta / 5) ≤
                        ↑(Finset.card
                            (RiffleLowerV2.shuffleEdges ω ∩
                              RiffleLowerV2.internalEdges
                                (RiffleLowerV2.clipTranslate N (RiffleLowerV2.coldRelativeSet cuts hN P W G)
                                  ↑(RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt W.ms G.ambient) ω))))) -
                    ε ≤
                  RiffleLowerV2.tv (RiffleLowerV2.physicalInverseLaw cuts) (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: propext, Classical.choice, Quot.sound.
