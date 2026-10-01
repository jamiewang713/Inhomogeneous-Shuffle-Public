# LB09 exact checked exports v1

All five required exports are proved theorems of their unchanged frozen target types. The types below are printed from the compiled Lean environment. Target definitions are not counted as proofs.

## RiffleLowerV2.Localization.ambient_exponent_lower

Source: `RiffleLowerV2/Localization/Geometry/Algebra.lean:58`. Kind: theorem.

```lean
RiffleLowerV2.Localization.ambient_exponent_lower : ∀ {b jp kap : ℝ}, 0 ≤ jp → b / 2 + 2 * kap ≤ b - jp → 4 * kap ≤ b
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.boundary_clipTranslate_le

Source: `RiffleLowerV2/Localization/Intervals.lean:156`. Kind: theorem.

```lean
RiffleLowerV2.Localization.boundary_clipTranslate_le : ∀ (N : ℕ) (H : Finset ℤ) (q : ℤ),
  (RiffleLowerV2.boundary (RiffleLowerV2.clipTranslate N H q)).card ≤ (RiffleLowerV2.integerBoundary H).card + 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.bridge_grid_cost_bounds

Source: `RiffleLowerV2/Localization/Geometry/Empirical.lean:37`. Kind: theorem.

```lean
RiffleLowerV2.Localization.bridge_grid_cost_bounds : ∀ {k N K : ℕ},
  2 ≤ k →
    2 ≤ N →
      ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {mu bl : ℕ} {rho : ℝ},
        0 < rho →
          bl = ⌈2 * rho * TimeProfile.logScale N⌉₊ →
            mu + bl ≤ K →
              have u := RiffleLowerV2.gridTime N mu;
              have v := RiffleLowerV2.gridTime N (mu + bl);
              have d := (2 * rho + 1 / TimeProfile.logScale N) * Real.log ↑k;
              0 ≤ RiffleLowerV2.J cuts hN 2 u v ∧
                RiffleLowerV2.J cuts hN 2 u v ≤ d ∧
                  0 ≤ RiffleLowerV2.H cuts hN 2 u v ∧ RiffleLowerV2.H cuts hN 2 u v ≤ d
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.bridge_log_bound

Source: `RiffleLowerV2/Localization/Bridge.lean:50`. Kind: theorem.

```lean
RiffleLowerV2.Localization.bridge_log_bound : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ N →
    0 < N →
      2 ≤ k →
        ∀ {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
          (G : RiffleLowerV2.ColdGeometryData K P W) {rho chi : ℝ},
          0 < rho →
            0 < chi →
              W.bridgeLength = ⌈2 * rho * TimeProfile.logScale N⌉₊ →
                chi ^ 2 * ↑k ^ (-↑W.bridgeLength) ≤ RiffleLowerV2.massOn cuts G.central →
                  0 ≤ RiffleLowerV2.geometryEllB cuts G ∧
                    RiffleLowerV2.geometryEllB cuts G ≤
                      2 * rho * Real.log ↑k + (Real.log ↑k + 2 * Real.log (1 / chi)) / TimeProfile.logScale N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.canonical_digit_eq_pileMax

Source: `RiffleLowerV2/Localization/Words.lean:203`. Kind: theorem.

```lean
RiffleLowerV2.Localization.canonical_digit_eq_pileMax : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (w : RiffleLowerV2.Word k K),
  RiffleLowerV2.IsCanonicalMaxWord cuts w →
    ∀ (j : Fin K), ↑(cuts.count j (List.Vector.get w j)) / ↑N = TimeProfile.pileMax (cuts.profile hN j)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.canonical_digit_ge_inv

Source: `RiffleLowerV2/Localization/Words.lean:220`. Kind: theorem.

```lean
RiffleLowerV2.Localization.canonical_digit_ge_inv : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    0 < k →
      ∀ (w : RiffleLowerV2.Word k K),
        RiffleLowerV2.IsCanonicalMaxWord cuts w → ∀ (j : Fin K), 1 / ↑k ≤ ↑(cuts.count j (List.Vector.get w j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.canonical_prefixMean_eq_rpow_beta

Source: `RiffleLowerV2/Localization/Words.lean:226`. Kind: theorem.

```lean
RiffleLowerV2.Localization.canonical_prefixMean_eq_rpow_beta : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ N →
    ∀ (hN : 0 < N) (w : RiffleLowerV2.Word k K),
      RiffleLowerV2.IsCanonicalMaxWord cuts w →
        ∀ m ≤ K,
          RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt m w) =
            ↑N ^ RiffleLowerV2.beta cuts hN (RiffleLowerV2.gridTime N m)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldFamily_localized_of_endpoint_reserves

Source: `RiffleLowerV2/Localization/RankBarriers.lean:330`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldFamily_localized_of_endpoint_reserves : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {P : TimeProfile.BorelPartition k}
  {W : RiffleLowerV2.ColdWitnessData} (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      RiffleLowerV2.wordOnList G.reserveMinus < RiffleLowerV2.wordOnList G.central →
        RiffleLowerV2.wordOnList G.central < RiffleLowerV2.wordOnList G.reservePlus →
          ∀ (e : ℝ) (omega : RiffleLowerV2.Sample cuts),
            (∀ x ∈ RiffleLowerV2.coldPrefixFamily cuts hN P W G,
                |↑(RiffleLowerV2.relativeLowerCount G.ambient W.ms W.mu x omega) -
                        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) *
                          RiffleLowerV2.relativeMassBefore cuts x| ≤
                    e ∧
                  |↑(RiffleLowerV2.relativeUpperCount G.ambient W.ms W.mu x omega) -
                          RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) *
                            (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x)| ≤
                      e ∧
                    e + 2 ≤ ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reserveMinus) omega) ∧
                      e + 2 ≤ ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reservePlus) omega)) →
              ∀ y ∈ RiffleLowerV2.coldFullFamily cuts hN P W G,
                ∀ (i : Fin N),
                  RiffleLowerV2.sortedWord omega i = y →
                    i ∈
                      RiffleLowerV2.clipTranslate N (RiffleLowerV2.coldRelativeSet cuts hN P W G)
                        ↑(RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt W.ms G.ambient) omega)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldFullFamily_card

Source: `RiffleLowerV2/Localization/Words.lean:149`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldFullFamily_card : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k)
  (W : RiffleLowerV2.ColdWitnessData) (G : RiffleLowerV2.ColdGeometryData K P W),
  (RiffleLowerV2.coldFullFamily cuts hN P W G).card =
    (RiffleLowerV2.coldPrefixFamily cuts hN P W G).card * (RiffleLowerV2.coldTailFamily cuts hN P W G).card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldFullFamily_card_rpow

Source: `RiffleLowerV2/Localization/Geometry/Consequences.lean:29`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldFullFamily_card_rpow : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k)
  (W : RiffleLowerV2.ColdWitnessData) (G : RiffleLowerV2.ColdGeometryData K P W) {xi : ℝ},
  RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.prefixColumns K W) xi W.theta G.prefixType →
    RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.tailColumns K W) xi 2 G.tailType →
      ↑(RiffleLowerV2.coldFullFamily cuts hN P W G).card =
        ↑N ^
          (RiffleLowerV2.typeH cuts hN P (RiffleLowerV2.prefixColumns K W) G.prefixType +
            RiffleLowerV2.typeH cuts hN P (RiffleLowerV2.tailColumns K W) G.tailType)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldFullFamily_mass_bounds

Source: `RiffleLowerV2/Localization/Geometry/Consequences.lean:43`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldFullFamily_mass_bounds : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ N →
    ∀ (hN : 0 < N) (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
      (G : RiffleLowerV2.ColdGeometryData K P W) {xi : ℝ},
      W.ms ≤ W.mu →
        W.mu + W.bridgeLength ≤ K →
          RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) =
              ↑N ^ RiffleLowerV2.beta cuts hN (W.s N) →
            RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.prefixColumns K W) xi W.theta G.prefixType →
              RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.tailColumns K W) xi 2 G.tailType →
                0 < RiffleLowerV2.massOn cuts G.central →
                  ∀ y ∈ RiffleLowerV2.coldFullFamily cuts hN P W G,
                    Real.exp (-2) * ↑N ^ RiffleLowerV2.geometryZ cuts hN P W G < ↑N * RiffleLowerV2.wordMass cuts y ∧
                      ↑N * RiffleLowerV2.wordMass cuts y ≤ ↑N ^ RiffleLowerV2.geometryZ cuts hN P W G
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldGeometryFromEmpirical

Source: `RiffleLowerV2/Localization/Main.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldGeometryFromEmpirical : RiffleLowerV2.Targets.ColdGeometryFromEmpiricalTarget
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldLocalization_failure_le_envelope

Source: `RiffleLowerV2/Localization/Events.lean:57`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldLocalization_failure_le_envelope : ∀ {k N K : ℕ},
  2 ≤ k →
    ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
      2 ≤ N →
        ∀ {T eta rho chi xi : ℝ},
          0 < T →
            0 < eta →
              ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
                (G : RiffleLowerV2.ColdGeometryData K P W),
                RiffleLowerV2.WitnessSpec cuts hN eta rho chi W →
                  RiffleLowerV2.GeometrySpec cuts hN eta rho chi xi P W G →
                    ↑K ≤ T * TimeProfile.logScale N →
                      4 * ↑k * T * TimeProfile.logScale N + 4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 4) →
                        4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 2) →
                          16 ≤ ↑N ^ (5 * RiffleLowerV2.kappa eta / 2) →
                            (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                                fun (omega : TimeProfile.ShuffleSample cuts) =>
                                ¬RiffleLowerV2.ColdLocalization hN P W G omega) ≤
                              2 * (T + 1) * ↑N ^ (1 + T * Real.log ↑k) *
                                Real.exp (-↑N ^ (RiffleLowerV2.kappa eta / 4) / 8)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldLocalization_failure_le_prefixFailure

Source: `RiffleLowerV2/Localization/Events.lean:38`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldLocalization_failure_le_prefixFailure : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ {T eta rho chi xi : ℝ},
      0 < T →
        0 < eta →
          ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
            (G : RiffleLowerV2.ColdGeometryData K P W),
            RiffleLowerV2.WitnessSpec cuts hN eta rho chi W →
              RiffleLowerV2.GeometrySpec cuts hN eta rho chi xi P W G →
                ↑K ≤ T * TimeProfile.logScale N →
                  4 * ↑k * T * TimeProfile.logScale N + 4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 4) →
                    4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 2) →
                      16 ≤ ↑N ^ (5 * RiffleLowerV2.kappa eta / 2) →
                        (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts)
                            fun (omega : TimeProfile.ShuffleSample cuts) =>
                            ¬RiffleLowerV2.ColdLocalization hN P W G omega) ≤
                          RiffleLowerV2.prefixFailure N k K (RiffleLowerV2.kappa eta / 4)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldLocalization_of_prefix_event

Source: `RiffleLowerV2/Localization/Events.lean:11`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldLocalization_of_prefix_event : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ {T eta rho chi xi : ℝ},
      0 < T →
        0 < eta →
          ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
            (G : RiffleLowerV2.ColdGeometryData K P W),
            RiffleLowerV2.WitnessSpec cuts hN eta rho chi W →
              RiffleLowerV2.GeometrySpec cuts hN eta rho chi xi P W G →
                ↑K ≤ T * TimeProfile.logScale N →
                  4 * ↑k * T * TimeProfile.logScale N + 4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 4) →
                    4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 2) →
                      16 ≤ ↑N ^ (5 * RiffleLowerV2.kappa eta / 2) →
                        ∀ (omega : RiffleLowerV2.Sample cuts),
                          RiffleLowerV2.allPrefixEvent (RiffleLowerV2.kappa eta / 4) omega →
                            RiffleLowerV2.ColdLocalization hN P W G omega
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldRelativeSet_estimates

Source: `RiffleLowerV2/Localization/ColdSet.lean:10`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldRelativeSet_estimates : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData) (G : RiffleLowerV2.ColdGeometryData K P W)
      {xi kap : ℝ},
      0 < kap →
        12 / kap ≤ TimeProfile.logScale N →
          RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) =
              ↑N ^ RiffleLowerV2.beta cuts hN (W.s N) →
            RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.prefixColumns K W) xi W.theta G.prefixType →
              RiffleLowerV2.beta cuts hN (W.s N) / 2 + 2 * kap ≤ RiffleLowerV2.geometryEllP cuts hN P W G →
                RiffleLowerV2.typeH cuts hN P (RiffleLowerV2.prefixColumns K W) G.prefixType ≤
                    RiffleLowerV2.geometryEllP cuts hN P W G - kap →
                  kap / 2 ≤ RiffleLowerV2.geometryH cuts hN P W G →
                    Real.exp (-2) * ↑N ^ RiffleLowerV2.geometryH cuts hN P W G ≤
                        ↑(RiffleLowerV2.coldRelativeSet cuts hN P W G).card ∧
                      ↑(RiffleLowerV2.coldRelativeSet cuts hN P W G).card ≤
                          2 * ↑N ^ RiffleLowerV2.geometryH cuts hN P W G ∧
                        ↑N ^ (kap / 3) ≤ ↑(RiffleLowerV2.coldRelativeSet cuts hN P W G).card ∧
                          ↑(RiffleLowerV2.coldRelativeSet cuts hN P W G).card ≤ ↑N ∧
                            ∀ (q : Fin (N + 1)),
                              ↑(RiffleLowerV2.boundary
                                      (RiffleLowerV2.clipTranslate N (RiffleLowerV2.coldRelativeSet cuts hN P W G)
                                        ↑↑q)).card ≤
                                4 * √↑(RiffleLowerV2.coldRelativeSet cuts hN P W G).card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldWord_mem_translate

Source: `RiffleLowerV2/Localization/RankBarriers.lean:293`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldWord_mem_translate : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {P : TimeProfile.BorelPartition k}
  {W : RiffleLowerV2.ColdWitnessData} (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      RiffleLowerV2.wordOnList G.reserveMinus < RiffleLowerV2.wordOnList G.central →
        RiffleLowerV2.wordOnList G.central < RiffleLowerV2.wordOnList G.reservePlus →
          ∀ x ∈ RiffleLowerV2.coldPrefixFamily cuts hN P W G,
            ∀ (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) (e : ℝ) (omega : RiffleLowerV2.Sample cuts),
              |↑(RiffleLowerV2.relativeLowerCount G.ambient W.ms W.mu x omega) -
                      RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) *
                        RiffleLowerV2.relativeMassBefore cuts x| ≤
                  e →
                |↑(RiffleLowerV2.relativeUpperCount G.ambient W.ms W.mu x omega) -
                        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) *
                          (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x)| ≤
                    e →
                  e + 2 ≤ ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reserveMinus) omega) →
                    e + 2 ≤ ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reservePlus) omega) →
                      ∀ (i : Fin N),
                        RiffleLowerV2.sortedWord omega i = RiffleLowerV2.joinColdWord G x G.central z →
                          i ∈
                            RiffleLowerV2.clipTranslate N (RiffleLowerV2.coldRelativeSet cuts hN P W G)
                              ↑(RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt W.ms G.ambient) omega)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.coldWord_rank_barriers

Source: `RiffleLowerV2/Localization/RankBarriers.lean:243`. Kind: theorem.

```lean
RiffleLowerV2.Localization.coldWord_rank_barriers : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      RiffleLowerV2.wordOnList G.reserveMinus < RiffleLowerV2.wordOnList G.central →
        RiffleLowerV2.wordOnList G.central < RiffleLowerV2.wordOnList G.reservePlus →
          ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
            (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) (omega : RiffleLowerV2.Sample cuts)
            (i : Fin N),
            RiffleLowerV2.sortedWord omega i = RiffleLowerV2.joinColdWord G x G.central z →
              RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt W.ms G.ambient) omega +
                      RiffleLowerV2.relativeLowerCount G.ambient W.ms W.mu x omega +
                    RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reserveMinus) omega ≤
                  ↑i ∧
                ↑i + 1 + RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reservePlus) omega ≤
                  RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt W.ms G.ambient) omega +
                    RiffleLowerV2.relativeUpperCount G.ambient W.ms W.mu x omega
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.cold_selected_digits

Source: `RiffleLowerV2/Localization/Geometry/Consequences.lean:183`. Kind: theorem.

```lean
RiffleLowerV2.Localization.cold_selected_digits : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ k →
    ∀ (hN : 0 < N) (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
      (G : RiffleLowerV2.ColdGeometryData K P W) {xi chi : ℝ},
      0 < xi →
        0 < chi →
          RiffleLowerV2.IsCanonicalMaxWord cuts G.ambient →
            RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.prefixColumns K W) xi W.theta G.prefixType →
              RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.tailColumns K W) xi 2 G.tailType →
                (∀ v ∈ {G.central, G.reserveMinus, G.reservePlus},
                    ∀ (j : ↥(RiffleLowerV2.bridgeColumns K W)), min chi (1 / ↑k) ≤ ↑(cuts.count (↑j) (v j)) / ↑N) →
                  have c := min xi (min chi (1 / ↑k));
                  0 < c ∧
                    (∀ y ∈ RiffleLowerV2.coldFullFamily cuts hN P W G,
                        ∀ (j : Fin K), c ≤ ↑(cuts.count j (List.Vector.get y j)) / ↑N) ∧
                      ∀ x ∈ RiffleLowerV2.coldPrefixFamily cuts hN P W G,
                        ∀ v ∈ {G.reserveMinus, G.reservePlus},
                          ∀ (j : Fin ↑(RiffleLowerV2.reservePrefix G x v).fst),
                            c ≤ ↑(cuts.count ⟨↑j, ⋯⟩ (List.Vector.get (RiffleLowerV2.reservePrefix G x v).snd j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.collision_exponent_buffers

Source: `RiffleLowerV2/Localization/Geometry/Algebra.lean:36`. Kind: theorem.

```lean
RiffleLowerV2.Localization.collision_exponent_buffers : ∀ {b jp hp jt ht jps hps jts hts ellb dj dh kap kap0 err : ℝ},
  0 < kap →
    0 < kap0 →
      kap0 ≤ kap / 100 →
        err ≤ kap0 / 1000 →
          |jps - jp| + |hps - hp| ≤ err →
            |jts - (jt - dj)| + |hts - (ht - dh)| ≤ err →
              0 ≤ dj →
                dj ≤ kap0 / 50 →
                  dh ≤ kap0 / 50 →
                    0 ≤ ellb →
                      ellb ≤ kap0 / 50 →
                        kap ≤ 2 * b - 2 * jp - 2 * jt + hp + ht - (b - jp + hp) / 2 →
                          b - jp - jt < kap0 →
                            kap / 2 ≤ 2 * (b - jps - jts - ellb) + hps + hts - (b - jps + hps) / 2 ∧
                              b - jps - jts - ellb ≤ 2 * kap0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.columnSet_card

Source: `RiffleLowerV2/Localization/Words.lean:15`. Kind: theorem.

```lean
RiffleLowerV2.Localization.columnSet_card : ∀ {K a b : ℕ}, a ≤ b → b ≤ K → (RiffleLowerV2.columnSet K a b).card = b - a
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.columnSet_disjoint

Source: `RiffleLowerV2/Localization/Words.lean:35`. Kind: theorem.

```lean
RiffleLowerV2.Localization.columnSet_disjoint : ∀ {K a b c : ℕ}, Disjoint (RiffleLowerV2.columnSet K a b) (RiffleLowerV2.columnSet K b c)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.columnSet_size

Source: `RiffleLowerV2/Localization/Geometry/Empirical.lean:19`. Kind: theorem.

```lean
RiffleLowerV2.Localization.columnSet_size : ∀ {N : ℕ},
  2 ≤ N →
    ∀ {T : ℝ},
      0 ≤ T →
        ∀ (a b : ℕ), ↑(RiffleLowerV2.columnSet (TimeProfile.horizonDepth N T) a b).card ≤ T * TimeProfile.logScale N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.columnSet_union

Source: `RiffleLowerV2/Localization/Words.lean:29`. Kind: theorem.

```lean
RiffleLowerV2.Localization.columnSet_union : ∀ {K a b c : ℕ},
  a ≤ b → b ≤ c → RiffleLowerV2.columnSet K a b ∪ RiffleLowerV2.columnSet K b c = RiffleLowerV2.columnSet K a c
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.count_fraction_sum

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:56`. Kind: theorem.

```lean
RiffleLowerV2.Localization.count_fraction_sum : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K), 0 < N → ∀ (j : Fin K), ∑ d : Fin k, ↑(cuts.count j d) / ↑N = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.cylinder_mass

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:41`. Kind: theorem.

```lean
RiffleLowerV2.Localization.cylinder_mass : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α] [inst_2 : Fintype β] (p : α → β → ℝ),
  (∀ (j : α), ∑ d : β, p j d = 1) →
    ∀ (S : α → Prop) (z : α → β),
      (∑ y : α → β, if ∀ (h : α), S h → y h = z h then RiffleLowerV2.Localization.functionMass p y else 0) =
        ∏ h : α, if S h then p h (z h) else 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.deterministicColdGeometry

Source: `RiffleLowerV2/Localization/Geometry.lean:11`. Kind: theorem.

```lean
RiffleLowerV2.Localization.deterministicColdGeometry : RiffleLowerV2.Targets.DeterministicColdGeometryTarget
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.endpointError

Source: `RiffleLowerV2/Localization/Concentration.lean:9`. Kind: definition.

```lean
RiffleLowerV2.Localization.endpointError : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.endpointError_le

Source: `RiffleLowerV2/Localization/Concentration.lean:29`. Kind: theorem.

```lean
RiffleLowerV2.Localization.endpointError_le : ∀ {N k K : ℕ},
  2 ≤ N →
    ∀ {T kap b : ℝ},
      0 < T →
        0 < kap →
          4 * kap ≤ b →
            ↑K ≤ T * TimeProfile.logScale N →
              4 * ↑k * T * TimeProfile.logScale N + 4 ≤ ↑N ^ (kap / 4) →
                RiffleLowerV2.Localization.endpointError N k K kap b ≤ ↑N ^ (b / 2 + kap / 2)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.exists_bridgeGeometry

Source: `RiffleLowerV2/Localization/Bridge.lean:87`. Kind: theorem.

```lean
RiffleLowerV2.Localization.exists_bridgeGeometry : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ N →
    ∀ (hN : 0 < N),
      2 ≤ k →
        ∀ {eta rho chi : ℝ},
          0 < rho →
            0 < chi →
              ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData) (a : RiffleLowerV2.Word k K),
                RiffleLowerV2.IsCanonicalMaxWord cuts a →
                  ∀ (Dp Dt : RiffleLowerV2.RoundedTypeData P),
                    RiffleLowerV2.WitnessSpec cuts hN eta rho chi W →
                      ∃ (G : RiffleLowerV2.ColdGeometryData K P W),
                        G.ambient = a ∧
                          G.prefixType = Dp ∧
                            G.tailType = Dt ∧
                              RiffleLowerV2.BridgeSpec cuts hN rho chi G ∧
                                ∀ v ∈ {G.central, G.reserveMinus, G.reservePlus},
                                  ∀ (j : ↥(RiffleLowerV2.bridgeColumns K W)),
                                    min chi (1 / ↑k) ≤ ↑(cuts.count (↑j) (v j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.exists_geometry_scalar_thresholds

Source: `RiffleLowerV2/Localization/Geometry/Rates.lean:70`. Kind: theorem.

```lean
RiffleLowerV2.Localization.exists_geometry_scalar_thresholds : ∀ (k : ℕ),
  2 ≤ k →
    ∀ (eta rho chi : ℝ),
      0 < eta →
        0 < chi →
          2 * rho * Real.log ↑k ≤ RiffleLowerV2.kappa0 eta / 100 →
            ∃ (N0 : ℕ),
              2 ≤ N0 ∧
                ∀ (N : ℕ),
                  N0 ≤ N →
                    (2 * rho + 1 / TimeProfile.logScale N) * Real.log ↑k ≤ RiffleLowerV2.kappa0 eta / 50 ∧
                      2 * rho * Real.log ↑k + (Real.log ↑k + 2 * Real.log (1 / chi)) / TimeProfile.logScale N ≤
                          RiffleLowerV2.kappa0 eta / 50 ∧
                        12 / RiffleLowerV2.kappa eta ≤ TimeProfile.logScale N ∧
                          ∀ (b ell : ℝ),
                            b / 2 + 2 * RiffleLowerV2.kappa eta ≤ ell →
                              ↑N ^ (b / 2 + RiffleLowerV2.kappa eta) ≤
                                Real.exp (-1) * chi ^ 2 * ↑k ^ (-1) * ↑N ^ (ell - 2 * rho * Real.log ↑k)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.exists_localization_thresholds

Source: `RiffleLowerV2/Localization/Concentration.lean:122`. Kind: theorem.

```lean
RiffleLowerV2.Localization.exists_localization_thresholds : ∀ (k : ℕ) (T kap : ℝ),
  0 < kap →
    ∃ (N0 : ℕ),
      2 ≤ N0 ∧
        ∀ (N : ℕ),
          N0 ≤ N →
            4 * ↑k * T * TimeProfile.logScale N + 4 ≤ ↑N ^ (kap / 4) ∧ 4 ≤ ↑N ^ (kap / 2) ∧ 16 ≤ ↑N ^ (5 * kap / 2)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.exists_log_linear_rpow_threshold

Source: `RiffleLowerV2/Localization/Concentration.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Localization.exists_log_linear_rpow_threshold : ∀ (a B C : ℝ), 0 < a → ∃ (N0 : ℕ), 2 ≤ N0 ∧ ∀ (N : ℕ), N0 ≤ N → B * TimeProfile.logScale N + C ≤ ↑N ^ a
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.exists_rpow_threshold

Source: `RiffleLowerV2/Localization/Geometry/Rates.lean:62`. Kind: theorem.

```lean
RiffleLowerV2.Localization.exists_rpow_threshold : ∀ (a C : ℝ), 0 < a → ∃ (N0 : ℕ), 2 ≤ N0 ∧ ∀ (N : ℕ), N0 ≤ N → C ≤ ↑N ^ a
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.exists_small_type_cutoff

Source: `RiffleLowerV2/Localization/Geometry/Rates.lean:11`. Kind: theorem.

```lean
RiffleLowerV2.Localization.exists_small_type_cutoff : ∀ (k : ℕ), 2 ≤ k → ∀ (B err : ℝ), 0 < err → ∃ (xi : ℝ), 0 < xi ∧ xi < 1 / (4 * ↑k) ∧ B * xi * Real.log (1 / xi) ≤ err
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.exists_uniform_type_data

Source: `RiffleLowerV2/Localization/Geometry/Rates.lean:33`. Kind: theorem.

```lean
RiffleLowerV2.Localization.exists_uniform_type_data : ∀ (k : ℕ),
  2 ≤ k →
    ∀ (T err : ℝ),
      0 < T →
        0 < err →
          ∃ (xi : ℝ),
            0 < xi ∧
              xi < 1 / (4 * ↑k) ∧
                ∃ (P : TimeProfile.BorelPartition k),
                  P.IsRegular xi 1 ∧
                    ∃ (N0 : ℕ),
                      2 ≤ N0 ∧
                        ∀ (N K : ℕ),
                          N0 ≤ N →
                            ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (I : Finset (Fin K)),
                              ↑I.card ≤ T * TimeProfile.logScale N →
                                ∀ alpha ∈ Set.Icc 2 4,
                                  ∃ (D : RiffleLowerV2.RoundedTypeData P),
                                    RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha D ∧
                                      RiffleLowerV2.TypeApproximation cuts hN P I alpha err D
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.finite_weight_error

Source: `RiffleLowerV2/Localization/Endpoints/Error.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Localization.finite_weight_error : ∀ {ι : Type u_1} (S : Finset ι) (mu value : ι → ℝ) (A M D : ℝ),
  0 ≤ A →
    0 ≤ M →
      0 ≤ D →
        (∀ (i : ι), 0 ≤ mu i) →
          ↑S.card ≤ D →
            ∑ i ∈ S, mu i ≤ M →
              (∀ i ∈ S, |value i - mu i| ≤ A * (√(mu i) + 1)) → |∑ i ∈ S, (value i - mu i)| ≤ A * (√D * √M + D)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.firstRepeatedWordEdge

Source: `RiffleLowerV2/Localization/Edges.lean:31`. Kind: definition.

```lean
RiffleLowerV2.Localization.firstRepeatedWordEdge : {k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    (omega : RiffleLowerV2.Sample cuts) →
      (w : RiffleLowerV2.Word k K) → 2 ≤ RiffleLowerV2.wordCount w omega → Fin (N - 1)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.firstRepeatedWordEdge_injective

Source: `RiffleLowerV2/Localization/Edges.lean:54`. Kind: theorem.

```lean
RiffleLowerV2.Localization.firstRepeatedWordEdge_injective : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (omega : RiffleLowerV2.Sample cuts),
  Function.Injective fun (w : { w : RiffleLowerV2.Word k K // 2 ≤ RiffleLowerV2.wordCount w omega }) =>
    RiffleLowerV2.Localization.firstRepeatedWordEdge omega ↑w ⋯
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.firstRepeatedWordEdge_words

Source: `RiffleLowerV2/Localization/Edges.lean:39`. Kind: theorem.

```lean
RiffleLowerV2.Localization.firstRepeatedWordEdge_words : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (omega : RiffleLowerV2.Sample cuts) (w : RiffleLowerV2.Word k K)
  (hw : 2 ≤ RiffleLowerV2.wordCount w omega),
  RiffleLowerV2.sortedWord omega
        (RiffleLowerV2.edgeLeft (RiffleLowerV2.Localization.firstRepeatedWordEdge omega w hw)) =
      w ∧
    RiffleLowerV2.sortedWord omega
        (RiffleLowerV2.edgeRight (RiffleLowerV2.Localization.firstRepeatedWordEdge omega w hw)) =
      w
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.functionMass

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:25`. Kind: definition.

```lean
RiffleLowerV2.Localization.functionMass : {α : Type u_1} → {β : Type u_2} → [Fintype α] → (α → β → ℝ) → (α → β) → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.functionMass_sum

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:32`. Kind: theorem.

```lean
RiffleLowerV2.Localization.functionMass_sum : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α] [inst_2 : Fintype β] (p : α → β → ℝ),
  (∀ (j : α), ∑ d : β, p j d = 1) → ∑ y : α → β, RiffleLowerV2.Localization.functionMass p y = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.geometryError

Source: `RiffleLowerV2/Localization/Geometry/Algebra.lean:6`. Kind: definition.

```lean
RiffleLowerV2.Localization.geometryError : ℝ → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.geometryError_le_kappa

Source: `RiffleLowerV2/Localization/Geometry/Algebra.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Localization.geometryError_le_kappa : ∀ (eta : ℝ), RiffleLowerV2.Localization.geometryError eta ≤ RiffleLowerV2.kappa eta / 1000
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.geometryError_le_kappa0

Source: `RiffleLowerV2/Localization/Geometry/Algebra.lean:16`. Kind: theorem.

```lean
RiffleLowerV2.Localization.geometryError_le_kappa0 : ∀ (eta : ℝ), RiffleLowerV2.Localization.geometryError eta ≤ RiffleLowerV2.kappa0 eta / 1000
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.geometryError_pos

Source: `RiffleLowerV2/Localization/Geometry/Algebra.lean:8`. Kind: theorem.

```lean
RiffleLowerV2.Localization.geometryError_pos : ∀ {eta : ℝ}, 0 < eta → 0 < RiffleLowerV2.Localization.geometryError eta
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.geometry_exponent_bounds

Source: `RiffleLowerV2/Localization/Geometry/Bounds.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.geometry_exponent_bounds : ∀ {k N K : ℕ},
  2 ≤ k →
    2 ≤ N →
      ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) {eta rho chi : ℝ},
        0 < eta →
          0 < rho →
            ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
              (G : RiffleLowerV2.ColdGeometryData K P W),
              RiffleLowerV2.WitnessSpec cuts hN eta rho chi W →
                RiffleLowerV2.TypeApproximation cuts hN P (RiffleLowerV2.prefixColumns K W) W.theta
                    (RiffleLowerV2.Localization.geometryError eta) G.prefixType →
                  RiffleLowerV2.TypeApproximation cuts hN P (RiffleLowerV2.tailColumns K W) 2
                      (RiffleLowerV2.Localization.geometryError eta) G.tailType →
                    RiffleLowerV2.BridgeSpec cuts hN rho chi G →
                      (2 * rho + 1 / TimeProfile.logScale N) * Real.log ↑k ≤ RiffleLowerV2.kappa0 eta / 50 →
                        2 * rho * Real.log ↑k + (Real.log ↑k + 2 * Real.log (1 / chi)) / TimeProfile.logScale N ≤
                            RiffleLowerV2.kappa0 eta / 50 →
                          have b := RiffleLowerV2.beta cuts hN (W.s N);
                          have ellp := RiffleLowerV2.geometryEllP cuts hN P W G;
                          have hp := RiffleLowerV2.typeH cuts hN P (RiffleLowerV2.prefixColumns K W) G.prefixType;
                          have h := RiffleLowerV2.geometryH cuts hN P W G;
                          have z := RiffleLowerV2.geometryZ cuts hN P W G;
                          have g := RiffleLowerV2.geometryG cuts hN P W G;
                          b / 2 + 2 * RiffleLowerV2.kappa eta ≤ ellp ∧
                            hp ≤ ellp - RiffleLowerV2.kappa eta ∧
                              RiffleLowerV2.kappa eta / 2 ≤ h ∧
                                RiffleLowerV2.kappa eta / 2 ≤ g - h / 2 ∧ z ≤ 2 * RiffleLowerV2.kappa0 eta
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.goodColumn_ordered_digits

Source: `RiffleLowerV2/Localization/Bridge.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.goodColumn_ordered_digits : ∀ {k : ℕ} {p : TimeProfile.Simplex k} {chi : ℝ},
  TimeProfile.GoodColumn p chi →
    ∃ (lo : Fin k) (hi : Fin k), lo < hi ∧ chi ≤ TimeProfile.prob p lo ∧ chi ≤ TimeProfile.prob p hi
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.gridTime_le_horizon

Source: `RiffleLowerV2/Localization/Geometry/Empirical.lean:16`. Kind: theorem.

```lean
RiffleLowerV2.Localization.gridTime_le_horizon : ∀ {N K m : ℕ}, 2 ≤ N → m ≤ K → RiffleLowerV2.gridTime N m ≤ RiffleLowerV2.horizon N K
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.gridTime_mono

Source: `RiffleLowerV2/Localization/Geometry/Empirical.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Localization.gridTime_mono : ∀ {N : ℕ}, 2 ≤ N → ∀ {a b : ℕ}, a ≤ b → RiffleLowerV2.gridTime N a ≤ RiffleLowerV2.gridTime N b
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.gridTime_nonneg

Source: `RiffleLowerV2/Localization/Geometry/Empirical.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.gridTime_nonneg : ∀ {N : ℕ}, 2 ≤ N → ∀ (m : ℕ), 0 ≤ RiffleLowerV2.gridTime N m
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.half_reserve_mean_dominates

Source: `RiffleLowerV2/Localization/Concentration.lean:91`. Kind: theorem.

```lean
RiffleLowerV2.Localization.half_reserve_mean_dominates : ∀ {N : ℕ},
  2 ≤ N →
    ∀ {kap b mu e : ℝ},
      0 < kap →
        4 * kap ≤ b →
          ↑N ^ (b / 2 + kap) ≤ mu →
            e ≤ ↑N ^ (b / 2 + kap / 2) → 4 ≤ ↑N ^ (kap / 2) → 16 ≤ ↑N ^ (5 * kap / 2) → e + 2 ≤ mu / 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_Ico_card_le

Source: `RiffleLowerV2/Localization/Intervals.lean:88`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_Ico_card_le : ∀ (a b : ℤ), (RiffleLowerV2.integerBoundary (Finset.Ico a b)).card ≤ 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_Ico_subset

Source: `RiffleLowerV2/Localization/Intervals.lean:81`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_Ico_subset : ∀ (a b : ℤ), RiffleLowerV2.integerBoundary (Finset.Ico a b) ⊆ {a - 1, b - 1}
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_biUnion_subset

Source: `RiffleLowerV2/Localization/Intervals.lean:69`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_biUnion_subset : ∀ {α : Type u_1} (S : Finset α) (H : α → Finset ℤ),
  RiffleLowerV2.integerBoundary (S.biUnion H) ⊆ S.biUnion fun (a : α) => RiffleLowerV2.integerBoundary (H a)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_integerHalfOpen_card_le

Source: `RiffleLowerV2/Localization/Intervals.lean:93`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_integerHalfOpen_card_le : ∀ (l r : ℝ), (RiffleLowerV2.integerBoundary (RiffleLowerV2.integerHalfOpen l r)).card ≤ 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_inter_subset

Source: `RiffleLowerV2/Localization/Intervals.lean:63`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_inter_subset : ∀ (H J : Finset ℤ),
  RiffleLowerV2.integerBoundary (H ∩ J) ⊆ RiffleLowerV2.integerBoundary H ∪ RiffleLowerV2.integerBoundary J
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_intervalUnion_card_le

Source: `RiffleLowerV2/Localization/Intervals.lean:98`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_intervalUnion_card_le : ∀ {α : Type u_1} (S : Finset α) (l r : α → ℝ),
  (RiffleLowerV2.integerBoundary (S.biUnion fun (a : α) => RiffleLowerV2.integerHalfOpen (l a) (r a))).card ≤ 2 * S.card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_translate

Source: `RiffleLowerV2/Localization/Intervals.lean:110`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_translate : ∀ (H : Finset ℤ) (q : ℤ),
  RiffleLowerV2.integerBoundary (Finset.image (fun (z : ℤ) => z + q) H) =
    Finset.image (fun (z : ℤ) => z + q) (RiffleLowerV2.integerBoundary H)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerBoundary_union_subset

Source: `RiffleLowerV2/Localization/Intervals.lean:57`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerBoundary_union_subset : ∀ (H J : Finset ℤ),
  RiffleLowerV2.integerBoundary (H ∪ J) ⊆ RiffleLowerV2.integerBoundary H ∪ RiffleLowerV2.integerBoundary J
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerHalfOpen_card_bounds

Source: `RiffleLowerV2/Localization/Intervals.lean:30`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerHalfOpen_card_bounds : ∀ {l r : ℝ},
  l ≤ r → r - l - 1 ≤ ↑(RiffleLowerV2.integerHalfOpen l r).card ∧ ↑(RiffleLowerV2.integerHalfOpen l r).card ≤ r - l + 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerHalfOpen_card_eq

Source: `RiffleLowerV2/Localization/Intervals.lean:25`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerHalfOpen_card_eq : ∀ {l r : ℝ}, l ≤ r → ↑(RiffleLowerV2.integerHalfOpen l r).card = ↑⌈r⌉ - ↑⌈l⌉
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerHalfOpen_disjoint

Source: `RiffleLowerV2/Localization/Intervals.lean:37`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerHalfOpen_disjoint : ∀ {l r l' r' : ℝ}, r ≤ l' → Disjoint (RiffleLowerV2.integerHalfOpen l r) (RiffleLowerV2.integerHalfOpen l' r')
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.integerHalfOpen_eq_Ico

Source: `RiffleLowerV2/Localization/Intervals.lean:20`. Kind: theorem.

```lean
RiffleLowerV2.Localization.integerHalfOpen_eq_Ico : ∀ (l r : ℝ), RiffleLowerV2.integerHalfOpen l r = Finset.Ico ⌈l⌉ ⌈r⌉
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.intervalUnion_card_bounds

Source: `RiffleLowerV2/Localization/Intervals.lean:171`. Kind: theorem.

```lean
RiffleLowerV2.Localization.intervalUnion_card_bounds : ∀ {α : Type u_1} (S : Finset α) (l r : α → ℝ),
  (∀ a ∈ S, l a ≤ r a) →
    ((↑S).PairwiseDisjoint fun (a : α) => RiffleLowerV2.integerHalfOpen (l a) (r a)) →
      ∑ a ∈ S, (r a - l a) - ↑S.card ≤ ↑(S.biUnion fun (a : α) => RiffleLowerV2.integerHalfOpen (l a) (r a)).card ∧
        ↑(S.biUnion fun (a : α) => RiffleLowerV2.integerHalfOpen (l a) (r a)).card ≤ ∑ a ∈ S, (r a - l a) + ↑S.card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_bridge_lt

Source: `RiffleLowerV2/Localization/RankBarriers.lean:229`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_bridge_lt : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
        (v v' : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
        (z z' : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)),
        RiffleLowerV2.wordOnList v < RiffleLowerV2.wordOnList v' →
          List.take (W.mu + W.bridgeLength) (List.Vector.toList (RiffleLowerV2.joinColdWord G x v z)) <
            List.take (W.mu + W.bridgeLength) (List.Vector.toList (RiffleLowerV2.joinColdWord G x v' z'))
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_digit_lower

Source: `RiffleLowerV2/Localization/Geometry/Consequences.lean:105`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_digit_lower : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
  (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
  (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) (c : ℝ),
  (∀ (j : Fin K), c ≤ ↑(cuts.count j (List.Vector.get G.ambient j)) / ↑N) →
    (∀ (j : ↥(RiffleLowerV2.prefixColumns K W)), c ≤ ↑(cuts.count (↑j) (x j)) / ↑N) →
      (∀ (j : ↥(RiffleLowerV2.bridgeColumns K W)), c ≤ ↑(cuts.count (↑j) (v j)) / ↑N) →
        (∀ (j : ↥(RiffleLowerV2.tailColumns K W)), c ≤ ↑(cuts.count (↑j) (z j)) / ↑N) →
          ∀ (j : Fin K), c ≤ ↑(cuts.count j (List.Vector.get (RiffleLowerV2.joinColdWord G x v z) j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_get_ambient

Source: `RiffleLowerV2/Localization/Words.lean:95`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_get_ambient : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
      (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
      (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) (j : Fin K),
      ↑j < W.ms → List.Vector.get (RiffleLowerV2.joinColdWord G x v z) j = List.Vector.get G.ambient j
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_get_bridge

Source: `RiffleLowerV2/Localization/Words.lean:70`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_get_bridge : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
  (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
  (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) (j : ↥(RiffleLowerV2.bridgeColumns K W)),
  List.Vector.get (RiffleLowerV2.joinColdWord G x v z) ↑j = v j
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_get_prefix

Source: `RiffleLowerV2/Localization/Words.lean:63`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_get_prefix : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
  (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
  (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) (j : ↥(RiffleLowerV2.prefixColumns K W)),
  List.Vector.get (RiffleLowerV2.joinColdWord G x v z) ↑j = x j
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_get_tail

Source: `RiffleLowerV2/Localization/Words.lean:81`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_get_tail : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
  (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
  (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) (j : ↥(RiffleLowerV2.tailColumns K W)),
  List.Vector.get (RiffleLowerV2.joinColdWord G x v z) ↑j = z j
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_injective

Source: `RiffleLowerV2/Localization/Words.lean:139`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_injective : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W)),
  Function.Injective
    fun
      (xz :
        RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W) ×
          RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)) =>
    RiffleLowerV2.joinColdWord G xz.1 v xz.2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_mass

Source: `RiffleLowerV2/Localization/Words.lean:177`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_mass : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
        (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
        (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)),
        RiffleLowerV2.wordMass cuts (RiffleLowerV2.joinColdWord G x v z) =
          RiffleLowerV2.prefixMass cuts (RiffleLowerV2.prefixAt W.ms G.ambient) * RiffleLowerV2.massOn cuts x *
              RiffleLowerV2.massOn cuts v *
            RiffleLowerV2.massOn cuts z
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.joinColdWord_take_mu_eq

Source: `RiffleLowerV2/Localization/RankBarriers.lean:214`. Kind: theorem.

```lean
RiffleLowerV2.Localization.joinColdWord_take_mu_eq : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
        (v v' : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
        (z z' : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)),
        List.take W.mu (List.Vector.toList (RiffleLowerV2.joinColdWord G x v z)) =
          List.take W.mu (List.Vector.toList (RiffleLowerV2.joinColdWord G x v' z'))
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.lB09

Source: `RiffleLowerV2/Localization/Main.lean:33`. Kind: theorem.

```lean
RiffleLowerV2.Localization.lB09 : RiffleLowerV2.Targets.LB09Target
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.localization

Source: `RiffleLowerV2/Localization/Events.lean:73`. Kind: theorem.

```lean
RiffleLowerV2.Localization.localization : RiffleLowerV2.Targets.LocalizationTarget
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.localized_collisions_supply_edges

Source: `RiffleLowerV2/Localization/Edges.lean:67`. Kind: theorem.

```lean
RiffleLowerV2.Localization.localized_collisions_supply_edges : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (omega : RiffleLowerV2.Sample cuts) (Y : Finset (RiffleLowerV2.Word k K))
  (H : Finset (Fin N)),
  (∀ y ∈ Y, ∀ (i : Fin N), RiffleLowerV2.sortedWord omega i = y → i ∈ H) →
    {y ∈ Y | 2 ≤ RiffleLowerV2.wordCount y omega}.card ≤
      Finset.card (RiffleLowerV2.shuffleEdges omega ∩ RiffleLowerV2.internalEdges H)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.lowerRank_prefixAt

Source: `RiffleLowerV2/Localization/RankBarriers.lean:93`. Kind: theorem.

```lean
RiffleLowerV2.Localization.lowerRank_prefixAt : ∀ {k N K m : ℕ} {cuts : TimeProfile.Cuts k N K},
  m ≤ K →
    ∀ (w : RiffleLowerV2.Word k K) (omega : RiffleLowerV2.Sample cuts),
      RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt m w) omega =
        {i : Fin N |
            List.take m (List.Vector.toList (RiffleLowerV2.rowWord omega i)) < List.take m (List.Vector.toList w)}.card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.map_lt_map_iff

Source: `RiffleLowerV2/Localization/WordOrder.lean:11`. Kind: theorem.

```lean
RiffleLowerV2.Localization.map_lt_map_iff : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : LinearOrder β] (L : List α),
  List.Pairwise (fun (x1 x2 : α) => x1 < x2) L →
    ∀ (f g : α → β), List.map f L < List.map g L ↔ ∃ j ∈ L, f j < g j ∧ ∀ h ∈ L, h < j → f h = g h
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.massOn_eq_rpow_geometryEllB

Source: `RiffleLowerV2/Localization/Geometry/Consequences.lean:17`. Kind: theorem.

```lean
RiffleLowerV2.Localization.massOn_eq_rpow_geometryEllB : ∀ {k N K : ℕ},
  2 ≤ N →
    ∀ (cuts : TimeProfile.Cuts k N K) {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
      (G : RiffleLowerV2.ColdGeometryData K P W),
      0 < RiffleLowerV2.massOn cuts G.central →
        RiffleLowerV2.massOn cuts G.central = ↑N ^ (-RiffleLowerV2.geometryEllB cuts G)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.massOn_le_one_of_positive_population

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:26`. Kind: theorem.

```lean
RiffleLowerV2.Localization.massOn_le_one_of_positive_population : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N → ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I), RiffleLowerV2.massOn cuts x ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.massOn_nonnegative

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:10`. Kind: theorem.

```lean
RiffleLowerV2.Localization.massOn_nonnegative : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I),
  0 ≤ RiffleLowerV2.massOn cuts x
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.massOn_restrictWord

Source: `RiffleLowerV2/Localization/Words.lean:49`. Kind: theorem.

```lean
RiffleLowerV2.Localization.massOn_restrictWord : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (I : Finset (Fin K)) (w : RiffleLowerV2.Word k K),
  RiffleLowerV2.massOn cuts (RiffleLowerV2.restrictWord I w) = ∏ j ∈ I, ↑(cuts.count j (List.Vector.get w j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.massOn_sum

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:61`. Kind: theorem.

```lean
RiffleLowerV2.Localization.massOn_sum : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N → ∀ (I : Finset (Fin K)), ∑ y : RiffleLowerV2.WordOn k I, RiffleLowerV2.massOn cuts y = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.mem_columnSet

Source: `RiffleLowerV2/Localization/Words.lean:11`. Kind: theorem.

```lean
RiffleLowerV2.Localization.mem_columnSet : ∀ {K a b : ℕ} {j : Fin K}, j ∈ RiffleLowerV2.columnSet K a b ↔ a ≤ ↑j ∧ ↑j < b
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.mem_integerBoundary

Source: `RiffleLowerV2/Localization/Intervals.lean:45`. Kind: theorem.

```lean
RiffleLowerV2.Localization.mem_integerBoundary : ∀ (H : Finset ℤ) (z : ℤ), z ∈ RiffleLowerV2.integerBoundary H ↔ z ∈ H ∧ z + 1 ∉ H ∨ z ∉ H ∧ z + 1 ∈ H
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.mem_integerHalfOpen

Source: `RiffleLowerV2/Localization/Intervals.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.mem_integerHalfOpen : ∀ (l r : ℝ) (z : ℤ), z ∈ RiffleLowerV2.integerHalfOpen l r ↔ l ≤ ↑z ∧ ↑z < r
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixAt_eq_of_get

Source: `RiffleLowerV2/Localization/WordOrder.lean:71`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixAt_eq_of_get : ∀ {k K m : ℕ} {a b : RiffleLowerV2.Word k K},
  m ≤ K →
    (∀ (j : Fin K), ↑j < m → List.Vector.get a j = List.Vector.get b j) →
      RiffleLowerV2.prefixAt m a = RiffleLowerV2.prefixAt m b
```

Transitive axioms: `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixAt_joinColdWord

Source: `RiffleLowerV2/Localization/Words.lean:130`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixAt_joinColdWord : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
        (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
        (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)),
        RiffleLowerV2.prefixAt W.ms (RiffleLowerV2.joinColdWord G x v z) = RiffleLowerV2.prefixAt W.ms G.ambient
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixAt_toList

Source: `RiffleLowerV2/Localization/WordOrder.lean:63`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixAt_toList : ∀ {k K : ℕ} (m : ℕ) (a : RiffleLowerV2.Word k K),
  m ≤ K → List.Vector.toList (RiffleLowerV2.prefixAt m a).snd = List.take m (List.Vector.toList a)
```

Transitive axioms: `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixCount_add_lowerRank

Source: `RiffleLowerV2/Localization/RankBarriers.lean:183`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixCount_add_lowerRank : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (w : RiffleLowerV2.Prefix k K) (omega : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.lowerRank w omega + RiffleLowerV2.prefixCount w omega = RiffleLowerV2.upperRank w omega
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixMass_prefixAt_eq_prod

Source: `RiffleLowerV2/Localization/WordOrder.lean:82`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixMass_prefixAt_eq_prod : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (m : ℕ) (a : RiffleLowerV2.Word k K),
  m ≤ K →
    RiffleLowerV2.prefixMass cuts (RiffleLowerV2.prefixAt m a) =
      ∏ j ∈ RiffleLowerV2.columnSet K 0 m, ↑(cuts.count j (List.Vector.get a j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixMass_sidePrefix

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:10`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixMass_sidePrefix : ∀ {k N K l m : ℕ} (cuts : TimeProfile.Cuts k N K) (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (j : ↥(RiffleLowerV2.columnSet K l m)) (d : Fin k),
        RiffleLowerV2.prefixMass cuts (RiffleLowerV2.sidePrefix a l m x j d) =
          RiffleLowerV2.prefixMass cuts (RiffleLowerV2.prefixAt l a) *
            RiffleLowerV2.Localization.sideWeight
              (fun (h : ↥(RiffleLowerV2.columnSet K l m)) (e : Fin k) => ↑(cuts.count (↑h) e) / ↑N) x j d
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixMass_split

Source: `RiffleLowerV2/Localization/Words.lean:55`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixMass_split : ∀ {k N K a b : ℕ} (cuts : TimeProfile.Cuts k N K) (w : RiffleLowerV2.Word k K),
  a ≤ b →
    b ≤ K →
      RiffleLowerV2.prefixMass cuts (RiffleLowerV2.prefixAt b w) =
        RiffleLowerV2.prefixMass cuts (RiffleLowerV2.prefixAt a w) *
          RiffleLowerV2.massOn cuts (RiffleLowerV2.restrictWord (RiffleLowerV2.columnSet K a b) w)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixMean_le_population

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:31`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixMean_le_population : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N → ∀ (v : RiffleLowerV2.Prefix k K), RiffleLowerV2.prefixMean cuts v ≤ ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefixMean_sidePrefix

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:47`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefixMean_sidePrefix : ∀ {k N K l m : ℕ} (cuts : TimeProfile.Cuts k N K) (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (j : ↥(RiffleLowerV2.columnSet K l m)) (d : Fin k),
        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d) =
          RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a) *
            RiffleLowerV2.Localization.sideWeight
              (fun (h : ↥(RiffleLowerV2.columnSet K l m)) (e : Fin k) => ↑(cuts.count (↑h) e) / ↑N) x j d
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefix_event_cold_bounds

Source: `RiffleLowerV2/Localization/EventBounds.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefix_event_cold_bounds : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N),
  2 ≤ N →
    ∀ {T eta rho chi xi : ℝ},
      0 < T →
        0 < eta →
          ∀ (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
            (G : RiffleLowerV2.ColdGeometryData K P W),
            RiffleLowerV2.WitnessSpec cuts hN eta rho chi W →
              RiffleLowerV2.GeometrySpec cuts hN eta rho chi xi P W G →
                ↑K ≤ T * TimeProfile.logScale N →
                  4 * ↑k * T * TimeProfile.logScale N + 4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 4) →
                    4 ≤ ↑N ^ (RiffleLowerV2.kappa eta / 2) →
                      16 ≤ ↑N ^ (5 * RiffleLowerV2.kappa eta / 2) →
                        ∀ (omega : RiffleLowerV2.Sample cuts),
                          RiffleLowerV2.allPrefixEvent (RiffleLowerV2.kappa eta / 4) omega →
                            have b := RiffleLowerV2.beta cuts hN (W.s N);
                            have e := RiffleLowerV2.Localization.endpointError N k K (RiffleLowerV2.kappa eta) b;
                            (∀ x ∈ RiffleLowerV2.coldPrefixFamily cuts hN P W G,
                                |↑(RiffleLowerV2.relativeLowerCount G.ambient W.ms W.mu x omega) -
                                        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) *
                                          RiffleLowerV2.relativeMassBefore cuts x| +
                                    |↑(RiffleLowerV2.relativeUpperCount G.ambient W.ms W.mu x omega) -
                                        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) *
                                          (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x)| ≤
                                  e) ∧
                              ∀ x ∈ RiffleLowerV2.coldPrefixFamily cuts hN P W G,
                                e + 2 ≤
                                    ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reserveMinus)
                                        omega) ∧
                                  e + 2 ≤
                                    ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.reservePrefix G x G.reservePlus) omega)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefix_exponent_buffers

Source: `RiffleLowerV2/Localization/Geometry/Algebra.lean:21`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefix_exponent_buffers : ∀ {b jp hp jstar hstar kap err : ℝ},
  0 < kap →
    err ≤ kap / 1000 →
      hp ≤ jp →
        jp ≤ b / 2 - 3 * kap →
          kap ≤ b - jp + hp →
            |jstar - jp| + |hstar - hp| ≤ err →
              b / 2 + 2 * kap ≤ b - jstar ∧ hstar ≤ b - jstar - kap ∧ kap / 2 ≤ b - jstar + hstar
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefix_rank_bounds

Source: `RiffleLowerV2/Localization/Edges.lean:7`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefix_rank_bounds : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (omega : RiffleLowerV2.Sample cuts) (w : RiffleLowerV2.Prefix k K),
  RiffleLowerV2.lowerRank w omega ≤ RiffleLowerV2.upperRank w omega ∧ RiffleLowerV2.upperRank w omega ≤ N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prefix_rank_bounds_of_take_eq

Source: `RiffleLowerV2/Localization/RankBarriers.lean:193`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prefix_rank_bounds_of_take_eq : ∀ {k N K l m : ℕ} {cuts : TimeProfile.Cuts k N K},
  l ≤ m →
    m ≤ K →
      ∀ (a w : RiffleLowerV2.Word k K),
        List.take l (List.Vector.toList w) = List.take l (List.Vector.toList a) →
          ∀ (omega : RiffleLowerV2.Sample cuts),
            RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt l a) omega ≤
                RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt m w) omega ∧
              RiffleLowerV2.upperRank (RiffleLowerV2.prefixAt m w) omega ≤
                RiffleLowerV2.upperRank (RiffleLowerV2.prefixAt l a) omega
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.probabilityIntervals_card_bounds

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:115`. Kind: theorem.

```lean
RiffleLowerV2.Localization.probabilityIntervals_card_bounds : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {I : Finset (Fin K)} (S : Finset (RiffleLowerV2.WordOn k I)) {mu Q : ℝ},
  0 ≤ mu →
    (∀ x ∈ S, Real.exp (-1) * Q ≤ mu * RiffleLowerV2.massOn cuts x ∧ mu * RiffleLowerV2.massOn cuts x ≤ Q) →
      ↑S.card * (Real.exp (-1) * Q - 1) ≤
          ↑(S.biUnion fun (x : RiffleLowerV2.WordOn k I) =>
                RiffleLowerV2.integerHalfOpen (mu * RiffleLowerV2.relativeMassBefore cuts x)
                  (mu * (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x))).card ∧
        ↑(S.biUnion fun (x : RiffleLowerV2.WordOn k I) =>
                RiffleLowerV2.integerHalfOpen (mu * RiffleLowerV2.relativeMassBefore cuts x)
                  (mu * (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x))).card ≤
          ↑S.card * (Q + 1)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.probabilityIntervals_card_le_population

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:98`. Kind: theorem.

```lean
RiffleLowerV2.Localization.probabilityIntervals_card_le_population : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ {I : Finset (Fin K)} (S : Finset (RiffleLowerV2.WordOn k I)) {mu : ℝ},
      0 ≤ mu →
        mu ≤ ↑N →
          (S.biUnion fun (x : RiffleLowerV2.WordOn k I) =>
                RiffleLowerV2.integerHalfOpen (mu * RiffleLowerV2.relativeMassBefore cuts x)
                  (mu * (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x))).card ≤
            N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.probabilityIntervals_pairwiseDisjoint

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:85`. Kind: theorem.

```lean
RiffleLowerV2.Localization.probabilityIntervals_pairwiseDisjoint : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {I : Finset (Fin K)} (S : Finset (RiffleLowerV2.WordOn k I)) {mu : ℝ},
  0 ≤ mu →
    (↑S).PairwiseDisjoint fun (x : RiffleLowerV2.WordOn k I) =>
      RiffleLowerV2.integerHalfOpen (mu * RiffleLowerV2.relativeMassBefore cuts x)
        (mu * (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x))
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.probability_add_complement

Source: `RiffleLowerV2/Localization/Probability.lean:8`. Kind: theorem.

```lean
RiffleLowerV2.Localization.probability_add_complement : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop),
  (RiffleLowerV2.probability P A + RiffleLowerV2.probability P fun (omega : Ω) => ¬A omega) = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.probability_ge_one_sub_failure

Source: `RiffleLowerV2/Localization/Probability.lean:25`. Kind: theorem.

```lean
RiffleLowerV2.Localization.probability_ge_one_sub_failure : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A B : Ω → Prop) {e : ℝ},
  (∀ (omega : Ω), A omega → B omega) →
    (RiffleLowerV2.probability P fun (omega : Ω) => ¬A omega) ≤ e → 1 - e ≤ RiffleLowerV2.probability P B
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prod_columnSet_split

Source: `RiffleLowerV2/Localization/Words.lean:43`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prod_columnSet_split : ∀ {K a b c : ℕ} (f : Fin K → ℝ),
  a ≤ b →
    b ≤ c →
      ∏ j ∈ RiffleLowerV2.columnSet K a c, f j =
        (∏ j ∈ RiffleLowerV2.columnSet K a b, f j) * ∏ j ∈ RiffleLowerV2.columnSet K b c, f j
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.prod_subtype_dite

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.prod_subtype_dite : ∀ {α : Type u_1} [inst : Fintype α] (I : Finset α) (f : ↥I → ℝ),
  (∏ j : α, if hj : j ∈ I then f ⟨j, hj⟩ else 1) = ∏ j : ↥I, f j
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.rankSet_clipTranslate

Source: `RiffleLowerV2/Localization/Intervals.lean:132`. Kind: theorem.

```lean
RiffleLowerV2.Localization.rankSet_clipTranslate : ∀ (N : ℕ) (H : Finset ℤ) (q : ℤ),
  RiffleLowerV2.rankSet (RiffleLowerV2.clipTranslate N H q) =
    Finset.image (fun (z : ℤ) => z + q) H ∩ Finset.Ico 1 (↑N + 1)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeEndpoint

Source: `RiffleLowerV2/Localization/Endpoints.lean:57`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeEndpoint : RiffleLowerV2.Targets.RelativeEndpointTarget
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeEndpoint_identities

Source: `RiffleLowerV2/Localization/Endpoints.lean:37`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeEndpoint_identities : ∀ {k N K l m : ℕ} (cuts : TimeProfile.Cuts k N K) (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (omega : RiffleLowerV2.Sample cuts),
        ↑(RiffleLowerV2.relativeLowerCount a l m x omega) -
              RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a) * RiffleLowerV2.relativeMassBefore cuts x =
            ∑ j : ↥(RiffleLowerV2.columnSet K l m),
              ∑ d : Fin k with d < x j,
                (↑(RiffleLowerV2.prefixCount (RiffleLowerV2.sidePrefix a l m x j d) omega) -
                  RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d)) ∧
          ↑(RiffleLowerV2.relativeUpperCount a l m x omega) -
              RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a) *
                (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x) =
            ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.prefixAt l a) omega) -
                RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a) -
              ∑ j : ↥(RiffleLowerV2.columnSet K l m),
                ∑ d : Fin k with x j < d,
                  (↑(RiffleLowerV2.prefixCount (RiffleLowerV2.sidePrefix a l m x j d) omega) -
                    RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d))
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeGreaterCount

Source: `RiffleLowerV2/Localization/Endpoints/Counts.lean:10`. Kind: definition.

```lean
RiffleLowerV2.Localization.relativeGreaterCount : {k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    RiffleLowerV2.Word k K →
      (l m : ℕ) → RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m) → RiffleLowerV2.Sample cuts → ℕ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeGreaterCount_eq_side_sum

Source: `RiffleLowerV2/Localization/Endpoints/Counts.lean:38`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeGreaterCount_eq_side_sum : ∀ {k N K l m : ℕ} {cuts : TimeProfile.Cuts k N K} (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (omega : RiffleLowerV2.Sample cuts),
        ↑(RiffleLowerV2.Localization.relativeGreaterCount a l m x omega) =
          ∑ j : ↥(RiffleLowerV2.columnSet K l m),
            ∑ d : Fin k with x j < d, ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.sidePrefix a l m x j d) omega)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeLowerCount_eq_side_sum

Source: `RiffleLowerV2/Localization/Endpoints/Counts.lean:16`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeLowerCount_eq_side_sum : ∀ {k N K l m : ℕ} {cuts : TimeProfile.Cuts k N K} (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (omega : RiffleLowerV2.Sample cuts),
        ↑(RiffleLowerV2.relativeLowerCount a l m x omega) =
          ∑ j : ↥(RiffleLowerV2.columnSet K l m),
            ∑ d : Fin k with d < x j, ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.sidePrefix a l m x j d) omega)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeLowerMean_eq_side_sum

Source: `RiffleLowerV2/Localization/Endpoints.lean:10`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeLowerMean_eq_side_sum : ∀ {k N K l m : ℕ} (cuts : TimeProfile.Cuts k N K) (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)),
        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a) * RiffleLowerV2.relativeMassBefore cuts x =
          ∑ j : ↥(RiffleLowerV2.columnSet K l m),
            ∑ d : Fin k with d < x j, RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeMassAfter

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:68`. Kind: definition.

```lean
RiffleLowerV2.Localization.relativeMassAfter : {k N K : ℕ} → TimeProfile.Cuts k N K → {I : Finset (Fin K)} → RiffleLowerV2.WordOn k I → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeMassAfter_eq_sideWeight

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:106`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeMassAfter_eq_sideWeight : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I),
      RiffleLowerV2.Localization.relativeMassAfter cuts x =
        ∑ j : ↥I,
          ∑ d : Fin k with x j < d,
            RiffleLowerV2.Localization.sideWeight (fun (h : ↥I) (e : Fin k) => ↑(cuts.count (↑h) e) / ↑N) x j d
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeMassBefore_add_mass_le_of_lt

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:64`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeMassBefore_add_mass_le_of_lt : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {I : Finset (Fin K)} {x y : RiffleLowerV2.WordOn k I},
  RiffleLowerV2.wordOnList x < RiffleLowerV2.wordOnList y →
    RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x ≤ RiffleLowerV2.relativeMassBefore cuts y
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeMassBefore_add_mass_le_one

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:50`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeMassBefore_add_mass_le_one : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I),
      RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeMassBefore_eq_sideWeight

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:86`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeMassBefore_eq_sideWeight : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I),
      RiffleLowerV2.relativeMassBefore cuts x =
        ∑ j : ↥I,
          ∑ d : Fin k with d < x j,
            RiffleLowerV2.Localization.sideWeight (fun (h : ↥I) (e : Fin k) => ↑(cuts.count (↑h) e) / ↑N) x j d
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeMassBefore_nonnegative

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:46`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeMassBefore_nonnegative : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I),
  0 ≤ RiffleLowerV2.relativeMassBefore cuts x
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeMass_total

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:130`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeMass_total : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I),
      RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x +
          RiffleLowerV2.Localization.relativeMassAfter cuts x =
        1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeUpperMean_eq_side_sum

Source: `RiffleLowerV2/Localization/Endpoints.lean:22`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeUpperMean_eq_side_sum : ∀ {k N K l m : ℕ} (cuts : TimeProfile.Cuts k N K) (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)),
        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a) *
            (RiffleLowerV2.relativeMassBefore cuts x + RiffleLowerV2.massOn cuts x) =
          RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a) -
            ∑ j : ↥(RiffleLowerV2.columnSet K l m),
              ∑ d : Fin k with x j < d, RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relativeUpper_add_greater

Source: `RiffleLowerV2/Localization/Endpoints/Counts.lean:65`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relativeUpper_add_greater : ∀ {k N K l m : ℕ} {cuts : TimeProfile.Cuts k N K} (a : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (omega : RiffleLowerV2.Sample cuts),
        ↑(RiffleLowerV2.relativeUpperCount a l m x omega) +
            ↑(RiffleLowerV2.Localization.relativeGreaterCount a l m x omega) =
          ↑(RiffleLowerV2.prefixCount (RiffleLowerV2.prefixAt l a) omega)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.relative_rank_decomposition

Source: `RiffleLowerV2/Localization/RankBarriers.lean:109`. Kind: theorem.

```lean
RiffleLowerV2.Localization.relative_rank_decomposition : ∀ {k N K l m : ℕ} {cuts : TimeProfile.Cuts k N K},
  l ≤ m →
    m ≤ K →
      ∀ (a w : RiffleLowerV2.Word k K) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)),
        List.take l (List.Vector.toList w) = List.take l (List.Vector.toList a) →
          RiffleLowerV2.restrictWord (RiffleLowerV2.columnSet K l m) w = x →
            ∀ (omega : RiffleLowerV2.Sample cuts),
              RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt m w) omega =
                  RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt l a) omega +
                    RiffleLowerV2.relativeLowerCount a l m x omega ∧
                RiffleLowerV2.upperRank (RiffleLowerV2.prefixAt m w) omega =
                  RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt l a) omega +
                    RiffleLowerV2.relativeUpperCount a l m x omega
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.reservePrefix_mean

Source: `RiffleLowerV2/Localization/Words.lean:157`. Kind: theorem.

```lean
RiffleLowerV2.Localization.reservePrefix_mean : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W),
  W.ms ≤ W.mu →
    W.mu + W.bridgeLength ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
        (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W)),
        RiffleLowerV2.prefixMean cuts (RiffleLowerV2.reservePrefix G x v) =
          RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) * RiffleLowerV2.massOn cuts x *
            RiffleLowerV2.massOn cuts v
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.reservePrefix_mean_lower

Source: `RiffleLowerV2/Localization/Geometry/Consequences.lean:122`. Kind: theorem.

```lean
RiffleLowerV2.Localization.reservePrefix_mean_lower : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ k →
    2 ≤ N →
      ∀ (hN : 0 < N) (P : TimeProfile.BorelPartition k) (W : RiffleLowerV2.ColdWitnessData)
        (G : RiffleLowerV2.ColdGeometryData K P W) {rho chi xi : ℝ},
        0 < rho →
          0 < chi →
            W.ms ≤ W.mu →
              W.mu + W.bridgeLength ≤ K →
                W.bridgeLength = ⌈2 * rho * TimeProfile.logScale N⌉₊ →
                  RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt W.ms G.ambient) =
                      ↑N ^ RiffleLowerV2.beta cuts hN (W.s N) →
                    RiffleLowerV2.TypeDataSpec cuts hN P (RiffleLowerV2.prefixColumns K W) xi W.theta G.prefixType →
                      RiffleLowerV2.BridgeSpec cuts hN rho chi G →
                        ∀ x ∈ RiffleLowerV2.coldPrefixFamily cuts hN P W G,
                          ∀ v ∈ {G.central, G.reserveMinus, G.reservePlus},
                            Real.exp (-1) * chi ^ 2 * ↑k ^ (-1) *
                                ↑N ^ (RiffleLowerV2.geometryEllP cuts hN P W G - 2 * rho * Real.log ↑k) ≤
                              RiffleLowerV2.prefixMean cuts (RiffleLowerV2.reservePrefix G x v)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.reserve_count_dominates

Source: `RiffleLowerV2/Localization/Concentration.lean:110`. Kind: theorem.

```lean
RiffleLowerV2.Localization.reserve_count_dominates : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  2 ≤ N →
    ∀ {kap b e : ℝ},
      0 < kap →
        4 * kap ≤ b →
          e ≤ ↑N ^ (b / 2 + kap / 2) →
            4 ≤ ↑N ^ (kap / 2) →
              16 ≤ ↑N ^ (5 * kap / 2) →
                ∀ (v : RiffleLowerV2.Prefix k K),
                  ↑N ^ (b / 2 + kap) ≤ RiffleLowerV2.prefixMean cuts v →
                    ∀ (omega : RiffleLowerV2.Sample cuts),
                      RiffleLowerV2.allPrefixEvent (kap / 4) omega → e + 2 ≤ ↑(RiffleLowerV2.prefixCount v omega)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.reserve_deviation_le_half

Source: `RiffleLowerV2/Localization/Concentration.lean:62`. Kind: theorem.

```lean
RiffleLowerV2.Localization.reserve_deviation_le_half : ∀ {N : ℕ},
  2 ≤ N →
    ∀ {kap b mu : ℝ},
      0 < kap → 4 * kap ≤ b → ↑N ^ (b / 2 + kap) ≤ mu → 16 ≤ ↑N ^ (5 * kap / 2) → ↑N ^ (kap / 4) * (√mu + 1) ≤ mu / 2
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.restrict_join_bridge

Source: `RiffleLowerV2/Localization/Words.lean:114`. Kind: theorem.

```lean
RiffleLowerV2.Localization.restrict_join_bridge : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
  (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
  (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)),
  RiffleLowerV2.restrictWord (RiffleLowerV2.bridgeColumns K W) (RiffleLowerV2.joinColdWord G x v z) = v
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.restrict_join_prefix

Source: `RiffleLowerV2/Localization/Words.lean:106`. Kind: theorem.

```lean
RiffleLowerV2.Localization.restrict_join_prefix : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
  (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
  (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)),
  RiffleLowerV2.restrictWord (RiffleLowerV2.prefixColumns K W) (RiffleLowerV2.joinColdWord G x v z) = x
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.restrict_join_tail

Source: `RiffleLowerV2/Localization/Words.lean:122`. Kind: theorem.

```lean
RiffleLowerV2.Localization.restrict_join_tail : ∀ {k K : ℕ} {P : TimeProfile.BorelPartition k} {W : RiffleLowerV2.ColdWitnessData}
  (G : RiffleLowerV2.ColdGeometryData K P W) (x : RiffleLowerV2.WordOn k (RiffleLowerV2.prefixColumns K W))
  (v : RiffleLowerV2.WordOn k (RiffleLowerV2.bridgeColumns K W))
  (z : RiffleLowerV2.WordOn k (RiffleLowerV2.tailColumns K W)),
  RiffleLowerV2.restrictWord (RiffleLowerV2.tailColumns K W) (RiffleLowerV2.joinColdWord G x v z) = z
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.selected_digit_lower

Source: `RiffleLowerV2/Localization/Geometry/Consequences.lean:9`. Kind: theorem.

```lean
RiffleLowerV2.Localization.selected_digit_lower : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) (I : Finset (Fin K))
  {xi alpha : ℝ} (D : RiffleLowerV2.RoundedTypeData P),
  RiffleLowerV2.TypeDataSpec cuts hN P I xi alpha D →
    ∀ x ∈ RiffleLowerV2.selectedClass cuts hN P I D, ∀ (j : ↥I), xi ≤ ↑(cuts.count (↑j) (x j)) / ↑N
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sideMatch

Source: `RiffleLowerV2/Localization/Endpoints/Partitions.lean:9`. Kind: definition.

```lean
RiffleLowerV2.Localization.sideMatch : {α : Type u_1} → {β : Type u_2} → [LT α] → (α → β) → (α → β) → α → β → Prop
```

Transitive axioms: none.

## RiffleLowerV2.Localization.sideMatch_iff_coordinates

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:69`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sideMatch_iff_coordinates : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] (x y : α → β) (j : α) (d : β),
  RiffleLowerV2.Localization.sideMatch x y j d ↔ ∀ h ≤ j, y h = if h = j then d else x h
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sideMatch_unique

Source: `RiffleLowerV2/Localization/Endpoints/Partitions.lean:12`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sideMatch_unique : ∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] {x y : α → β} {j q : α} {d e : β},
  RiffleLowerV2.Localization.sideMatch x y j d →
    RiffleLowerV2.Localization.sideMatch x y q e → d ≠ x j → e ≠ x q → j = q
```

Transitive axioms: `propext`.

## RiffleLowerV2.Localization.sideMean_sum_le

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:146`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sideMean_sum_le : ∀ {k N K l m : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ (a : RiffleLowerV2.Word k K),
      l ≤ m →
        m ≤ K →
          ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (R : Fin k → Fin k → Prop),
            (∀ (d e : Fin k), R d e → d ≠ e) →
              ∑ j : ↥(RiffleLowerV2.columnSet K l m),
                  ∑ d : Fin k with R d (x j), RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d) ≤
                RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sidePrefix_coordinates

Source: `RiffleLowerV2/Localization/Endpoints/Coordinates.lean:26`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sidePrefix_coordinates : ∀ {k K l m : ℕ} (a v : RiffleLowerV2.Word k K),
  l ≤ m →
    m ≤ K →
      ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (j : ↥(RiffleLowerV2.columnSet K l m)) (d : Fin k),
        List.take (↑(RiffleLowerV2.sidePrefix a l m x j d).fst) (List.Vector.toList v) =
            List.Vector.toList (RiffleLowerV2.sidePrefix a l m x j d).snd ↔
          List.take l (List.Vector.toList v) = List.take l (List.Vector.toList a) ∧
            RiffleLowerV2.Localization.sideMatch x (RiffleLowerV2.restrictWord (RiffleLowerV2.columnSet K l m) v) j d
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sideWeight

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:28`. Kind: definition.

```lean
RiffleLowerV2.Localization.sideWeight : {α : Type u_1} → {β : Type u_2} → [Fintype α] → [LinearOrder α] → (α → β → ℝ) → (α → β) → α → β → ℝ
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sideWeight_eq_massOn_sum

Source: `RiffleLowerV2/Localization/Endpoints/Means.lean:72`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sideWeight_eq_massOn_sum : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ {I : Finset (Fin K)} (x : RiffleLowerV2.WordOn k I) (j : ↥I) (d : Fin k),
      RiffleLowerV2.Localization.sideWeight (fun (h : ↥I) (e : Fin k) => ↑(cuts.count (↑h) e) / ↑N) x j d =
        ∑ y : RiffleLowerV2.WordOn k I,
          if RiffleLowerV2.Localization.sideMatch x y j d then RiffleLowerV2.massOn cuts y else 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sideWeight_eq_sum

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:82`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sideWeight_eq_sum : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : LinearOrder α] [inst_2 : Fintype β] (p : α → β → ℝ),
  (∀ (j : α), ∑ d : β, p j d = 1) →
    ∀ (x : α → β) (j : α) (d : β),
      RiffleLowerV2.Localization.sideWeight p x j d =
        ∑ y : α → β,
          if RiffleLowerV2.Localization.sideMatch x y j d then RiffleLowerV2.Localization.functionMass p y else 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sideWeight_nonneg

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:90`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sideWeight_nonneg : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : LinearOrder α] (p : α → β → ℝ),
  (∀ (j : α) (d : β), 0 ≤ p j d) → ∀ (x : α → β) (j : α) (d : β), 0 ≤ RiffleLowerV2.Localization.sideWeight p x j d
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.side_error_bound

Source: `RiffleLowerV2/Localization/Endpoints/Error.lean:33`. Kind: theorem.

```lean
RiffleLowerV2.Localization.side_error_bound : ∀ {k N K l m : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N →
    ∀ (a : RiffleLowerV2.Word k K),
      l ≤ m →
        m ≤ K →
          ∀ (x : RiffleLowerV2.WordOn k (RiffleLowerV2.columnSet K l m)) (omega : RiffleLowerV2.Sample cuts) (A : ℝ),
            0 < A →
              (∀ (v : RiffleLowerV2.Prefix k K),
                  |↑(RiffleLowerV2.prefixCount v omega) - RiffleLowerV2.prefixMean cuts v| ≤
                    A * (√(RiffleLowerV2.prefixMean cuts v) + 1)) →
                ∀ (R : Fin k → Fin k → Prop),
                  (∀ (d e : Fin k), R d e → d ≠ e) →
                    |∑ j : ↥(RiffleLowerV2.columnSet K l m),
                          ∑ d : Fin k with R d (x j),
                            (↑(RiffleLowerV2.prefixCount (RiffleLowerV2.sidePrefix a l m x j d) omega) -
                              RiffleLowerV2.prefixMean cuts (RiffleLowerV2.sidePrefix a l m x j d))| ≤
                      A * (√(↑k * ↑K) * √(RiffleLowerV2.prefixMean cuts (RiffleLowerV2.prefixAt l a)) + ↑k * ↑K)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sortedWord_full_rank_iff

Source: `RiffleLowerV2/Localization/Edges.lean:16`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sortedWord_full_rank_iff : ∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (omega : RiffleLowerV2.Sample cuts) (w : RiffleLowerV2.Word k K)
  (i : Fin N),
  RiffleLowerV2.sortedWord omega i = w ↔
    RiffleLowerV2.lowerRank (RiffleLowerV2.fullPrefix w) omega ≤ ↑i ∧
      ↑i < RiffleLowerV2.upperRank (RiffleLowerV2.fullPrefix w) omega
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sorted_take_le_iff

Source: `RiffleLowerV2/Localization/RankBarriers.lean:163`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sorted_take_le_iff : ∀ {k N K m : ℕ} {cuts : TimeProfile.Cuts k N K},
  m ≤ K →
    ∀ (w : RiffleLowerV2.Word k K) (omega : RiffleLowerV2.Sample cuts) (i : Fin N),
      ↑i < RiffleLowerV2.upperRank (RiffleLowerV2.prefixAt m w) omega ↔
        List.take m (List.Vector.toList (RiffleLowerV2.sortedWord omega i)) ≤ List.take m (List.Vector.toList w)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sorted_take_lt_iff

Source: `RiffleLowerV2/Localization/RankBarriers.lean:143`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sorted_take_lt_iff : ∀ {k N K m : ℕ} {cuts : TimeProfile.Cuts k N K},
  m ≤ K →
    ∀ (w : RiffleLowerV2.Word k K) (omega : RiffleLowerV2.Sample cuts) (i : Fin N),
      ↑i < RiffleLowerV2.lowerRank (RiffleLowerV2.prefixAt m w) omega ↔
        List.take m (List.Vector.toList (RiffleLowerV2.sortedWord omega i)) < List.take m (List.Vector.toList w)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sum_massOn_eq_one

Source: `RiffleLowerV2/Localization/ProbabilityIntervals.lean:15`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sum_massOn_eq_one : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  0 < N → ∀ (I : Finset (Fin K)), ∑ x : RiffleLowerV2.WordOn k I, RiffleLowerV2.massOn cuts x = 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sum_sideMatch

Source: `RiffleLowerV2/Localization/Endpoints/Partitions.lean:22`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sum_sideMatch : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : LinearOrder α] [inst_2 : Fintype β]
  [inst_3 : DecidableEq β] (x y : α → β) (R : β → β → Prop),
  (∀ (d e : β), R d e → d ≠ e) →
    (∑ j : α, ∑ d : β with R d (x j), if RiffleLowerV2.Localization.sideMatch x y j d then 1 else 0) =
      if ∃ (j : α), R (y j) (x j) ∧ ∀ h < j, y h = x h then 1 else 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.sum_sideWeight_le_one

Source: `RiffleLowerV2/Localization/Endpoints/ProductWeights.lean:98`. Kind: theorem.

```lean
RiffleLowerV2.Localization.sum_sideWeight_le_one : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : LinearOrder α] [inst_2 : Fintype β] [DecidableEq β]
  (p : α → β → ℝ),
  (∀ (j : α), ∑ d : β, p j d = 1) →
    (∀ (j : α) (d : β), 0 ≤ p j d) →
      ∀ (x : α → β) (R : β → β → Prop),
        (∀ (d e : β), R d e → d ≠ e) →
          ∑ j : α, ∑ d : β with R d (x j), RiffleLowerV2.Localization.sideWeight p x j d ≤ 1
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.tail_grid_cost_sub

Source: `RiffleLowerV2/Localization/Geometry/Empirical.lean:67`. Kind: theorem.

```lean
RiffleLowerV2.Localization.tail_grid_cost_sub : ∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (mu bl : ℕ),
  RiffleLowerV2.J cuts hN 2 (RiffleLowerV2.gridTime N (mu + bl)) (RiffleLowerV2.horizon N K) =
      RiffleLowerV2.J cuts hN 2 (RiffleLowerV2.gridTime N mu) (RiffleLowerV2.horizon N K) -
        RiffleLowerV2.J cuts hN 2 (RiffleLowerV2.gridTime N mu) (RiffleLowerV2.gridTime N (mu + bl)) ∧
    RiffleLowerV2.H cuts hN 2 (RiffleLowerV2.gridTime N (mu + bl)) (RiffleLowerV2.horizon N K) =
      RiffleLowerV2.H cuts hN 2 (RiffleLowerV2.gridTime N mu) (RiffleLowerV2.horizon N K) -
        RiffleLowerV2.H cuts hN 2 (RiffleLowerV2.gridTime N mu) (RiffleLowerV2.gridTime N (mu + bl))
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.take_eq_map_finRange

Source: `RiffleLowerV2/Localization/RankBarriers.lean:13`. Kind: theorem.

```lean
RiffleLowerV2.Localization.take_eq_map_finRange : ∀ {k K m : ℕ} (hm : m ≤ K) (w : RiffleLowerV2.Word k K),
  List.take m (List.Vector.toList w) = List.map (fun (j : Fin m) => List.Vector.get w ⟨↑j, ⋯⟩) (List.finRange m)
```

Transitive axioms: `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.take_eq_take_iff

Source: `RiffleLowerV2/Localization/Endpoints/Coordinates.lean:10`. Kind: theorem.

```lean
RiffleLowerV2.Localization.take_eq_take_iff : ∀ {k K l : ℕ},
  l ≤ K →
    ∀ (v a : RiffleLowerV2.Word k K),
      List.take l (List.Vector.toList v) = List.take l (List.Vector.toList a) ↔
        ∀ (j : Fin K), ↑j < l → List.Vector.get v j = List.Vector.get a j
```

Transitive axioms: `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.take_le_split

Source: `RiffleLowerV2/Localization/RankBarriers.lean:68`. Kind: theorem.

```lean
RiffleLowerV2.Localization.take_le_split : ∀ {k K l m : ℕ},
  l ≤ m →
    m ≤ K →
      ∀ (v w : RiffleLowerV2.Word k K),
        List.take m (List.Vector.toList v) ≤ List.take m (List.Vector.toList w) ↔
          List.take l (List.Vector.toList v) < List.take l (List.Vector.toList w) ∨
            List.take l (List.Vector.toList v) = List.take l (List.Vector.toList w) ∧
              RiffleLowerV2.wordOnList (RiffleLowerV2.restrictWord (RiffleLowerV2.columnSet K l m) v) ≤
                RiffleLowerV2.wordOnList (RiffleLowerV2.restrictWord (RiffleLowerV2.columnSet K l m) w)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.take_lt_split

Source: `RiffleLowerV2/Localization/RankBarriers.lean:40`. Kind: theorem.

```lean
RiffleLowerV2.Localization.take_lt_split : ∀ {k K l m : ℕ},
  l ≤ m →
    m ≤ K →
      ∀ (v w : RiffleLowerV2.Word k K),
        List.take m (List.Vector.toList v) < List.take m (List.Vector.toList w) ↔
          List.take l (List.Vector.toList v) < List.take l (List.Vector.toList w) ∨
            List.take l (List.Vector.toList v) = List.take l (List.Vector.toList w) ∧
              RiffleLowerV2.wordOnList (RiffleLowerV2.restrictWord (RiffleLowerV2.columnSet K l m) v) <
                RiffleLowerV2.wordOnList (RiffleLowerV2.restrictWord (RiffleLowerV2.columnSet K l m) w)
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.take_lt_take_iff

Source: `RiffleLowerV2/Localization/RankBarriers.lean:23`. Kind: theorem.

```lean
RiffleLowerV2.Localization.take_lt_take_iff : ∀ {k K m : ℕ},
  m ≤ K →
    ∀ (v w : RiffleLowerV2.Word k K),
      List.take m (List.Vector.toList v) < List.take m (List.Vector.toList w) ↔
        ∃ (j : Fin K),
          ↑j < m ∧
            List.Vector.get v j < List.Vector.get w j ∧
              ∀ (h : Fin K), ↑h < ↑j → List.Vector.get v h = List.Vector.get w h
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.typeApproximation_grid

Source: `RiffleLowerV2/Localization/Geometry/Empirical.lean:28`. Kind: theorem.

```lean
RiffleLowerV2.Localization.typeApproximation_grid : ∀ {k N K : ℕ},
  2 ≤ N →
    ∀ (cuts : TimeProfile.Cuts k N K) (hN : 0 < N) (P : TimeProfile.BorelPartition k) {a b : ℕ},
      a ≤ b →
        ∀ (alpha err : ℝ) (D : RiffleLowerV2.RoundedTypeData P),
          RiffleLowerV2.TypeApproximation cuts hN P (RiffleLowerV2.columnSet K a b) alpha err D →
            |RiffleLowerV2.typeJ N D -
                    RiffleLowerV2.J cuts hN alpha (RiffleLowerV2.gridTime N a) (RiffleLowerV2.gridTime N b)| +
                |RiffleLowerV2.typeH cuts hN P (RiffleLowerV2.columnSet K a b) D -
                    RiffleLowerV2.H cuts hN alpha (RiffleLowerV2.gridTime N a) (RiffleLowerV2.gridTime N b)| ≤
              err
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.upperRank_prefixAt

Source: `RiffleLowerV2/Localization/RankBarriers.lean:101`. Kind: theorem.

```lean
RiffleLowerV2.Localization.upperRank_prefixAt : ∀ {k N K m : ℕ} {cuts : TimeProfile.Cuts k N K},
  m ≤ K →
    ∀ (w : RiffleLowerV2.Word k K) (omega : RiffleLowerV2.Sample cuts),
      RiffleLowerV2.upperRank (RiffleLowerV2.prefixAt m w) omega =
        {i : Fin N |
            List.take m (List.Vector.toList (RiffleLowerV2.rowWord omega i)) ≤ List.take m (List.Vector.toList w)}.card
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.weighted_side_partition

Source: `RiffleLowerV2/Localization/Endpoints/Partitions.lean:57`. Kind: theorem.

```lean
RiffleLowerV2.Localization.weighted_side_partition : ∀ {α : Type u_1} {β : Type u_2} {Ω : Type u_3} [inst : Fintype α] [inst_1 : LinearOrder α] [inst_2 : Fintype β]
  [inst_3 : DecidableEq β] [inst_4 : Fintype Ω] (x : α → β) (y : Ω → α → β) (A : Ω → Prop) (f : Ω → ℝ)
  (R : β → β → Prop),
  (∀ (d e : β), R d e → d ≠ e) →
    (∑ ω : Ω, if A ω ∧ ∃ (j : α), R (y ω j) (x j) ∧ ∀ h < j, y ω h = x h then f ω else 0) =
      ∑ j : α,
        ∑ d : β with R d (x j), ∑ ω : Ω, if A ω ∧ RiffleLowerV2.Localization.sideMatch x (y ω) j d then f ω else 0
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.wordOnList_injective

Source: `RiffleLowerV2/Localization/WordOrder.lean:50`. Kind: theorem.

```lean
RiffleLowerV2.Localization.wordOnList_injective : ∀ {k K : ℕ} {I : Finset (Fin K)}, Function.Injective RiffleLowerV2.wordOnList
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.wordOnList_lt_iff

Source: `RiffleLowerV2/Localization/WordOrder.lean:42`. Kind: theorem.

```lean
RiffleLowerV2.Localization.wordOnList_lt_iff : ∀ {k K : ℕ} {I : Finset (Fin K)} (x y : RiffleLowerV2.WordOn k I),
  RiffleLowerV2.wordOnList x < RiffleLowerV2.wordOnList y ↔ ∃ (j : ↥I), x j < y j ∧ ∀ h < j, x h = y h
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.

## RiffleLowerV2.Localization.wordOnList_lt_of_single_change

Source: `RiffleLowerV2/Localization/WordOrder.lean:58`. Kind: theorem.

```lean
RiffleLowerV2.Localization.wordOnList_lt_of_single_change : ∀ {k K : ℕ} {I : Finset (Fin K)} {x y : RiffleLowerV2.WordOn k I} (j : ↥I),
  x j < y j → (∀ (h : ↥I), h ≠ j → x h = y h) → RiffleLowerV2.wordOnList x < RiffleLowerV2.wordOnList y
```

Transitive axioms: `Classical.choice`, `Quot.sound`, `propext`.
