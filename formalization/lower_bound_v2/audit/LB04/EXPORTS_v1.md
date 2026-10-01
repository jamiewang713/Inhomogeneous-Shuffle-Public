# Exact checked LB04 exports v1

Every type below is read from the compiled Lean environment. The ten frozen targets are theorems; explicitly conditional intermediate helpers retain their displayed premises.

## RiffleLowerV2.Ascent.Separates

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean:11`.

```lean
RiffleLowerV2.Ascent.Separates : {N : ℕ} → Finset (Fin N) → Finset (Fin N) → RiffleLowerV2.Permutation N → Prop
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.ascentCount_eq_sum

theorem; source: `RiffleLowerV2/Ascent/UniformBaseline.lean:39`.

```lean
RiffleLowerV2.Ascent.ascentCount_eq_sum : ∀ {N : ℕ} (H : Finset (Fin N)) (π : RiffleLowerV2.Permutation N),
  ↑(RiffleLowerV2.ascentCount H π) =
    ∑ e ∈ RiffleLowerV2.internalEdges H, if π (RiffleLowerV2.edgeLeft e) < π (RiffleLowerV2.edgeRight e) then 1 else 0
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.badBoundaries

definition; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:22`.

```lean
RiffleLowerV2.Ascent.badBoundaries : {N : ℕ} → RiffleLowerV2.PathEdges N → Finset (Fin N) → RiffleLowerV2.PathEdges N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.badBoundaries_card_le

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:177`.

```lean
RiffleLowerV2.Ascent.badBoundaries_card_le : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  Finset.card (RiffleLowerV2.Ascent.badBoundaries G H) ≤ 2 * (RiffleLowerV2.boundary H).card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.badBoundaries_subset

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:38`.

```lean
RiffleLowerV2.Ascent.badBoundaries_subset : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  RiffleLowerV2.Ascent.badBoundaries G H ⊆ RiffleLowerV2.Ascent.retainedBoundaries G H
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.badLeftBoundaries

definition; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:16`.

```lean
RiffleLowerV2.Ascent.badLeftBoundaries : {N : ℕ} → RiffleLowerV2.PathEdges N → Finset (Fin N) → RiffleLowerV2.PathEdges N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.badLeftBoundaries_card_le_partial

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:151`.

```lean
RiffleLowerV2.Ascent.badLeftBoundaries_card_le_partial : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  Finset.card (RiffleLowerV2.Ascent.badLeftBoundaries G H) ≤ (RiffleLowerV2.Ascent.partialComponents G H).card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.badRightBoundaries

definition; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:19`.

```lean
RiffleLowerV2.Ascent.badRightBoundaries : {N : ℕ} → RiffleLowerV2.PathEdges N → Finset (Fin N) → RiffleLowerV2.PathEdges N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.badRightBoundaries_card_le_partial

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:164`.

```lean
RiffleLowerV2.Ascent.badRightBoundaries_card_le_partial : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  Finset.card (RiffleLowerV2.Ascent.badRightBoundaries G H) ≤ (RiffleLowerV2.Ascent.partialComponents G H).card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.bernoulliMGF

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:31`.

```lean
RiffleLowerV2.Ascent.bernoulliMGF : RiffleLowerV2.Targets.BernoulliMGF
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.bernoulli_mgf

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:12`.

```lean
RiffleLowerV2.Ascent.bernoulli_mgf : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop) (t : ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (t * ((if A ω then 1 else 0) - RiffleLowerV2.probability P A))) ≤
    Real.exp (t ^ 2 / 8)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.binomial_boundary_deficit_le

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:14`.

```lean
RiffleLowerV2.Ascent.binomial_boundary_deficit_le : ∀ (a b : ℕ), 1 ≤ a → 1 ≤ b → 1 / 2 - 1 / ↑((a + b).choose a) ≤ (↑(a - 1) + ↑(b - 1)) / 6
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.blockAction

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:96`.

```lean
RiffleLowerV2.Ascent.blockAction : {N : ℕ} →
  {I : Type u_1} →
    [Fintype I] →
      (A : I → Finset (Fin N)) →
        (∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) →
          ((i : I) → Equiv.Perm (Fin (A i).card)) → RiffleLowerV2.Permutation N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.blockAction_apply

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:113`.

```lean
RiffleLowerV2.Ascent.blockAction_apply : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] (A : I → Finset (Fin N)) (hA : ∀ (i j : I), i ≠ j → Disjoint (A i) (A j))
  (η : (i : I) → Equiv.Perm (Fin (A i).card)) (i : I) (x : Fin (A i).card),
  (RiffleLowerV2.Ascent.blockAction A hA η) ↑((RiffleLowerV2.Ascent.positionEnum (A i)) x) =
    ↑((RiffleLowerV2.Ascent.positionEnum (A i)) ((η i) x))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.blockAction_mem

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:118`.

```lean
RiffleLowerV2.Ascent.blockAction_mem : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] (A : I → Finset (Fin N)) (hA : ∀ (i j : I), i ≠ j → Disjoint (A i) (A j))
  (η : (i : I) → Equiv.Perm (Fin (A i).card)) (i : I) {x : Fin N},
  x ∈ A i → (RiffleLowerV2.Ascent.blockAction A hA η) x ∈ A i
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.blockAction_symm_mem

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:124`.

```lean
RiffleLowerV2.Ascent.blockAction_symm_mem : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] (A : I → Finset (Fin N)) (hA : ∀ (i j : I), i ≠ j → Disjoint (A i) (A j))
  (η : (i : I) → Equiv.Perm (Fin (A i).card)) (i : I) {x : Fin N},
  x ∈ A i → (Equiv.symm (RiffleLowerV2.Ascent.blockAction A hA η)) x ∈ A i
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.blockMap

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:63`.

```lean
RiffleLowerV2.Ascent.blockMap : {N : ℕ} →
  {I : Type u_1} → [Fintype I] → (A : I → Finset (Fin N)) → ((i : I) → Equiv.Perm (Fin (A i).card)) → Fin N → Fin N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.blockMap_apply

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:71`.

```lean
RiffleLowerV2.Ascent.blockMap_apply : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] (A : I → Finset (Fin N)),
  (∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (η : (i : I) → Equiv.Perm (Fin (A i).card)) (i : I) (x : Fin (A i).card),
      RiffleLowerV2.Ascent.blockMap A η ↑((RiffleLowerV2.Ascent.positionEnum (A i)) x) =
        ↑((RiffleLowerV2.Ascent.positionEnum (A i)) ((η i) x))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.blockMap_apply_of_mem

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:89`.

```lean
RiffleLowerV2.Ascent.blockMap_apply_of_mem : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] (A : I → Finset (Fin N)),
  (∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (η : (i : I) → Equiv.Perm (Fin (A i).card)) (i : I) (x : Fin N) (hx : x ∈ A i),
      RiffleLowerV2.Ascent.blockMap A η x =
        ↑((RiffleLowerV2.Ascent.positionEnum (A i)) ((η i) ((RiffleLowerV2.Ascent.positionEnum (A i)).symm ⟨x, hx⟩)))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundaryAscent

definition; source: `RiffleLowerV2/Ascent/Components.lean:31`.

```lean
RiffleLowerV2.Ascent.boundaryAscent : {N : ℕ} → RiffleLowerV2.PathEdges N → Fin (N - 1) → RiffleLowerV2.Permutation N → Prop
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundaryAscentProbability

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean:79`.

```lean
RiffleLowerV2.Ascent.boundaryAscentProbability : RiffleLowerV2.Targets.BoundaryAscentProbability
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundaryAscent_congr_relativeOrder

theorem; source: `RiffleLowerV2/Ascent/Components.lean:136`.

```lean
RiffleLowerV2.Ascent.boundaryAscent_congr_relativeOrder : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (e : Fin (N - 1)) (π τ : RiffleLowerV2.Permutation N),
  (∀ x ∈ RiffleLowerV2.Ascent.boundarySupport G e,
      ∀ y ∈ RiffleLowerV2.Ascent.boundarySupport G e, π x < π y ↔ τ x < τ y) →
    (RiffleLowerV2.Ascent.boundaryAscent G e π ↔ RiffleLowerV2.Ascent.boundaryAscent G e τ)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundaryParity

definition; source: `RiffleLowerV2/Ascent/Components.lean:28`.

```lean
RiffleLowerV2.Ascent.boundaryParity : {N : ℕ} → RiffleLowerV2.PathEdges N → Fin (N - 1) → ℕ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundarySupport

definition; source: `RiffleLowerV2/Ascent/Components.lean:25`.

```lean
RiffleLowerV2.Ascent.boundarySupport : {N : ℕ} → RiffleLowerV2.PathEdges N → Fin (N - 1) → Finset (Fin N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundarySupport_disjoint_sameParity

theorem; source: `RiffleLowerV2/Ascent/Components.lean:109`.

```lean
RiffleLowerV2.Ascent.boundarySupport_disjoint_sameParity : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) {e f : Fin (N - 1)},
  e ∉ G →
    f ∉ G →
      e ≠ f →
        RiffleLowerV2.Ascent.boundaryParity G e = RiffleLowerV2.Ascent.boundaryParity G f →
          Disjoint (RiffleLowerV2.Ascent.boundarySupport G e) (RiffleLowerV2.Ascent.boundarySupport G f)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundary_class_factorization

theorem; source: `RiffleLowerV2/Ascent/Concentration.lean:12`.

```lean
RiffleLowerV2.Ascent.boundary_class_factorization : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (s : Finset (Fin (N - 1))),
  (∀ e ∈ s, e ∉ G) →
    (∀ e ∈ s, ∀ f ∈ s, RiffleLowerV2.Ascent.boundaryParity G e = RiffleLowerV2.Ascent.boundaryParity G f) →
      ∀ (u : ℝ),
        (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
            ∏ e ∈ s,
              Real.exp
                (u *
                  ((if RiffleLowerV2.Ascent.boundaryAscent G e π then 1 else 0) -
                    RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N)
                      (RiffleLowerV2.Ascent.boundaryAscent G e)))) =
          ∏ e ∈ s,
            RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
              Real.exp
                (u *
                  ((if RiffleLowerV2.Ascent.boundaryAscent G e π then 1 else 0) -
                    RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N)
                      (RiffleLowerV2.Ascent.boundaryAscent G e)))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundary_index_strict

theorem; source: `RiffleLowerV2/Ascent/Components.lean:99`.

```lean
RiffleLowerV2.Ascent.boundary_index_strict : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) {e f : Fin (N - 1)},
  e ∉ G →
    e < f →
      RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e) <
        RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft f)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundary_left_index_injective

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:135`.

```lean
RiffleLowerV2.Ascent.boundary_left_index_injective : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  Set.InjOn (fun (e : Fin (N - 1)) => RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e))
    {e : Fin (N - 1) | e ∉ G}
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.boundary_right_index_injective

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:143`.

```lean
RiffleLowerV2.Ascent.boundary_right_index_injective : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  Set.InjOn (fun (e : Fin (N - 1)) => RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeRight e))
    {e : Fin (N - 1) | e ∉ G}
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.chosenTranslate

definition; source: `RiffleLowerV2/Ascent/Selection.lean:14`.

```lean
RiffleLowerV2.Ascent.chosenTranslate : {N : ℕ} → Finset ℤ → RiffleLowerV2.PathEdges N → ℝ → Fin (N + 1)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.chosenTranslate_measurable

theorem; source: `RiffleLowerV2/Ascent/Selection.lean:49`.

```lean
RiffleLowerV2.Ascent.chosenTranslate_measurable : ∀ {N : ℕ} (H0 : Finset ℤ) (r : ℝ) [inst : MeasurableSpace (RiffleLowerV2.PathEdges N)]
  [MeasurableSingletonClass (RiffleLowerV2.PathEdges N)] [inst_2 : MeasurableSpace (Fin (N + 1))],
  Measurable fun (G : RiffleLowerV2.PathEdges N) => RiffleLowerV2.Ascent.chosenTranslate H0 G r
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.chosenTranslate_spec

theorem; source: `RiffleLowerV2/Ascent/Selection.lean:24`.

```lean
RiffleLowerV2.Ascent.chosenTranslate_spec : ∀ {N : ℕ} (H0 : Finset ℤ) (G : RiffleLowerV2.PathEdges N) (r : ℝ),
  (∃ (q : Fin (N + 1)), r ≤ ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q)))) →
    r ≤
        ↑(Finset.card
            (G ∩
              RiffleLowerV2.internalEdges
                (RiffleLowerV2.clipTranslate N H0 ↑↑(RiffleLowerV2.Ascent.chosenTranslate H0 G r)))) ∧
      ∀ q' < RiffleLowerV2.Ascent.chosenTranslate H0 G r,
        ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q'))) < r
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentComparison

theorem; source: `RiffleLowerV2/Ascent/Test.lean:12`.

```lean
RiffleLowerV2.Ascent.componentComparison : RiffleLowerV2.Targets.ComponentComparison
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentComparison_of_concentration_expectation

theorem; source: `RiffleLowerV2/Ascent/FiniteConsequences.lean:32`.

```lean
RiffleLowerV2.Ascent.componentComparison_of_concentration_expectation : RiffleLowerV2.Targets.ComponentConcentration →
  RiffleLowerV2.Targets.ComponentExpectation → RiffleLowerV2.Targets.ComponentComparison
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentConcentration

theorem; source: `RiffleLowerV2/Ascent/Concentration.lean:45`.

```lean
RiffleLowerV2.Ascent.componentConcentration : RiffleLowerV2.Targets.ComponentConcentration
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentConcentrationTwoSided

theorem; source: `RiffleLowerV2/Ascent/Concentration.lean:86`.

```lean
RiffleLowerV2.Ascent.componentConcentrationTwoSided : RiffleLowerV2.Targets.ComponentConcentrationTwoSided
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentConcentrationTwoSided_of_concentration

theorem; source: `RiffleLowerV2/Ascent/FiniteConsequences.lean:44`.

```lean
RiffleLowerV2.Ascent.componentConcentrationTwoSided_of_concentration : RiffleLowerV2.Targets.ComponentConcentration → RiffleLowerV2.Targets.ComponentConcentrationTwoSided
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentEdges

definition; source: `RiffleLowerV2/Ascent/Components/Charging.lean:10`.

```lean
RiffleLowerV2.Ascent.componentEdges : {N : ℕ} → RiffleLowerV2.PathEdges N → ℕ → RiffleLowerV2.PathEdges N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentEdges_disjoint

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:59`.

```lean
RiffleLowerV2.Ascent.componentEdges_disjoint : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) {i j : ℕ},
  i ≠ j → Disjoint (RiffleLowerV2.Ascent.componentEdges G i) (RiffleLowerV2.Ascent.componentEdges G j)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentEdges_endpoints

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:17`.

```lean
RiffleLowerV2.Ascent.componentEdges_endpoints : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (j : ℕ),
  ∀ e ∈ RiffleLowerV2.Ascent.componentEdges G j,
    RiffleLowerV2.edgeLeft e ∈ RiffleLowerV2.Ascent.componentSet G j ∧
      RiffleLowerV2.edgeRight e ∈ RiffleLowerV2.Ascent.componentSet G j
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentEdges_subset_retainedInternal

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:66`.

```lean
RiffleLowerV2.Ascent.componentEdges_subset_retainedInternal : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) (j : ℕ),
  RiffleLowerV2.Ascent.componentSet G j ⊆ H →
    RiffleLowerV2.Ascent.componentEdges G j ⊆ G ∩ RiffleLowerV2.internalEdges H
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentExpectation

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:120`.

```lean
RiffleLowerV2.Ascent.componentExpectation : RiffleLowerV2.Targets.ComponentExpectation
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentIndex_edge_missing

theorem; source: `RiffleLowerV2/Ascent/Components.lean:66`.

```lean
RiffleLowerV2.Ascent.componentIndex_edge_missing : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G,
    RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeRight e) =
      RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e) + 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentIndex_edge_present

theorem; source: `RiffleLowerV2/Ascent/Components.lean:48`.

```lean
RiffleLowerV2.Ascent.componentIndex_edge_present : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∈ G,
    RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeRight e) =
      RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentIndex_empty_injective

theorem; source: `RiffleLowerV2/Ascent/Components.lean:254`.

```lean
RiffleLowerV2.Ascent.componentIndex_empty_injective : ∀ {N : ℕ}, Function.Injective (RiffleLowerV2.componentIndex ∅)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentIndex_eq_between

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:28`.

```lean
RiffleLowerV2.Ascent.componentIndex_eq_between : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) {i j k : Fin N},
  i ≤ j →
    j ≤ k →
      RiffleLowerV2.componentIndex G i = RiffleLowerV2.componentIndex G k →
        RiffleLowerV2.componentIndex G j = RiffleLowerV2.componentIndex G i
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentIndex_le

theorem; source: `RiffleLowerV2/Ascent/Components.lean:41`.

```lean
RiffleLowerV2.Ascent.componentIndex_le : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) {i j : Fin N},
  i ≤ j → RiffleLowerV2.componentIndex G i ≤ RiffleLowerV2.componentIndex G j
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentSet

definition; source: `RiffleLowerV2/Ascent/Components.lean:13`.

```lean
RiffleLowerV2.Ascent.componentSet : {N : ℕ} → RiffleLowerV2.PathEdges N → ℕ → Finset (Fin N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentSet_card

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:24`.

```lean
RiffleLowerV2.Ascent.componentSet_card : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (j : ℕ),
  (RiffleLowerV2.Ascent.componentSet G j).Nonempty →
    (RiffleLowerV2.Ascent.componentSet G j).card = Finset.card (RiffleLowerV2.Ascent.componentEdges G j) + 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentSet_disjoint

theorem; source: `RiffleLowerV2/Ascent/Components.lean:87`.

```lean
RiffleLowerV2.Ascent.componentSet_disjoint : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) {a b : ℕ},
  a ≠ b → Disjoint (RiffleLowerV2.Ascent.componentSet G a) (RiffleLowerV2.Ascent.componentSet G b)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentSort_boundary_ascent_iff

theorem; source: `RiffleLowerV2/Ascent/Components.lean:211`.

```lean
RiffleLowerV2.Ascent.componentSort_boundary_ascent_iff : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G,
    ∀ (π : RiffleLowerV2.Permutation N),
      (RiffleLowerV2.componentSort G π) (RiffleLowerV2.edgeLeft e) <
          (RiffleLowerV2.componentSort G π) (RiffleLowerV2.edgeRight e) ↔
        RiffleLowerV2.Ascent.boundaryAscent G e π
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentSort_empty

theorem; source: `RiffleLowerV2/Ascent/Components.lean:271`.

```lean
RiffleLowerV2.Ascent.componentSort_empty : ∀ {N : ℕ} (π : RiffleLowerV2.Permutation N), RiffleLowerV2.componentSort ∅ π = π
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.componentSort_internal_ascent

theorem; source: `RiffleLowerV2/Ascent/Components.lean:226`.

```lean
RiffleLowerV2.Ascent.componentSort_internal_ascent : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∈ G,
    ∀ (π : RiffleLowerV2.Permutation N),
      (RiffleLowerV2.componentSort G π) (RiffleLowerV2.edgeLeft e) <
        (RiffleLowerV2.componentSort G π) (RiffleLowerV2.edgeRight e)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.component_ascent_decomposition

theorem; source: `RiffleLowerV2/Ascent/Components.lean:232`.

```lean
RiffleLowerV2.Ascent.component_ascent_decomposition : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) (π : RiffleLowerV2.Permutation N),
  RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π) =
    Finset.card (G ∩ RiffleLowerV2.internalEdges H) +
      ∑ e ∈ RiffleLowerV2.Ascent.retainedBoundaries G H, if RiffleLowerV2.Ascent.boundaryAscent G e π then 1 else 0
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.component_expectation_eq

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:25`.

```lean
RiffleLowerV2.Ascent.component_expectation_eq : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
      ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π))) =
    ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges H)) +
      ∑ e ∈ RiffleLowerV2.Ascent.retainedBoundaries G H,
        RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) (RiffleLowerV2.Ascent.boundaryAscent G e)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.component_expectation_lower_of_boundary_probability

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:72`.

```lean
RiffleLowerV2.Ascent.component_expectation_lower_of_boundary_probability : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  (∀ e ∉ G,
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) (RiffleLowerV2.Ascent.boundaryAscent G e) =
        1 /
          ↑(((RiffleLowerV2.Ascent.leftComponent G e).card + (RiffleLowerV2.Ascent.rightComponent G e).card).choose
              (RiffleLowerV2.Ascent.leftComponent G e).card)) →
    (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π))) ≥
      ↑(Finset.card (RiffleLowerV2.internalEdges H)) / 2 + ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges H)) / 6 -
        ↑(RiffleLowerV2.boundary H).card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.conditionalLalleyTendsto

theorem; source: `RiffleLowerV2/Ascent/Test.lean:48`.

```lean
RiffleLowerV2.Ascent.conditionalLalleyTendsto : ∀ (a δ D : ℝ),
  0 < a →
    0 < δ →
      0 ≤ D →
        ∀ (H0 : ℕ → Finset ℤ) (ρ : (N : ℕ) → PMF (RiffleLowerV2.PathEdges N))
          (P : (N : ℕ) → PMF (RiffleLowerV2.Permutation N)),
          (∀ (N : ℕ), P N = RiffleLowerV2.Ascent.pathGraphMixture (ρ N)) →
            (∀ᶠ (N : ℕ) in Filter.atTop,
                ↑N ^ a ≤ ↑(H0 N).card ∧
                  ∀ (q : Fin (N + 1)),
                    ↑(RiffleLowerV2.boundary (RiffleLowerV2.clipTranslate N (H0 N) ↑↑q)).card ≤ D * √↑(H0 N).card) →
              Filter.Tendsto
                  (fun (N : ℕ) => RiffleLowerV2.probability (ρ N) (RiffleLowerV2.Ascent.graphScanSuccess (H0 N) δ))
                  Filter.atTop (nhds 1) →
                Filter.Tendsto (fun (N : ℕ) => RiffleLowerV2.tv (P N) (RiffleLowerV2.uniformPermutation N)) Filter.atTop
                  (nhds 1)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.conditionalLalleyTest

theorem; source: `RiffleLowerV2/Ascent/Test.lean:24`.

```lean
RiffleLowerV2.Ascent.conditionalLalleyTest : ∀ (a δ D ε : ℝ),
  0 < a →
    0 < δ →
      0 ≤ D →
        0 < ε →
          ∃ (N0 : ℕ),
            1 ≤ N0 ∧
              ∀ N ≥ N0,
                ∀ (H0 : Finset ℤ) (ρ : PMF (RiffleLowerV2.PathEdges N)) (P : PMF (RiffleLowerV2.Permutation N)),
                  P = RiffleLowerV2.Ascent.pathGraphMixture ρ →
                    ↑N ^ a ≤ ↑H0.card →
                      (∀ (q : Fin (N + 1)),
                          ↑(RiffleLowerV2.boundary (RiffleLowerV2.clipTranslate N H0 ↑↑q)).card ≤ D * √↑H0.card) →
                        RiffleLowerV2.probability ρ (RiffleLowerV2.Ascent.graphScanSuccess H0 δ) - ε ≤
                          RiffleLowerV2.tv P (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.crossingEdges

definition; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:10`.

```lean
RiffleLowerV2.Ascent.crossingEdges : {N : ℕ} → RiffleLowerV2.PathEdges N → Finset (Fin N) → RiffleLowerV2.PathEdges N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.crossingEdges_card_le_boundary

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:90`.

```lean
RiffleLowerV2.Ascent.crossingEdges_card_le_boundary : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  Finset.card (RiffleLowerV2.Ascent.crossingEdges G H) ≤ (RiffleLowerV2.boundary H).card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.edge_mem_of_same_component

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:35`.

```lean
RiffleLowerV2.Ascent.edge_mem_of_same_component : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) {i j : Fin N} (e : Fin (N - 1)),
  i ≤ RiffleLowerV2.edgeLeft e →
    RiffleLowerV2.edgeRight e ≤ j → RiffleLowerV2.componentIndex G i = RiffleLowerV2.componentIndex G j → e ∈ G
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.endpoint_le_rightComponent

theorem; source: `RiffleLowerV2/Ascent/Components.lean:160`.

```lean
RiffleLowerV2.Ascent.endpoint_le_rightComponent : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G, ∀ {i : Fin N}, i ∈ RiffleLowerV2.Ascent.rightComponent G e → RiffleLowerV2.edgeRight e ≤ i
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.exists_crossing_of_same_component

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:44`.

```lean
RiffleLowerV2.Ascent.exists_crossing_of_same_component : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) {i j : Fin N},
  RiffleLowerV2.componentIndex G i = RiffleLowerV2.componentIndex G j →
    ¬(i ∈ H ↔ j ∈ H) →
      ∃ e ∈ RiffleLowerV2.Ascent.crossingEdges G H,
        RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e) = RiffleLowerV2.componentIndex G i
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.exists_separates

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean:14`.

```lean
RiffleLowerV2.Ascent.exists_separates : ∀ {N : ℕ} (A B : Finset (Fin N)),
  Disjoint A B → ∃ (τ : RiffleLowerV2.Permutation N), RiffleLowerV2.Ascent.Separates A B τ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.exp_markov

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:70`.

```lean
RiffleLowerV2.Ascent.exp_markov : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (X : Ω → ℝ) {u t : ℝ},
  0 < u →
    (RiffleLowerV2.probability P fun (ω : Ω) => t ≤ X ω) ≤
      Real.exp (-u * t) * RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (u * X ω)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_add

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:40`.

```lean
RiffleLowerV2.Ascent.expect_add : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (f g : Ω → ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => f ω + g ω) = RiffleLowerV2.expect P f + RiffleLowerV2.expect P g
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_ascentCount_uniform

theorem; source: `RiffleLowerV2/Ascent/UniformBaseline.lean:45`.

```lean
RiffleLowerV2.Ascent.expect_ascentCount_uniform : ∀ {N : ℕ} (H : Finset (Fin N)),
  (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
      ↑(RiffleLowerV2.ascentCount H π)) =
    ↑(Finset.card (RiffleLowerV2.internalEdges H)) / 2
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_const

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:24`.

```lean
RiffleLowerV2.Ascent.expect_const : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (c : ℝ), (RiffleLowerV2.expect P fun (x : Ω) => c) = c
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_const_mul

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:33`.

```lean
RiffleLowerV2.Ascent.expect_const_mul : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (c : ℝ) (f : Ω → ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => c * f ω) = c * RiffleLowerV2.expect P f
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_indicator

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:132`.

```lean
RiffleLowerV2.Ascent.expect_indicator : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop) [inst_1 : DecidablePred A],
  (RiffleLowerV2.expect P fun (ω : Ω) => if A ω then 1 else 0) = RiffleLowerV2.probability P A
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_mono

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:16`.

```lean
RiffleLowerV2.Ascent.expect_mono : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) {f g : Ω → ℝ},
  (∀ (ω : Ω), f ω ≤ g ω) → RiffleLowerV2.expect P f ≤ RiffleLowerV2.expect P g
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_mul_sq_le

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:61`.

```lean
RiffleLowerV2.Ascent.expect_mul_sq_le : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (f g : Ω → ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => f ω * g ω) ^ 2 ≤
    (RiffleLowerV2.expect P fun (ω : Ω) => f ω ^ 2) * RiffleLowerV2.expect P fun (ω : Ω) => g ω ^ 2
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_nonneg

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:20`.

```lean
RiffleLowerV2.Ascent.expect_nonneg : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) {f : Ω → ℝ}, (∀ (ω : Ω), 0 ≤ f ω) → 0 ≤ RiffleLowerV2.expect P f
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_prod_of_relativeOrder

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:106`.

```lean
RiffleLowerV2.Ascent.expect_prod_of_relativeOrder : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] [DecidableEq I] (A : I → Finset (Fin N)),
  (∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (f : I → RiffleLowerV2.Permutation N → ℝ),
      (∀ (i : I) (π σ : RiffleLowerV2.Permutation N), (∀ x ∈ A i, ∀ y ∈ A i, π x < π y ↔ σ x < σ y) → f i π = f i σ) →
        (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
            ∏ i : I, f i π) =
          ∏ i : I, RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) (f i)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_sub

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:44`.

```lean
RiffleLowerV2.Ascent.expect_sub : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (f g : Ω → ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => f ω - g ω) = RiffleLowerV2.expect P f - RiffleLowerV2.expect P g
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_sum

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:48`.

```lean
RiffleLowerV2.Ascent.expect_sum : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) {I : Type u_3} (s : Finset I) (f : I → Ω → ℝ),
  (RiffleLowerV2.expect P fun (ω : Ω) => ∑ i ∈ s, f i ω) = ∑ i ∈ s, RiffleLowerV2.expect P (f i)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.expect_uniform

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:120`.

```lean
RiffleLowerV2.Ascent.expect_uniform : ∀ {Ω : Type u_1} [inst : Fintype Ω] [inst_1 : Nonempty Ω] (f : Ω → ℝ),
  RiffleLowerV2.expect (PMF.uniformOfFintype Ω) f = (∑ ω : Ω, f ω) / ↑(Fintype.card Ω)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.failure_envelope_tendsto_zero

theorem; source: `RiffleLowerV2/Ascent/Asymptotic.lean:40`.

```lean
RiffleLowerV2.Ascent.failure_envelope_tendsto_zero : ∀ {a δ : ℝ}, 0 < a → 0 < δ → Filter.Tendsto (fun (N : ℕ) => Real.exp (-↑N ^ (a * (2 * δ)) / 144)) Filter.atTop (nhds 0)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.goodBoundaries

definition; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:25`.

```lean
RiffleLowerV2.Ascent.goodBoundaries : {N : ℕ} → RiffleLowerV2.PathEdges N → Finset (Fin N) → RiffleLowerV2.PathEdges N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.good_bad_disjoint

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:45`.

```lean
RiffleLowerV2.Ascent.good_bad_disjoint : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  Disjoint (RiffleLowerV2.Ascent.goodBoundaries G H) (RiffleLowerV2.Ascent.badBoundaries G H)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.good_bad_union

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:51`.

```lean
RiffleLowerV2.Ascent.good_bad_union : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  RiffleLowerV2.Ascent.goodBoundaries G H ∪ RiffleLowerV2.Ascent.badBoundaries G H =
    RiffleLowerV2.Ascent.retainedBoundaries G H
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.good_boundary_double_charge

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:116`.

```lean
RiffleLowerV2.Ascent.good_boundary_double_charge : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  ∑ e ∈ RiffleLowerV2.Ascent.goodBoundaries G H,
      ((RiffleLowerV2.Ascent.leftComponent G e).card - 1 + ((RiffleLowerV2.Ascent.rightComponent G e).card - 1)) ≤
    2 * Finset.card (G ∩ RiffleLowerV2.internalEdges H)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.good_left_charge_le

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:80`.

```lean
RiffleLowerV2.Ascent.good_left_charge_le : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  ∑ e ∈ RiffleLowerV2.Ascent.goodBoundaries G H,
      Finset.card (RiffleLowerV2.Ascent.componentEdges G (RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e))) ≤
    Finset.card (G ∩ RiffleLowerV2.internalEdges H)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.good_right_charge_le

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:98`.

```lean
RiffleLowerV2.Ascent.good_right_charge_le : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  ∑ e ∈ RiffleLowerV2.Ascent.goodBoundaries G H,
      Finset.card (RiffleLowerV2.Ascent.componentEdges G (RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeRight e))) ≤
    Finset.card (G ∩ RiffleLowerV2.internalEdges H)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.graphScanSuccess

definition; source: `RiffleLowerV2/Ascent/Test.lean:19`.

```lean
RiffleLowerV2.Ascent.graphScanSuccess : {N : ℕ} → Finset ℤ → ℝ → RiffleLowerV2.PathEdges N → Prop
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.graph_mixture_event_lower

theorem; source: `RiffleLowerV2/Ascent/Mixture.lean:27`.

```lean
RiffleLowerV2.Ascent.graph_mixture_event_lower : ∀ {N : ℕ} (ρ : PMF (RiffleLowerV2.PathEdges N)) (good : RiffleLowerV2.PathEdges N → Prop)
  (A : RiffleLowerV2.Permutation N → Prop) {ε : ℝ},
  0 ≤ ε →
    (∀ (G : RiffleLowerV2.PathEdges N),
        good G →
          1 - ε ≤
            RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
              A (RiffleLowerV2.componentSort G π)) →
      RiffleLowerV2.probability ρ good - ε ≤ RiffleLowerV2.probability (RiffleLowerV2.Ascent.pathGraphMixture ρ) A
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.graph_mixture_tv_lower

theorem; source: `RiffleLowerV2/Ascent/Mixture.lean:81`.

```lean
RiffleLowerV2.Ascent.graph_mixture_tv_lower : ∀ {N : ℕ} (ρ : PMF (RiffleLowerV2.PathEdges N)) (P : PMF (RiffleLowerV2.Permutation N)),
  P = RiffleLowerV2.Ascent.pathGraphMixture ρ →
    ∀ (good : RiffleLowerV2.PathEdges N → Prop) (A : RiffleLowerV2.Permutation N → Prop) {ε η : ℝ},
      0 ≤ ε →
        (∀ (G : RiffleLowerV2.PathEdges N),
            good G →
              1 - ε ≤
                RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
                  A (RiffleLowerV2.componentSort G π)) →
          RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) A ≤ η →
            RiffleLowerV2.probability ρ good - ε - η ≤ RiffleLowerV2.tv P (RiffleLowerV2.uniformPermutation N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.graph_scan_ge_of_comparison

theorem; source: `RiffleLowerV2/Ascent/Asymptotic.lean:11`.

```lean
RiffleLowerV2.Ascent.graph_scan_ge_of_comparison : RiffleLowerV2.Targets.ComponentComparison →
  ∀ {N : ℕ} (H0 : Finset ℤ) (G : RiffleLowerV2.PathEdges N) {D δ : ℝ},
    0 < ↑H0.card →
      576 ≤ ↑H0.card ^ δ →
        24 * D ≤ ↑H0.card ^ δ →
          (∀ (q : Fin (N + 1)), ↑(RiffleLowerV2.boundary (RiffleLowerV2.clipTranslate N H0 ↑↑q)).card ≤ D * √↑H0.card) →
            (∃ (q : Fin (N + 1)),
                ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q))) ≥
                  ↑H0.card ^ (1 / 2 + δ)) →
              1 - Real.exp (-↑H0.card ^ (2 * δ) / 144) ≤
                RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
                  RiffleLowerV2.scan H0 (↑H0.card ^ (1 / 2 + δ / 2)) (RiffleLowerV2.componentSort G π)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.lalley_gap

theorem; source: `RiffleLowerV2/Ascent/Quantitative.lean:10`.

```lean
RiffleLowerV2.Ascent.lalley_gap : ∀ {M D δ r d : ℝ},
  0 < M →
    576 ≤ M ^ δ →
      24 * D ≤ M ^ δ → M ^ (1 / 2 + δ) ≤ r → d ≤ D * √M → M ^ (1 / 2 + δ) / 12 ≤ r / 6 - d - M ^ (1 / 2 + δ / 2)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.lalley_gap_square

theorem; source: `RiffleLowerV2/Ascent/Quantitative.lean:31`.

```lean
RiffleLowerV2.Ascent.lalley_gap_square : ∀ {M δ : ℝ}, 0 < M → (M ^ (1 / 2 + δ) / 12) ^ 2 / M = M ^ (2 * δ) / 144
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.leastSuccessfulTranslate

theorem; source: `RiffleLowerV2/Ascent/Selection.lean:44`.

```lean
RiffleLowerV2.Ascent.leastSuccessfulTranslate : RiffleLowerV2.Targets.LeastSuccessfulTranslate
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.leftComponent

definition; source: `RiffleLowerV2/Ascent/Components.lean:19`.

```lean
RiffleLowerV2.Ascent.leftComponent : {N : ℕ} → RiffleLowerV2.PathEdges N → Fin (N - 1) → Finset (Fin N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.leftComponent_le_endpoint

theorem; source: `RiffleLowerV2/Ascent/Components.lean:147`.

```lean
RiffleLowerV2.Ascent.leftComponent_le_endpoint : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G, ∀ {i : Fin N}, i ∈ RiffleLowerV2.Ascent.leftComponent G e → i ≤ RiffleLowerV2.edgeLeft e
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.leftPositionAction

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:21`.

```lean
RiffleLowerV2.Ascent.leftPositionAction : {N : ℕ} → RiffleLowerV2.Permutation N → RiffleLowerV2.Permutation N ≃ RiffleLowerV2.Permutation N
```

Axiom closure: propext, Quot.sound.

## RiffleLowerV2.Ascent.left_right_disjoint

theorem; source: `RiffleLowerV2/Ascent/Components.lean:93`.

```lean
RiffleLowerV2.Ascent.left_right_disjoint : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G, Disjoint (RiffleLowerV2.Ascent.leftComponent G e) (RiffleLowerV2.Ascent.rightComponent G e)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.markov

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:112`.

```lean
RiffleLowerV2.Ascent.markov : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) {f : Ω → ℝ},
  (∀ (ω : Ω), 0 ≤ f ω) →
    ∀ {t : ℝ}, 0 < t → (RiffleLowerV2.probability P fun (ω : Ω) => t ≤ f ω) ≤ RiffleLowerV2.expect P f / t
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.mem_componentEdges

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:13`.

```lean
RiffleLowerV2.Ascent.mem_componentEdges : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (j : ℕ) (e : Fin (N - 1)),
  e ∈ RiffleLowerV2.Ascent.componentEdges G j ↔ e ∈ G ∧ RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e) = j
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.mem_componentSet

theorem; source: `RiffleLowerV2/Ascent/Components.lean:34`.

```lean
RiffleLowerV2.Ascent.mem_componentSet : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (j : ℕ) (i : Fin N),
  i ∈ RiffleLowerV2.Ascent.componentSet G j ↔ RiffleLowerV2.componentIndex G i = j
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.mem_goodBoundaries

theorem; source: `RiffleLowerV2/Ascent/Components/Charging.lean:73`.

```lean
RiffleLowerV2.Ascent.mem_goodBoundaries : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) (e : Fin (N - 1)),
  e ∈ RiffleLowerV2.Ascent.goodBoundaries G H ↔
    e ∈ RiffleLowerV2.Ascent.retainedBoundaries G H ∧
      RiffleLowerV2.Ascent.leftComponent G e ⊆ H ∧ RiffleLowerV2.Ascent.rightComponent G e ⊆ H
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.mem_retainedBoundaries

theorem; source: `RiffleLowerV2/Ascent/Components.lean:37`.

```lean
RiffleLowerV2.Ascent.mem_retainedBoundaries : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) (e : Fin (N - 1)),
  e ∈ RiffleLowerV2.Ascent.retainedBoundaries G H ↔ e ∈ RiffleLowerV2.internalEdges H ∧ e ∉ G
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.mem_successfulTranslates

theorem; source: `RiffleLowerV2/Ascent/Selection.lean:18`.

```lean
RiffleLowerV2.Ascent.mem_successfulTranslates : ∀ {N : ℕ} (H0 : Finset ℤ) (G : RiffleLowerV2.PathEdges N) (r : ℝ) (q : Fin (N + 1)),
  q ∈ RiffleLowerV2.Ascent.successfulTranslates H0 G r ↔
    r ≤ ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges (RiffleLowerV2.clipTranslate N H0 ↑↑q)))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.null_scan_envelope_tendsto_zero

theorem; source: `RiffleLowerV2/Ascent/Asymptotic.lean:98`.

```lean
RiffleLowerV2.Ascent.null_scan_envelope_tendsto_zero : ∀ {β : ℝ}, 0 < β → Filter.Tendsto (fun (N : ℕ) => (↑N + 1) * Real.exp (-↑N ^ β)) Filter.atTop (nhds 0)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.one_class_mgf

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:37`.

```lean
RiffleLowerV2.Ascent.one_class_mgf : ∀ {Ω : Type u_1} [inst : Fintype Ω] {I : Type u_2} (P : PMF Ω) (s : Finset I) (A : I → Ω → Prop),
  (∀ (u : ℝ),
      (RiffleLowerV2.expect P fun (ω : Ω) =>
          ∏ i ∈ s, Real.exp (u * ((if A i ω then 1 else 0) - RiffleLowerV2.probability P (A i)))) =
        ∏ i ∈ s,
          RiffleLowerV2.expect P fun (ω : Ω) =>
            Real.exp (u * ((if A i ω then 1 else 0) - RiffleLowerV2.probability P (A i)))) →
    ∀ (u : ℝ),
      (RiffleLowerV2.expect P fun (ω : Ω) =>
          Real.exp (u * ∑ i ∈ s, ((if A i ω then 1 else 0) - RiffleLowerV2.probability P (A i)))) ≤
        Real.exp (u ^ 2 * ↑s.card / 8)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.orderTransform

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:14`.

```lean
RiffleLowerV2.Ascent.orderTransform : {n : ℕ} → Equiv.Perm (Fin n) → Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n)
```

Axiom closure: propext, Quot.sound.

## RiffleLowerV2.Ascent.pairSets

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean:50`.

```lean
RiffleLowerV2.Ascent.pairSets : {N : ℕ} → Finset (Fin N) → Finset (Fin N) → Bool → Finset (Fin N)
```

Axiom closure: propext, Quot.sound.

## RiffleLowerV2.Ascent.pairSets_disjoint

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean:53`.

```lean
RiffleLowerV2.Ascent.pairSets_disjoint : ∀ {N : ℕ} (A B : Finset (Fin N)),
  Disjoint A B →
    ∀ (i j : Bool), i ≠ j → Disjoint (RiffleLowerV2.Ascent.pairSets A B i) (RiffleLowerV2.Ascent.pairSets A B j)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.parity_mgf

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:89`.

```lean
RiffleLowerV2.Ascent.parity_mgf : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (S₀ S₁ : Ω → ℝ) (B₀ B₁ : ℝ),
  (∀ (u : ℝ), (RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (u * S₀ ω)) ≤ Real.exp (u ^ 2 * B₀ / 8)) →
    (∀ (u : ℝ), (RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (u * S₁ ω)) ≤ Real.exp (u ^ 2 * B₁ / 8)) →
      ∀ (u : ℝ), (RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (u * (S₀ ω + S₁ ω))) ≤ Real.exp (u ^ 2 * (B₀ + B₁) / 4)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.partialComponents

definition; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:13`.

```lean
RiffleLowerV2.Ascent.partialComponents : {N : ℕ} → RiffleLowerV2.PathEdges N → Finset (Fin N) → Finset ℕ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.partialComponents_card_le_boundary

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:130`.

```lean
RiffleLowerV2.Ascent.partialComponents_card_le_boundary : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  (RiffleLowerV2.Ascent.partialComponents G H).card ≤ (RiffleLowerV2.boundary H).card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.partialComponents_subset_crossingImage

theorem; source: `RiffleLowerV2/Ascent/Components/Clipping.lean:78`.

```lean
RiffleLowerV2.Ascent.partialComponents_subset_crossingImage : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  RiffleLowerV2.Ascent.partialComponents G H ⊆
    Finset.image (fun (e : Fin (N - 1)) => RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e))
      (RiffleLowerV2.Ascent.crossingEdges G H)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.pathGraphMixture

definition; source: `RiffleLowerV2/Ascent/Mixture.lean:13`.

```lean
RiffleLowerV2.Ascent.pathGraphMixture : {N : ℕ} → PMF (RiffleLowerV2.PathEdges N) → PMF (RiffleLowerV2.Permutation N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.positionEnum

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:13`.

```lean
RiffleLowerV2.Ascent.positionEnum : {N : ℕ} → (A : Finset (Fin N)) → Fin A.card ≃ ↥A
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_and_relativeOrder

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Weighted.lean:74`.

```lean
RiffleLowerV2.Ascent.probability_and_relativeOrder : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] [DecidableEq I] (A : I → Finset (Fin N))
  (hA : ∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) (S : RiffleLowerV2.Permutation N → Prop),
  (∀ (η : (i : I) → Equiv.Perm (Fin (A i).card)) (π : Fin N ≃ Fin N),
      S (Equiv.trans (RiffleLowerV2.Ascent.blockAction A hA η) π) ↔ S π) →
    ∀ (τ : RiffleLowerV2.Permutation N),
      (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
          S π ∧ ∀ (i : I), RiffleLowerV2.Ascent.relativeOrder (A i) π = RiffleLowerV2.Ascent.relativeOrder (A i) τ) =
        RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) S * ∏ i : I, 1 / ↑(A i).card.factorial
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_false

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:73`.

```lean
RiffleLowerV2.Ascent.probability_false : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω), (RiffleLowerV2.probability P fun (x : Ω) => False) = 0
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_iUnion_le

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:96`.

```lean
RiffleLowerV2.Ascent.probability_iUnion_le : ∀ {Ω : Type u_1} [inst : Fintype Ω] {I : Type u_3} [inst_1 : Fintype I] (P : PMF Ω) (A : I → Ω → Prop),
  (RiffleLowerV2.probability P fun (ω : Ω) => ∃ (i : I), A i ω) ≤ ∑ i : I, RiffleLowerV2.probability P (A i)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_le_one

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:64`.

```lean
RiffleLowerV2.Ascent.probability_le_one : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop), RiffleLowerV2.probability P A ≤ 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_mono

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:53`.

```lean
RiffleLowerV2.Ascent.probability_mono : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) {A B : Ω → Prop},
  (∀ (ω : Ω), A ω → B ω) → RiffleLowerV2.probability P A ≤ RiffleLowerV2.probability P B
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_nonneg

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:59`.

```lean
RiffleLowerV2.Ascent.probability_nonneg : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop), 0 ≤ RiffleLowerV2.probability P A
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_not

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:76`.

```lean
RiffleLowerV2.Ascent.probability_not : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A : Ω → Prop),
  (RiffleLowerV2.probability P fun (ω : Ω) => ¬A ω) = 1 - RiffleLowerV2.probability P A
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_pathGraphMixture

theorem; source: `RiffleLowerV2/Ascent/Mixture.lean:16`.

```lean
RiffleLowerV2.Ascent.probability_pathGraphMixture : ∀ {N : ℕ} (ρ : PMF (RiffleLowerV2.PathEdges N)) (A : RiffleLowerV2.Permutation N → Prop),
  RiffleLowerV2.probability (RiffleLowerV2.Ascent.pathGraphMixture ρ) A =
    RiffleLowerV2.expect ρ fun (G : RiffleLowerV2.PathEdges N) =>
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        A (RiffleLowerV2.componentSort G π)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_relativeOrder

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Weighted.lean:53`.

```lean
RiffleLowerV2.Ascent.probability_relativeOrder : ∀ {N : ℕ} (A : Finset (Fin N)) (τ : RiffleLowerV2.Permutation N),
  (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
      ∀ x ∈ A, ∀ y ∈ A, π x < π y ↔ τ x < τ y) =
    1 / ↑A.card.factorial
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_sub_le_tv

theorem; source: `RiffleLowerV2/Ascent/Mixture.lean:43`.

```lean
RiffleLowerV2.Ascent.probability_sub_le_tv : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P Q : PMF Ω) (A : Ω → Prop),
  RiffleLowerV2.probability P A - RiffleLowerV2.probability Q A ≤ RiffleLowerV2.tv P Q
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_true

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:70`.

```lean
RiffleLowerV2.Ascent.probability_true : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω), (RiffleLowerV2.probability P fun (x : Ω) => True) = 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_uniform_ascent

theorem; source: `RiffleLowerV2/Ascent/UniformBaseline.lean:17`.

```lean
RiffleLowerV2.Ascent.probability_uniform_ascent : ∀ {N : ℕ} (i j : Fin N),
  i ≠ j →
    (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        π i < π j) =
      1 / 2
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.probability_union_le

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:88`.

```lean
RiffleLowerV2.Ascent.probability_union_le : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (A B : Ω → Prop),
  (RiffleLowerV2.probability P fun (ω : Ω) => A ω ∨ B ω) ≤ RiffleLowerV2.probability P A + RiffleLowerV2.probability P B
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.quantitative_component_failure

theorem; source: `RiffleLowerV2/Ascent/Quantitative.lean:43`.

```lean
RiffleLowerV2.Ascent.quantitative_component_failure : RiffleLowerV2.Targets.ComponentComparison →
  ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)) {M D δ : ℝ},
    0 < M →
      ↑H.card ≤ M →
        576 ≤ M ^ δ →
          24 * D ≤ M ^ δ →
            M ^ (1 / 2 + δ) ≤ ↑(Finset.card (G ∩ RiffleLowerV2.internalEdges H)) →
              ↑(RiffleLowerV2.boundary H).card ≤ D * √M →
                (RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
                    ↑(RiffleLowerV2.ascentCount H (RiffleLowerV2.componentSort G π)) ≤
                      ↑(Finset.card (RiffleLowerV2.internalEdges H)) / 2 + M ^ (1 / 2 + δ / 2)) ≤
                  Real.exp (-M ^ (2 * δ) / 144)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.realizeRelativeOrder

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:98`.

```lean
RiffleLowerV2.Ascent.realizeRelativeOrder : {N : ℕ} → (A : Finset (Fin N)) → Equiv.Perm (Fin A.card) → RiffleLowerV2.Permutation N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder

definition; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:16`.

```lean
RiffleLowerV2.Ascent.relativeOrder : {N : ℕ} → (A : Finset (Fin N)) → RiffleLowerV2.Permutation N → Equiv.Perm (Fin A.card)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrderIndependence

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:143`.

```lean
RiffleLowerV2.Ascent.relativeOrderIndependence : RiffleLowerV2.Targets.RelativeOrderIndependence
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_blockAction

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:130`.

```lean
RiffleLowerV2.Ascent.relativeOrder_blockAction : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] (A : I → Finset (Fin N)) (hA : ∀ (i j : I), i ≠ j → Disjoint (A i) (A j))
  (η : (i : I) → Equiv.Perm (Fin (A i).card)) (π : RiffleLowerV2.Permutation N) (i : I),
  RiffleLowerV2.Ascent.relativeOrder (A i) (Equiv.trans (RiffleLowerV2.Ascent.blockAction A hA η) π) =
    Equiv.trans (RiffleLowerV2.Ascent.relativeOrder (A i) π) (Equiv.symm (η i))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_eq_iff

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:33`.

```lean
RiffleLowerV2.Ascent.relativeOrder_eq_iff : ∀ {N : ℕ} (A : Finset (Fin N)) (π σ : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Ascent.relativeOrder A π = RiffleLowerV2.Ascent.relativeOrder A σ ↔
    ∀ x ∈ A, ∀ y ∈ A, π x < π y ↔ σ x < σ y
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_expect

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:28`.

```lean
RiffleLowerV2.Ascent.relativeOrder_expect : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] (A : I → Finset (Fin N)),
  (∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (F : ((i : I) → Equiv.Perm (Fin (A i).card)) → ℝ),
      (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
          F fun (i : I) => RiffleLowerV2.Ascent.relativeOrder (A i) π) =
        RiffleLowerV2.expect (PMF.uniformOfFintype ((i : I) → Equiv.Perm (Fin (A i).card))) F
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_expect_prod

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:77`.

```lean
RiffleLowerV2.Ascent.relativeOrder_expect_prod : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] [DecidableEq I] (A : I → Finset (Fin N)),
  (∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (f : (i : I) → Equiv.Perm (Fin (A i).card) → ℝ),
      (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
          ∏ i : I, f i (RiffleLowerV2.Ascent.relativeOrder (A i) π)) =
        ∏ i : I,
          RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
            f i (RiffleLowerV2.Ascent.relativeOrder (A i) π)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_expect_single

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:62`.

```lean
RiffleLowerV2.Ascent.relativeOrder_expect_single : ∀ {N : ℕ} (A : Finset (Fin N)) (f : Equiv.Perm (Fin A.card) → ℝ),
  (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
      f (RiffleLowerV2.Ascent.relativeOrder A π)) =
    RiffleLowerV2.expect (PMF.uniformOfFintype (Equiv.Perm (Fin A.card))) f
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_fiber_card_mul

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:122`.

```lean
RiffleLowerV2.Ascent.relativeOrder_fiber_card_mul : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] [DecidableEq I] (A : I → Finset (Fin N)),
  (∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) →
    ∀ (η : (i : I) → Equiv.Perm (Fin (A i).card)),
      Nat.card { π : RiffleLowerV2.Permutation N // (fun (i : I) => RiffleLowerV2.Ascent.relativeOrder (A i) π) = η } *
          ∏ i : I, (A i).card.factorial =
        N.factorial
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_lt_iff

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:25`.

```lean
RiffleLowerV2.Ascent.relativeOrder_lt_iff : ∀ {N : ℕ} (A : Finset (Fin N)) (π : RiffleLowerV2.Permutation N) (x y : Fin A.card),
  π ↑((RiffleLowerV2.Ascent.positionEnum A) x) < π ↑((RiffleLowerV2.Ascent.positionEnum A) y) ↔
    (Equiv.symm (RiffleLowerV2.Ascent.relativeOrder A π)) x < (Equiv.symm (RiffleLowerV2.Ascent.relativeOrder A π)) y
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_realize

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:101`.

```lean
RiffleLowerV2.Ascent.relativeOrder_realize : ∀ {N : ℕ} (A : Finset (Fin N)) (ρ : Equiv.Perm (Fin A.card)),
  RiffleLowerV2.Ascent.relativeOrder A (RiffleLowerV2.Ascent.realizeRelativeOrder A ρ) = ρ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_strictMono

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Basic.lean:19`.

```lean
RiffleLowerV2.Ascent.relativeOrder_strictMono : ∀ {N : ℕ} (A : Finset (Fin N)) (π : RiffleLowerV2.Permutation N),
  StrictMono fun (i : Fin A.card) =>
    π ↑((RiffleLowerV2.Ascent.positionEnum A) ((RiffleLowerV2.Ascent.relativeOrder A π) i))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_surjective

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Law.lean:87`.

```lean
RiffleLowerV2.Ascent.relativeOrder_surjective : ∀ {N : ℕ} (A : Finset (Fin N)), Function.Surjective (RiffleLowerV2.Ascent.relativeOrder A)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.relativeOrder_weighted_expect

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Weighted.lean:12`.

```lean
RiffleLowerV2.Ascent.relativeOrder_weighted_expect : ∀ {N : ℕ} {I : Type u_1} [inst : Fintype I] [inst_1 : DecidableEq I] (A : I → Finset (Fin N))
  (hA : ∀ (i j : I), i ≠ j → Disjoint (A i) (A j)) (w : RiffleLowerV2.Permutation N → ℝ),
  (∀ (η : (i : I) → Equiv.Perm (Fin (A i).card)) (π : Fin N ≃ Fin N),
      w (Equiv.trans (RiffleLowerV2.Ascent.blockAction A hA η) π) = w π) →
    ∀ (F : ((i : I) → Equiv.Perm (Fin (A i).card)) → ℝ),
      (RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
          w π * F fun (i : I) => RiffleLowerV2.Ascent.relativeOrder (A i) π) =
        RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) w *
          RiffleLowerV2.expect (PMF.uniformOfFintype ((i : I) → Equiv.Perm (Fin (A i).card))) F
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.retainedBoundaries

definition; source: `RiffleLowerV2/Ascent/Components.lean:16`.

```lean
RiffleLowerV2.Ascent.retainedBoundaries : {N : ℕ} → RiffleLowerV2.PathEdges N → Finset (Fin N) → RiffleLowerV2.PathEdges N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.retainedBoundaries_card_le

theorem; source: `RiffleLowerV2/Ascent/Components.lean:126`.

```lean
RiffleLowerV2.Ascent.retainedBoundaries_card_le : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  Finset.card (RiffleLowerV2.Ascent.retainedBoundaries G H) ≤ H.card
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.retained_edges_card_partition

theorem; source: `RiffleLowerV2/Ascent/Expectation.lean:55`.

```lean
RiffleLowerV2.Ascent.retained_edges_card_partition : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (H : Finset (Fin N)),
  Finset.card (RiffleLowerV2.internalEdges H) =
    Finset.card (G ∩ RiffleLowerV2.internalEdges H) + Finset.card (RiffleLowerV2.Ascent.goodBoundaries G H) +
      Finset.card (RiffleLowerV2.Ascent.badBoundaries G H)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.rightComponent

definition; source: `RiffleLowerV2/Ascent/Components.lean:22`.

```lean
RiffleLowerV2.Ascent.rightComponent : {N : ℕ} → RiffleLowerV2.PathEdges N → Fin (N - 1) → Finset (Fin N)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.scan_threshold_sq_div

theorem; source: `RiffleLowerV2/Ascent/Asymptotic.lean:87`.

```lean
RiffleLowerV2.Ascent.scan_threshold_sq_div : ∀ {M δ : ℝ}, 0 < M → (M ^ (1 / 2 + δ / 2)) ^ 2 / M = M ^ δ
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.separates_blockAction

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean:58`.

```lean
RiffleLowerV2.Ascent.separates_blockAction : ∀ {N : ℕ} (A B : Finset (Fin N)) (hAB : Disjoint A B)
  (η : (i : Bool) → Equiv.Perm (Fin (RiffleLowerV2.Ascent.pairSets A B i).card)) (π : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Ascent.Separates A B
      (Equiv.trans (RiffleLowerV2.Ascent.blockAction (RiffleLowerV2.Ascent.pairSets A B) ⋯ η) π) ↔
    RiffleLowerV2.Ascent.Separates A B π
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.sorted_left_endpoint_ge

theorem; source: `RiffleLowerV2/Ascent/Components.lean:173`.

```lean
RiffleLowerV2.Ascent.sorted_left_endpoint_ge : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G,
    ∀ (π : RiffleLowerV2.Permutation N) {x : Fin N},
      x ∈ RiffleLowerV2.Ascent.leftComponent G e → π x ≤ (RiffleLowerV2.componentSort G π) (RiffleLowerV2.edgeLeft e)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.sorted_right_endpoint_le

theorem; source: `RiffleLowerV2/Ascent/Components.lean:192`.

```lean
RiffleLowerV2.Ascent.sorted_right_endpoint_le : ∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G,
    ∀ (π : RiffleLowerV2.Permutation N) {y : Fin N},
      y ∈ RiffleLowerV2.Ascent.rightComponent G e → (RiffleLowerV2.componentSort G π) (RiffleLowerV2.edgeRight e) ≤ π y
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.subgaussian_tails

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:124`.

```lean
RiffleLowerV2.Ascent.subgaussian_tails : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P : PMF Ω) (X : Ω → ℝ) {B t : ℝ},
  0 < B →
    0 < t →
      (∀ (u : ℝ), (RiffleLowerV2.expect P fun (ω : Ω) => Real.exp (u * X ω)) ≤ Real.exp (u ^ 2 * B / 4)) →
        (RiffleLowerV2.probability P fun (ω : Ω) => t ≤ X ω) ≤ Real.exp (-t ^ 2 / B) ∧
          (RiffleLowerV2.probability P fun (ω : Ω) => X ω ≤ -t) ≤ Real.exp (-t ^ 2 / B)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.successfulTranslates

definition; source: `RiffleLowerV2/Ascent/Selection.lean:9`.

```lean
RiffleLowerV2.Ascent.successfulTranslates : {N : ℕ} → Finset ℤ → RiffleLowerV2.PathEdges N → ℝ → Finset (Fin (N + 1))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.swapPositions

definition; source: `RiffleLowerV2/Ascent/UniformBaseline.lean:10`.

```lean
RiffleLowerV2.Ascent.swapPositions : {N : ℕ} → Fin N → Fin N → RiffleLowerV2.Permutation N ≃ RiffleLowerV2.Permutation N
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.tv_le_one

theorem; source: `RiffleLowerV2/Ascent/Mixture.lean:69`.

```lean
RiffleLowerV2.Ascent.tv_le_one : ∀ {Ω : Type u_1} [inst : Fintype Ω] (P Q : PMF Ω), RiffleLowerV2.tv P Q ≤ 1
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.two_class_indicator_concentration

theorem; source: `RiffleLowerV2/Ascent/MGF.lean:161`.

```lean
RiffleLowerV2.Ascent.two_class_indicator_concentration : ∀ {Ω : Type u_1} [inst : Fintype Ω] {I : Type u_2} (P : PMF Ω) (X : Ω → ℝ) (c : ℝ) (s₀ s₁ : Finset I)
  (A : I → Ω → Prop),
  (∀ (ω : Ω), X ω = (c + ∑ i ∈ s₀, if A i ω then 1 else 0) + ∑ i ∈ s₁, if A i ω then 1 else 0) →
    (∀ (u : ℝ),
        (RiffleLowerV2.expect P fun (ω : Ω) =>
            ∏ i ∈ s₀, Real.exp (u * ((if A i ω then 1 else 0) - RiffleLowerV2.probability P (A i)))) =
          ∏ i ∈ s₀,
            RiffleLowerV2.expect P fun (ω : Ω) =>
              Real.exp (u * ((if A i ω then 1 else 0) - RiffleLowerV2.probability P (A i)))) →
      (∀ (u : ℝ),
          (RiffleLowerV2.expect P fun (ω : Ω) =>
              ∏ i ∈ s₁, Real.exp (u * ((if A i ω then 1 else 0) - RiffleLowerV2.probability P (A i)))) =
            ∏ i ∈ s₁,
              RiffleLowerV2.expect P fun (ω : Ω) =>
                Real.exp (u * ((if A i ω then 1 else 0) - RiffleLowerV2.probability P (A i)))) →
        ∀ {M t : ℝ},
          0 < M →
            ↑s₀.card + ↑s₁.card ≤ M →
              0 < t →
                (RiffleLowerV2.probability P fun (ω : Ω) => t ≤ X ω - RiffleLowerV2.expect P X) ≤
                    Real.exp (-t ^ 2 / M) ∧
                  (RiffleLowerV2.probability P fun (ω : Ω) => X ω - RiffleLowerV2.expect P X ≤ -t) ≤
                    Real.exp (-t ^ 2 / M)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniformGraphScan

theorem; source: `RiffleLowerV2/Ascent/Test.lean:15`.

```lean
RiffleLowerV2.Ascent.uniformGraphScan : RiffleLowerV2.Targets.UniformGraphScan
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniformGraphScan_of_comparison

theorem; source: `RiffleLowerV2/Ascent/Asymptotic.lean:50`.

```lean
RiffleLowerV2.Ascent.uniformGraphScan_of_comparison : RiffleLowerV2.Targets.ComponentComparison → RiffleLowerV2.Targets.UniformGraphScan
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniformScan

theorem; source: `RiffleLowerV2/Ascent/Concentration.lean:89`.

```lean
RiffleLowerV2.Ascent.uniformScan : RiffleLowerV2.Targets.UniformScan
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniformScan_of_concentration

theorem; source: `RiffleLowerV2/Ascent/FiniteConsequences.lean:12`.

```lean
RiffleLowerV2.Ascent.uniformScan_of_concentration : RiffleLowerV2.Targets.ComponentConcentration → RiffleLowerV2.Targets.UniformScan
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniform_expect_equiv

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:126`.

```lean
RiffleLowerV2.Ascent.uniform_expect_equiv : ∀ {Ω : Type u_1} {Γ : Type u_2} [inst : Fintype Ω] [inst_1 : Fintype Γ] [inst_2 : Nonempty Ω] [inst_3 : Nonempty Γ]
  (e : Ω ≃ Γ) (f : Γ → ℝ),
  (RiffleLowerV2.expect (PMF.uniformOfFintype Ω) fun (ω : Ω) => f (e ω)) =
    RiffleLowerV2.expect (PMF.uniformOfFintype Γ) f
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniform_null_scan_bound

theorem; source: `RiffleLowerV2/Ascent/Asymptotic.lean:115`.

```lean
RiffleLowerV2.Ascent.uniform_null_scan_bound : RiffleLowerV2.Targets.UniformScan →
  ∀ {N : ℕ},
    0 < N →
      ∀ (H0 : Finset ℤ) {a δ : ℝ},
        0 < a →
          0 < δ →
            ↑N ^ a ≤ ↑H0.card →
              RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N)
                  (RiffleLowerV2.scan H0 (↑H0.card ^ (1 / 2 + δ / 2))) ≤
                (↑N + 1) * Real.exp (-↑N ^ (a * δ))
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniform_null_scan_eventually

theorem; source: `RiffleLowerV2/Ascent/Asymptotic.lean:131`.

```lean
RiffleLowerV2.Ascent.uniform_null_scan_eventually : RiffleLowerV2.Targets.UniformScan →
  ∀ (a δ ε : ℝ),
    0 < a →
      0 < δ →
        0 < ε →
          ∃ (N0 : ℕ),
            1 ≤ N0 ∧
              ∀ N ≥ N0,
                ∀ (H0 : Finset ℤ),
                  ↑N ^ a ≤ ↑H0.card →
                    RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N)
                        (RiffleLowerV2.scan H0 (↑H0.card ^ (1 / 2 + δ / 2))) ≤
                      ε
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniform_probability

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:145`.

```lean
RiffleLowerV2.Ascent.uniform_probability : ∀ {Ω : Type u_1} [inst : Fintype Ω] [inst_1 : Nonempty Ω] (A : Ω → Prop),
  RiffleLowerV2.probability (PMF.uniformOfFintype Ω) A = ↑(Fintype.card { ω : Ω // A ω }) / ↑(Fintype.card Ω)
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.uniform_probability_equiv

theorem; source: `RiffleLowerV2/Ascent/FiniteProbability.lean:139`.

```lean
RiffleLowerV2.Ascent.uniform_probability_equiv : ∀ {Ω : Type u_1} {Γ : Type u_2} [inst : Fintype Ω] [inst_1 : Fintype Γ] [inst_2 : Nonempty Ω] [inst_3 : Nonempty Γ]
  (e : Ω ≃ Γ) (A : Γ → Prop),
  (RiffleLowerV2.probability (PMF.uniformOfFintype Ω) fun (ω : Ω) => A (e ω)) =
    RiffleLowerV2.probability (PMF.uniformOfFintype Γ) A
```

Axiom closure: propext, Classical.choice, Quot.sound.

## RiffleLowerV2.Ascent.union_relativeOrder_iff

theorem; source: `RiffleLowerV2/Ascent/RelativeOrder/Boundary.lean:26`.

```lean
RiffleLowerV2.Ascent.union_relativeOrder_iff : ∀ {N : ℕ} (A B : Finset (Fin N)) (π τ : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Ascent.Separates A B τ →
    (RiffleLowerV2.Ascent.relativeOrder (A ∪ B) π = RiffleLowerV2.Ascent.relativeOrder (A ∪ B) τ ↔
      RiffleLowerV2.Ascent.Separates A B π ∧
        RiffleLowerV2.Ascent.relativeOrder A π = RiffleLowerV2.Ascent.relativeOrder A τ ∧
          RiffleLowerV2.Ascent.relativeOrder B π = RiffleLowerV2.Ascent.relativeOrder B τ)
```

Axiom closure: propext, Classical.choice, Quot.sound.
