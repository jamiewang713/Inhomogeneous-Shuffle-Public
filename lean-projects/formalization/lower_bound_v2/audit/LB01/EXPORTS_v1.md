# LB-01 exact compiled exports, v1

Generated from Lean 4.33.1 after importing `RiffleLowerV2.Model.Main`. Types and axiom closure below are taken from the elaborated environment. Required target definitions are expanded in the frozen Contracts/v1/EXPORTS.md.

## RiffleLowerV2.Model.BlockIncreasing

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.BlockIncreasing :
{N : ℕ} → RiffleLowerV2.PathEdges N → RiffleLowerV2.Permutation N → Prop
```

## RiffleLowerV2.Model.ComponentSortFiber

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.ComponentSortFiber :
{N : ℕ} → RiffleLowerV2.PathEdges N → RiffleLowerV2.Permutation N → Type
```

## RiffleLowerV2.Model.KeyAssignmentFiber

Kind: definition. Axiom closure: Quot.sound.

```lean
RiffleLowerV2.Model.KeyAssignmentFiber :
{N : ℕ} → {W : Type u_1} → (Fin N → W) → (Fin N → W) → Type
```

## RiffleLowerV2.Model.KeyStabilizer

Kind: definition. Axiom closure: Quot.sound.

```lean
RiffleLowerV2.Model.KeyStabilizer :
{N : ℕ} → {W : Type u_1} → (Fin N → W) → Type
```

## RiffleLowerV2.Model.card_filter_reindex

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.card_filter_reindex :
∀ {N : ℕ} (σ : RiffleLowerV2.Permutation N) (P : Fin N → Prop),
  {i : Fin N | P (σ i)}.card = (Finset.filter P Finset.univ).card
```

## RiffleLowerV2.Model.card_filter_reindex._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.card_filter_reindex._simp_1_1 :
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a)
```

## RiffleLowerV2.Model.card_filter_reindex._simp_1_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.card_filter_reindex._simp_1_2 :
∀ {α : Type u_1} [inst : Fintype α] (x : α), (x ∈ Finset.univ) = True
```

## RiffleLowerV2.Model.columnEquiv

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnEquiv :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) →
    (j : Fin K) →
      RiffleLowerV2.Permutation N → TimeProfile.ColumnAssignments cuts j ≃ TimeProfile.ColumnAssignments cuts j
```

## RiffleLowerV2.Model.columnEquiv._proof_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnEquiv._proof_1 :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (σ : RiffleLowerV2.Permutation N)
  (a : TimeProfile.ColumnAssignments cuts j),
  RiffleLowerV2.Model.columnRelabel cuts j (Equiv.symm σ) (RiffleLowerV2.Model.columnRelabel cuts j σ a) = a
```

## RiffleLowerV2.Model.columnEquiv._proof_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnEquiv._proof_2 :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (σ : RiffleLowerV2.Permutation N)
  (a : TimeProfile.ColumnAssignments cuts j),
  RiffleLowerV2.Model.columnRelabel cuts j σ (RiffleLowerV2.Model.columnRelabel cuts j (Equiv.symm σ) a) = a
```

## RiffleLowerV2.Model.columnEquiv_apply_val

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnEquiv_apply_val :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (σ : RiffleLowerV2.Permutation N)
  (a : TimeProfile.ColumnAssignments cuts j) (i : Fin N), ↑((RiffleLowerV2.Model.columnEquiv cuts j σ) a) i = ↑a (σ i)
```

## RiffleLowerV2.Model.columnIndependence

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnIndependence :
RiffleLowerV2.Targets.ColumnIndependence
```

## RiffleLowerV2.Model.columnMarginal

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnMarginal :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K),
  PMF.map (fun (ω : TimeProfile.ShuffleSample cuts) => ω j) (TimeProfile.fixedCountPMF cuts) =
    TimeProfile.columnPMF cuts j
```

## RiffleLowerV2.Model.columnRelabel

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnRelabel :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) →
    (j : Fin K) →
      RiffleLowerV2.Permutation N → TimeProfile.ColumnAssignments cuts j → TimeProfile.ColumnAssignments cuts j
```

## RiffleLowerV2.Model.columnRelabel._proof_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnRelabel._proof_1 :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (σ : RiffleLowerV2.Permutation N)
  (a : TimeProfile.ColumnAssignments cuts j) (l : Fin k), {i : Fin N | ↑a (σ i) = l}.card = cuts.count j l
```

## RiffleLowerV2.Model.columnRelabel.eq_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.columnRelabel.eq_1 :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (σ : RiffleLowerV2.Permutation N)
  (a : TimeProfile.ColumnAssignments cuts j),
  RiffleLowerV2.Model.columnRelabel cuts j σ a = ⟨fun (i : Fin N) => ↑a (σ i), ⋯⟩
```

## RiffleLowerV2.Model.componentIndex_eq_of_key_eq

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_eq_of_key_eq :
∀ {N : ℕ} {α : Type u_1} [inst : PartialOrder α] (f : Fin N → α),
  Monotone f →
    ∀ {i j : Fin N},
      f i = f j →
        RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) i =
          RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) j
```

## RiffleLowerV2.Model.componentIndex_eq_of_key_eq._proof_1_3

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_eq_of_key_eq._proof_1_3 :
∀ {N : ℕ} (a b : Fin N) (e : Fin (N - 1)), ¬↑e < ↑a → ¬↑a ≤ ↑e → False
```

## RiffleLowerV2.Model.componentIndex_eq_of_key_eq._proof_1_4

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_eq_of_key_eq._proof_1_4 :
∀ {N : ℕ} (a b : Fin N) (e : Fin (N - 1)), ¬↑e ≤ ↑e + 1 → False
```

## RiffleLowerV2.Model.componentIndex_eq_of_key_eq._proof_1_5

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_eq_of_key_eq._proof_1_5 :
∀ {N : ℕ} (a b : Fin N) (e : Fin (N - 1)), ↑e < ↑b → ¬↑e + 1 ≤ ↑b → False
```

## RiffleLowerV2.Model.componentIndex_eq_of_key_eq._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_eq_of_key_eq._simp_1_1 :
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a)
```

## RiffleLowerV2.Model.componentIndex_eq_of_key_eq._simp_1_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_eq_of_key_eq._simp_1_2 :
∀ {α : Type u_1} [inst : Fintype α] (x : α), (x ∈ Finset.univ) = True
```

## RiffleLowerV2.Model.componentIndex_keyEdges_eq_iff

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_keyEdges_eq_iff :
∀ {N : ℕ} {α : Type u_1} [inst : PartialOrder α] (f : Fin N → α),
  Monotone f →
    ∀ (i j : Fin N),
      RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) i =
          RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) j ↔
        f i = f j
```

## RiffleLowerV2.Model.componentIndex_keyEdges_lt_iff

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_keyEdges_lt_iff :
∀ {N : ℕ} {α : Type u_1} [inst : LinearOrder α] (f : Fin N → α),
  Monotone f →
    ∀ (i j : Fin N),
      RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) i <
          RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) j ↔
        f i < f j
```

## RiffleLowerV2.Model.componentIndex_lt_of_missing

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_lt_of_missing :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N),
  ∀ e ∉ G,
    RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeLeft e) <
      RiffleLowerV2.componentIndex G (RiffleLowerV2.edgeRight e)
```

## RiffleLowerV2.Model.componentIndex_lt_of_missing._proof_1_3

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_lt_of_missing._proof_1_3 :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (e : Fin (N - 1)) ⦃a : Fin (N - 1)⦄, ↑a < ↑e ∧ a ∉ G → ¬↑a < ↑e + 1 → False
```

## RiffleLowerV2.Model.componentIndex_lt_of_missing._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_lt_of_missing._simp_1_1 :
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a)
```

## RiffleLowerV2.Model.componentIndex_lt_of_missing._simp_1_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_lt_of_missing._simp_1_2 :
∀ {α : Type u_1} [inst : Fintype α] (x : α), (x ∈ Finset.univ) = True
```

## RiffleLowerV2.Model.componentIndex_monotone

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_monotone :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N), Monotone (RiffleLowerV2.componentIndex G)
```

## RiffleLowerV2.Model.componentIndex_monotone._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_monotone._simp_1_1 :
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a)
```

## RiffleLowerV2.Model.componentIndex_monotone._simp_1_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentIndex_monotone._simp_1_2 :
∀ {α : Type u_1} [inst : Fintype α] (x : α), (x ∈ Finset.univ) = True
```

## RiffleLowerV2.Model.componentSort_blockIncreasing

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentSort_blockIncreasing :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (π : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Model.BlockIncreasing G (RiffleLowerV2.componentSort G π)
```

## RiffleLowerV2.Model.componentSort_eq_iff

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentSort_eq_iff :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (π σ : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Model.BlockIncreasing G σ →
    (RiffleLowerV2.componentSort G π = σ ↔
      ∀ (i : Fin N), RiffleLowerV2.componentIndex G ((Equiv.symm π) (σ i)) = RiffleLowerV2.componentIndex G i)
```

## RiffleLowerV2.Model.componentSort_fiber_card_of_not_increasing

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentSort_fiber_card_of_not_increasing :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (σ : RiffleLowerV2.Permutation N),
  ¬RiffleLowerV2.Model.BlockIncreasing G σ → Fintype.card (RiffleLowerV2.Model.ComponentSortFiber G σ) = 0
```

## RiffleLowerV2.Model.componentSort_increasing

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentSort_increasing :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (π : RiffleLowerV2.Permutation N) {i j : Fin N},
  i < j →
    RiffleLowerV2.componentIndex G i = RiffleLowerV2.componentIndex G j →
      (RiffleLowerV2.componentSort G π) i < (RiffleLowerV2.componentSort G π) j
```

## RiffleLowerV2.Model.componentSort_preserves_component

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.componentSort_preserves_component :
∀ {N : ℕ} (G : RiffleLowerV2.PathEdges N) (π : RiffleLowerV2.Permutation N) (i : Fin N),
  RiffleLowerV2.componentIndex G ((Equiv.symm π) ((RiffleLowerV2.componentSort G π) i)) =
    RiffleLowerV2.componentIndex G i
```

## RiffleLowerV2.Model.exists_relabel_of_sortedWord_eq

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.exists_relabel_of_sortedWord_eq :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω η : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.sortedWord ω = RiffleLowerV2.sortedWord η →
    ∃ (ρ : RiffleLowerV2.Permutation N), (RiffleLowerV2.Model.sampleRelabel cuts ρ) ω = η
```

## RiffleLowerV2.Model.expect_bind

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_bind :
∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (P : PMF α) (Q : α → PMF β) (f : β → ℝ),
  RiffleLowerV2.expect (P.bind Q) f = RiffleLowerV2.expect P fun (a : α) => RiffleLowerV2.expect (Q a) f
```

## RiffleLowerV2.Model.expect_const

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_const :
∀ {α : Type u_1} [inst : Fintype α] (P : PMF α) (c : ℝ), (RiffleLowerV2.expect P fun (x : α) => c) = c
```

## RiffleLowerV2.Model.expect_const._simp_1_1

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.expect_const._simp_1_1 :
∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R),
  ∑ i ∈ s, f i * a = (∑ i ∈ s, f i) * a
```

## RiffleLowerV2.Model.expect_map

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_map :
∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (P : PMF α) (g : α → β) (f : β → ℝ),
  RiffleLowerV2.expect (PMF.map g P) f = RiffleLowerV2.expect P fun (a : α) => f (g a)
```

## RiffleLowerV2.Model.expect_singleton

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_singleton :
∀ {α : Type u_1} [inst : Fintype α] (P : PMF α) (a : α),
  (RiffleLowerV2.expect P fun (b : α) => if b = a then 1 else 0) = (P a).toReal
```

## RiffleLowerV2.Model.expect_swap

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_swap :
∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (P : PMF α) (Q : PMF β) (F : α → β → ℝ),
  (RiffleLowerV2.expect P fun (a : α) => RiffleLowerV2.expect Q (F a)) =
    RiffleLowerV2.expect Q fun (b : β) => RiffleLowerV2.expect P fun (a : α) => F a b
```

## RiffleLowerV2.Model.expect_uniform

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_uniform :
∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Nonempty α] (f : α → ℝ),
  RiffleLowerV2.expect (PMF.uniformOfFintype α) f = (∑ a : α, f a) / ↑(Fintype.card α)
```

## RiffleLowerV2.Model.expect_uniform._simp_1_1

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.expect_uniform._simp_1_1 :
∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R),
  ∑ i ∈ s, a * f i = a * ∑ i ∈ s, f i
```

## RiffleLowerV2.Model.expect_uniform_const

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_uniform_const :
∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Nonempty α] (c : ℝ),
  (RiffleLowerV2.expect (PMF.uniformOfFintype α) fun (x : α) => c) = c
```

## RiffleLowerV2.Model.expect_uniform_const._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.expect_uniform_const._simp_1_1 :
∀ {α : Type u_1} [inst : Fintype α] [Nonempty α], (Fintype.card α = 0) = False
```

## RiffleLowerV2.Model.graphEventIdentity

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.graphEventIdentity :
RiffleLowerV2.Targets.GraphEventIdentity
```

## RiffleLowerV2.Model.graphRepresentation

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.graphRepresentation :
RiffleLowerV2.Targets.GraphRepresentation
```

## RiffleLowerV2.Model.inversionEquiv

Kind: definition. Axiom closure: .

```lean
RiffleLowerV2.Model.inversionEquiv :
(N : ℕ) → RiffleLowerV2.Permutation N ≃ RiffleLowerV2.Permutation N
```

## RiffleLowerV2.Model.inversionEquiv._proof_1

Kind: theorem. Axiom closure: .

```lean
RiffleLowerV2.Model.inversionEquiv._proof_1 :
∀ (N : ℕ) (e : Fin N ≃ Fin N), e.symm.symm = e
```

## RiffleLowerV2.Model.inversionTV

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.inversionTV :
RiffleLowerV2.Targets.InversionTV
```

## RiffleLowerV2.Model.keyAssignmentFiberEquiv

Kind: definition. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiberEquiv :
{N : ℕ} →
  {W : Type u_1} →
    (f g : Fin N → W) →
      (τ : RiffleLowerV2.Permutation N) →
        (∀ (i : Fin N), f (τ i) = g i) →
          RiffleLowerV2.Model.KeyAssignmentFiber f g ≃ RiffleLowerV2.Model.KeyStabilizer f
```

## RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_1

Kind: theorem. Axiom closure: Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_1 :
∀ {N : ℕ} {W : Type u_1} (f g : Fin N → W) (τ : RiffleLowerV2.Permutation N),
  (∀ (i : Fin N), f (τ i) = g i) →
    ∀ (ρ : RiffleLowerV2.Model.KeyAssignmentFiber f g) (i : Fin N), f (((Equiv.symm τ).trans ↑ρ) i) = f i
```

## RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_2

Kind: theorem. Axiom closure: Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_2 :
∀ {N : ℕ} {W : Type u_1} (f g : Fin N → W) (τ : RiffleLowerV2.Permutation N),
  (∀ (i : Fin N), f (τ i) = g i) →
    ∀ (ρ : RiffleLowerV2.Model.KeyStabilizer f) (i : Fin N), f ((Equiv.trans τ ↑ρ) i) = g i
```

## RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_3

Kind: theorem. Axiom closure: Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_3 :
∀ {N : ℕ} {W : Type u_1} (f g : Fin N → W) (τ : RiffleLowerV2.Permutation N) (hτ : ∀ (i : Fin N), f (τ i) = g i)
  (ρ : RiffleLowerV2.Model.KeyAssignmentFiber f g) (i : Fin N),
  f ((Equiv.trans τ ↑⟨(Equiv.symm τ).trans ↑ρ, ⋯⟩) i) = g i
```

## RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_4

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_4 :
∀ {N : ℕ} {W : Type u_1} (f g : Fin N → W) (τ : RiffleLowerV2.Permutation N) (hτ : ∀ (i : Fin N), f (τ i) = g i)
  (ρ : RiffleLowerV2.Model.KeyAssignmentFiber f g), ⟨Equiv.trans τ ↑⟨(Equiv.symm τ).trans ↑ρ, ⋯⟩, ⋯⟩ = ρ
```

## RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_5

Kind: theorem. Axiom closure: Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_5 :
∀ {N : ℕ} {W : Type u_1} (f g : Fin N → W) (τ : RiffleLowerV2.Permutation N) (hτ : ∀ (i : Fin N), f (τ i) = g i)
  (ρ : RiffleLowerV2.Model.KeyStabilizer f) (i : Fin N), f (((Equiv.symm τ).trans ↑⟨Equiv.trans τ ↑ρ, ⋯⟩) i) = f i
```

## RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_6

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiberEquiv._proof_6 :
∀ {N : ℕ} {W : Type u_1} (f g : Fin N → W) (τ : RiffleLowerV2.Permutation N) (hτ : ∀ (i : Fin N), f (τ i) = g i)
  (ρ : RiffleLowerV2.Model.KeyStabilizer f), ⟨(Equiv.symm τ).trans ↑⟨Equiv.trans τ ↑ρ, ⋯⟩, ⋯⟩ = ρ
```

## RiffleLowerV2.Model.keyAssignmentFiber_card

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyAssignmentFiber_card :
∀ {N : ℕ} {W : Type u_1} [inst : Fintype W] (f g : Fin N → W) (τ : RiffleLowerV2.Permutation N),
  (∀ (i : Fin N), f (τ i) = g i) →
    Fintype.card (RiffleLowerV2.Model.KeyAssignmentFiber f g) = ∏ w : W, {i : Fin N | f i = w}.card.factorial
```

## RiffleLowerV2.Model.keyEdges

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyEdges :
{N : ℕ} → {α : Type u_1} → (Fin N → α) → RiffleLowerV2.PathEdges N
```

## RiffleLowerV2.Model.keyEdges.eq_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyEdges.eq_1 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α),
  RiffleLowerV2.Model.keyEdges f = {e : Fin (N - 1) | f (RiffleLowerV2.edgeLeft e) = f (RiffleLowerV2.edgeRight e)}
```

## RiffleLowerV2.Model.keyEdges_sortedWord

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyEdges_sortedWord :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.Model.keyEdges (RiffleLowerV2.sortedWord ω) = RiffleLowerV2.shuffleEdges ω
```

## RiffleLowerV2.Model.keyStabilizerEquiv

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizerEquiv :
{N : ℕ} →
  {W : Type u_1} →
    (f : Fin N → W) → RiffleLowerV2.Model.KeyStabilizer f ≃ ((w : W) → Equiv.Perm { i : Fin N // f i = w })
```

## RiffleLowerV2.Model.keyStabilizerEquiv._proof_1

Kind: theorem. Axiom closure: Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizerEquiv._proof_1 :
∀ {N : ℕ} {W : Type u_1} (f : Fin N → W) (ρ : RiffleLowerV2.Model.KeyStabilizer f) (w : W) (i : Fin N),
  f i = w ↔ f (↑ρ i) = w
```

## RiffleLowerV2.Model.keyStabilizerEquiv._proof_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizerEquiv._proof_2 :
∀ {N : ℕ} {W : Type u_1} (f : Fin N → W) (η : (w : W) → Equiv.Perm { i : Fin N // f i = w }) (a : Fin N),
  f ((Equiv.ofFiberEquiv η) a) = f a
```

## RiffleLowerV2.Model.keyStabilizerEquiv._proof_3

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizerEquiv._proof_3 :
∀ {N : ℕ} {W : Type u_1} (f : Fin N → W) (ρ : RiffleLowerV2.Model.KeyStabilizer f) (a : Fin N),
  f ((Equiv.ofFiberEquiv fun (w : W) => Equiv.subtypeEquiv ↑ρ ⋯) a) = f a
```

## RiffleLowerV2.Model.keyStabilizerEquiv._proof_4

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizerEquiv._proof_4 :
∀ {N : ℕ} {W : Type u_1} (f : Fin N → W) (ρ : RiffleLowerV2.Model.KeyStabilizer f),
  ⟨Equiv.ofFiberEquiv fun (w : W) => Equiv.subtypeEquiv ↑ρ ⋯, ⋯⟩ = ρ
```

## RiffleLowerV2.Model.keyStabilizerEquiv._proof_5

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizerEquiv._proof_5 :
∀ {N : ℕ} {W : Type u_1} (f : Fin N → W) (η : (w : W) → Equiv.Perm { i : Fin N // f i = w }) (w : W) (i : Fin N),
  f i = w ↔ f (↑⟨Equiv.ofFiberEquiv η, ⋯⟩ i) = w
```

## RiffleLowerV2.Model.keyStabilizerEquiv._proof_6

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizerEquiv._proof_6 :
∀ {N : ℕ} {W : Type u_1} (f : Fin N → W) (η : (w : W) → Equiv.Perm { i : Fin N // f i = w }),
  (fun (w : W) => Equiv.subtypeEquiv ↑⟨Equiv.ofFiberEquiv η, ⋯⟩ ⋯) = η
```

## RiffleLowerV2.Model.keyStabilizer_card

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.keyStabilizer_card :
∀ {N : ℕ} {W : Type u_1} [inst : Fintype W] (f : Fin N → W),
  Fintype.card (RiffleLowerV2.Model.KeyStabilizer f) = ∏ w : W, {i : Fin N | f i = w}.card.factorial
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N},
  RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) i =
      RiffleLowerV2.componentIndex (RiffleLowerV2.Model.keyEdges f) j →
    f i = f j
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_1 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (a b : Fin N), ↑b - ↑a = 0 → a ≤ b → ¬↑a = ↑b → False
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_2 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (d : ℕ) (a b : Fin N), ↑b - ↑a = d + 1 → a ≤ b → ¬0 < ↑b → False
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_3

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_3 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (d : ℕ) (a b : Fin N), 0 < ↑b → ¬↑b - 1 < N → False
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_4

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_4 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (d : ℕ) (a b : Fin N),
  ↑b - ↑a = d + 1 → a ≤ b → 0 < ↑b → ¬↑a ≤ ↑b - 1 → False
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_5

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_5 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (d : ℕ) (a b : Fin N), 0 < ↑b → ¬↑b - 1 ≤ ↑b → False
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_6

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_6 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (d : ℕ) (a b : Fin N),
  ↑b - ↑a = d + 1 → a ≤ b → 0 < ↑b → ¬↑b - 1 - ↑a = d → False
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_7

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_7 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (d : ℕ) (a b : Fin N), 0 < ↑b → ¬↑b - 1 < N - 1 → False
```

## RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_8

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.key_eq_of_componentIndex_eq._proof_1_8 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) {i j : Fin N} (d : ℕ) (a b : Fin N), 0 < ↑b → ¬↑b - 1 + 1 = ↑b → False
```

## RiffleLowerV2.Model.map_equiv_apply

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.map_equiv_apply :
∀ {α : Type u_1} {β : Type u_2} [Fintype α] (P : PMF α) (e : α ≃ β) (b : β), (PMF.map (⇑e) P) b = P (e.symm b)
```

## RiffleLowerV2.Model.map_uniform_equiv

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.map_uniform_equiv :
∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : Nonempty α] [inst_3 : Nonempty β]
  (e : α ≃ β), PMF.map (⇑e) (PMF.uniformOfFintype α) = PMF.uniformOfFintype β
```

## RiffleLowerV2.Model.matrix_expect_eq_graph_expect

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.matrix_expect_eq_graph_expect :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (F : RiffleLowerV2.Permutation N → ℝ),
  RiffleLowerV2.expect (RiffleLowerV2.matrixLaw cuts) F = RiffleLowerV2.expect (RiffleLowerV2.graphMixtureLaw cuts) F
```

## RiffleLowerV2.Model.matrix_multiset_event

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.matrix_multiset_event :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (w : Fin N → RiffleLowerV2.Word k K)
  (A : RiffleLowerV2.Permutation N → Prop),
  (RiffleLowerV2.probability (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      RiffleLowerV2.sortedWord ω = w ∧ A (RiffleLowerV2.stableSort ω)) =
    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      if RiffleLowerV2.sortedWord ω = w then
        RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
          A (RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) π)
      else 0
```

## RiffleLowerV2.Model.matrix_multiset_expect

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.matrix_multiset_expect :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (F : (Fin N → RiffleLowerV2.Word k K) → RiffleLowerV2.Permutation N → ℝ),
  (RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      F (RiffleLowerV2.sortedWord ω) (RiffleLowerV2.stableSort ω)) =
    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      RiffleLowerV2.expect (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        F (RiffleLowerV2.sortedWord ω) (RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) π)
```

## RiffleLowerV2.Model.mem_keyEdges

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.mem_keyEdges :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) (e : Fin (N - 1)),
  e ∈ RiffleLowerV2.Model.keyEdges f ↔ f (RiffleLowerV2.edgeLeft e) = f (RiffleLowerV2.edgeRight e)
```

## RiffleLowerV2.Model.mem_keyEdges._simp_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.mem_keyEdges._simp_1 :
∀ {N : ℕ} {α : Type u_1} (f : Fin N → α) (e : Fin (N - 1)),
  (e ∈ RiffleLowerV2.Model.keyEdges f) = (f (RiffleLowerV2.edgeLeft e) = f (RiffleLowerV2.edgeRight e))
```

## RiffleLowerV2.Model.physicalColumnShear

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalColumnShear :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) →
    (j : Fin K) → (l : List (Fin K)) → j ∉ l → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts
```

## RiffleLowerV2.Model.physicalColumnShear._proof_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalColumnShear._proof_1 :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (l : List (Fin K)),
  j ∉ l →
    ∀ (ω : RiffleLowerV2.Sample cuts),
      Function.update
          (Function.update ω j
            ((RiffleLowerV2.Model.columnEquiv cuts j (Equiv.symm (RiffleLowerV2.Model.physicalListSort l ω))) (ω j)))
          j
          ((RiffleLowerV2.Model.columnEquiv cuts j
              (RiffleLowerV2.Model.physicalListSort l
                (Function.update ω j
                  ((RiffleLowerV2.Model.columnEquiv cuts j (Equiv.symm (RiffleLowerV2.Model.physicalListSort l ω)))
                    (ω j)))))
            (Function.update ω j
              ((RiffleLowerV2.Model.columnEquiv cuts j (Equiv.symm (RiffleLowerV2.Model.physicalListSort l ω))) (ω j))
              j)) =
        ω
```

## RiffleLowerV2.Model.physicalColumnShear._proof_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalColumnShear._proof_2 :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (l : List (Fin K)),
  j ∉ l →
    ∀ (ω : RiffleLowerV2.Sample cuts),
      Function.update
          (Function.update ω j
            ((RiffleLowerV2.Model.columnEquiv cuts j (RiffleLowerV2.Model.physicalListSort l ω)) (ω j)))
          j
          ((RiffleLowerV2.Model.columnEquiv cuts j
              (Equiv.symm
                (RiffleLowerV2.Model.physicalListSort l
                  (Function.update ω j
                    ((RiffleLowerV2.Model.columnEquiv cuts j (RiffleLowerV2.Model.physicalListSort l ω)) (ω j))))))
            (Function.update ω j
              ((RiffleLowerV2.Model.columnEquiv cuts j (RiffleLowerV2.Model.physicalListSort l ω)) (ω j)) j)) =
        ω
```

## RiffleLowerV2.Model.physicalColumnShear_other

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalColumnShear_other :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (l : List (Fin K)) (hj : j ∉ l)
  (ω : RiffleLowerV2.Sample cuts) (t : Fin K), t ≠ j → (RiffleLowerV2.Model.physicalColumnShear cuts j l hj) ω t = ω t
```

## RiffleLowerV2.Model.physicalInverseList

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalInverseList :
{k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → List (Fin K) → RiffleLowerV2.Sample cuts → RiffleLowerV2.Permutation N
```

## RiffleLowerV2.Model.physicalInverseList.eq_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalInverseList.eq_1 :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (l : List (Fin K)) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.Model.physicalInverseList l ω =
    List.foldr (fun (j : Fin K) (deck : RiffleLowerV2.Permutation N) => Equiv.trans (Tuple.sort ↑(ω j)) deck)
      (Equiv.refl (Fin N)) l
```

## RiffleLowerV2.Model.physicalInverseList_foldl

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalInverseList_foldl :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (l : List (Fin K)) (ω : RiffleLowerV2.Sample cuts)
  (deck : RiffleLowerV2.Permutation N),
  (List.foldl (fun (deck : Fin N ≃ Fin N) (j : Fin K) => (Equiv.symm (Tuple.sort ↑(ω j))).trans deck) deck l).symm =
    (Equiv.symm deck).trans (RiffleLowerV2.Model.physicalInverseList l ω)
```

## RiffleLowerV2.Model.physicalInverseList_full

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalInverseList_full :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.Model.physicalInverseList (List.finRange K) ω = RiffleLowerV2.physicalInverse ω
```

## RiffleLowerV2.Model.physicalListSort

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalListSort :
{k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → List (Fin K) → RiffleLowerV2.Sample cuts → RiffleLowerV2.Permutation N
```

## RiffleLowerV2.Model.physicalListSort.eq_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalListSort.eq_1 :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (l : List (Fin K)) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.Model.physicalListSort l ω = Tuple.sort (RiffleLowerV2.Model.physicalRowList l ω)
```

## RiffleLowerV2.Model.physicalListSort_full

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalListSort_full :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.Model.physicalListSort (List.finRange K) ω = RiffleLowerV2.stableSort ω
```

## RiffleLowerV2.Model.physicalListSort_full._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalListSort_full._simp_1_1 :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (i : Fin N),
  List.Vector.toList (RiffleLowerV2.rowWord ω i) = RiffleLowerV2.Model.physicalRowList (List.finRange K) ω i
```

## RiffleLowerV2.Model.physicalListSort_shear

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalListSort_shear :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (j : Fin K) (l : List (Fin K)) (hj : j ∉ l)
  (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.Model.physicalListSort (j :: l) ((RiffleLowerV2.Model.physicalColumnShear cuts j l hj) ω) =
    Equiv.trans (Tuple.sort ↑(ω j)) (RiffleLowerV2.Model.physicalListSort l ω)
```

## RiffleLowerV2.Model.physicalListSort_update

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalListSort_update :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (l : List (Fin K)),
  ∀ j ∉ l,
    ∀ (ω : RiffleLowerV2.Sample cuts) (a : TimeProfile.ColumnAssignments cuts j),
      RiffleLowerV2.Model.physicalListSort l (Function.update ω j a) = RiffleLowerV2.Model.physicalListSort l ω
```

## RiffleLowerV2.Model.physicalMatrixBridge

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalMatrixBridge :
RiffleLowerV2.Targets.PhysicalMatrixBridge
```

## RiffleLowerV2.Model.physicalPullback

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalPullback :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) → (l : List (Fin K)) → l.Nodup → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts
```

## RiffleLowerV2.Model.physicalPullback._f

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalPullback._f :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) →
    (x : List (Fin K)) →
      List.below (motive := fun (x : List (Fin K)) => x.Nodup → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts)
          x →
        x.Nodup → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts
```

## RiffleLowerV2.Model.physicalPullback._proof_1

Kind: theorem. Axiom closure: propext.

```lean
RiffleLowerV2.Model.physicalPullback._proof_1 :
∀ {K : ℕ} (j : Fin K) (l : List (Fin K)), (j :: l).Nodup → l.Nodup
```

## RiffleLowerV2.Model.physicalPullback._proof_2

Kind: theorem. Axiom closure: propext.

```lean
RiffleLowerV2.Model.physicalPullback._proof_2 :
∀ {K : ℕ} (j : Fin K) (l : List (Fin K)), (j :: l).Nodup → j ∉ l
```

## RiffleLowerV2.Model.physicalPullback._sunfold

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalPullback._sunfold :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) → (l : List (Fin K)) → l.Nodup → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts
```

## RiffleLowerV2.Model.physicalPullback._unsafe_rec

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalPullback._unsafe_rec :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) → (l : List (Fin K)) → l.Nodup → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts
```

## RiffleLowerV2.Model.physicalPullback.match_1

Kind: definition. Axiom closure: .

```lean
RiffleLowerV2.Model.physicalPullback.match_1 :
{K : ℕ} →
  (motive : (x : List (Fin K)) → x.Nodup → Sort u_1) →
    (x : List (Fin K)) →
      (x_1 : x.Nodup) →
        ((x : [].Nodup) → motive [] x) →
          ((j : Fin K) → (l : List (Fin K)) → (h : (j :: l).Nodup) → motive (j :: l) h) → motive x x_1
```

## RiffleLowerV2.Model.physicalPullbackEquiv

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalPullbackEquiv :
{k N K : ℕ} → (cuts : TimeProfile.Cuts k N K) → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts
```

## RiffleLowerV2.Model.physicalPullback_other

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalPullback_other :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (l : List (Fin K)) (h : l.Nodup) (ω : RiffleLowerV2.Sample cuts),
  ∀ j ∉ l, (RiffleLowerV2.Model.physicalPullback cuts l h) ω j = ω j
```

## RiffleLowerV2.Model.physicalPullback_sort

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalPullback_sort :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (l : List (Fin K)) (h : l.Nodup) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.Model.physicalListSort l ((RiffleLowerV2.Model.physicalPullback cuts l h) ω) =
    RiffleLowerV2.Model.physicalInverseList l ω
```

## RiffleLowerV2.Model.physicalRowList

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalRowList :
{k N K : ℕ} → {cuts : TimeProfile.Cuts k N K} → List (Fin K) → RiffleLowerV2.Sample cuts → Fin N → List (Fin k)
```

## RiffleLowerV2.Model.physicalRowList.eq_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalRowList.eq_1 :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (l : List (Fin K)) (ω : RiffleLowerV2.Sample cuts) (i : Fin N),
  RiffleLowerV2.Model.physicalRowList l ω i = List.map (fun (j : Fin K) => ↑(ω j) i) l
```

## RiffleLowerV2.Model.physicalRowList_full

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalRowList_full :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (i : Fin N),
  RiffleLowerV2.Model.physicalRowList (List.finRange K) ω i = List.Vector.toList (RiffleLowerV2.rowWord ω i)
```

## RiffleLowerV2.Model.physicalRowList_update

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physicalRowList_update :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (l : List (Fin K)),
  ∀ j ∉ l,
    ∀ (ω : RiffleLowerV2.Sample cuts) (a : TimeProfile.ColumnAssignments cuts j),
      RiffleLowerV2.Model.physicalRowList l (Function.update ω j a) = RiffleLowerV2.Model.physicalRowList l ω
```

## RiffleLowerV2.Model.physical_graph_event

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physical_graph_event :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (A : RiffleLowerV2.Permutation N → Prop),
  RiffleLowerV2.probability (RiffleLowerV2.physicalInverseLaw cuts) A =
    RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) fun (ω : TimeProfile.ShuffleSample cuts) =>
      RiffleLowerV2.probability (RiffleLowerV2.uniformPermutation N) fun (π : RiffleLowerV2.Permutation N) =>
        A (RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) π)
```

## RiffleLowerV2.Model.physical_graph_representation

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.physical_graph_representation :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K),
  RiffleLowerV2.physicalInverseLaw cuts = RiffleLowerV2.graphMixtureLaw cuts
```

## RiffleLowerV2.Model.prefixRanks

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.prefixRanks :
RiffleLowerV2.Targets.PrefixRanks
```

## RiffleLowerV2.Model.prefixRanks._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.prefixRanks._simp_1_1 :
∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred p] {s : Finset α} {a : α}, (a ∈ Finset.filter p s) = (a ∈ s ∧ p a)
```

## RiffleLowerV2.Model.prefixRanks._simp_1_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.prefixRanks._simp_1_2 :
∀ {α : Type u_1} [inst : Fintype α] (x : α), (x ∈ Finset.univ) = True
```

## RiffleLowerV2.Model.prefixRanks._simp_1_4

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.prefixRanks._simp_1_4 :
∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} {a : α}, (a ∈ s \ t) = (a ∈ s ∧ a ∉ t)
```

## RiffleLowerV2.Model.prefixRanks._simp_1_5

Kind: theorem. Axiom closure: propext.

```lean
RiffleLowerV2.Model.prefixRanks._simp_1_5 :
∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, (¬a < b) = (b ≤ a)
```

## RiffleLowerV2.Model.relabelToLabels

Kind: definition. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.relabelToLabels :
{N : ℕ} → RiffleLowerV2.Permutation N → RiffleLowerV2.Permutation N ≃ RiffleLowerV2.Permutation N
```

## RiffleLowerV2.Model.relabelToLabels._proof_1

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.relabelToLabels._proof_1 :
∀ {N : ℕ} (s ρ : RiffleLowerV2.Permutation N), (Equiv.trans s (Equiv.symm ρ)).symm.trans s = ρ
```

## RiffleLowerV2.Model.relabelToLabels._proof_2

Kind: theorem. Axiom closure: propext, Quot.sound.

```lean
RiffleLowerV2.Model.relabelToLabels._proof_2 :
∀ {N : ℕ} (s π : RiffleLowerV2.Permutation N), Equiv.trans s ((Equiv.symm π).trans s).symm = π
```

## RiffleLowerV2.Model.rowRelabeling

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.rowRelabeling :
RiffleLowerV2.Targets.RowRelabeling
```

## RiffleLowerV2.Model.rowWord_relabel

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.rowWord_relabel :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (σ : RiffleLowerV2.Permutation N) (ω : RiffleLowerV2.Sample cuts)
  (i : Fin N), RiffleLowerV2.rowWord ((RiffleLowerV2.Model.sampleRelabel cuts σ) ω) i = RiffleLowerV2.rowWord ω (σ i)
```

## RiffleLowerV2.Model.sampleRelabel

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRelabel :
{k N K : ℕ} →
  (cuts : TimeProfile.Cuts k N K) → RiffleLowerV2.Permutation N → RiffleLowerV2.Sample cuts ≃ RiffleLowerV2.Sample cuts
```

## RiffleLowerV2.Model.sampleRelabelFiberEquiv

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRelabelFiberEquiv :
{k N K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    (ω η : RiffleLowerV2.Sample cuts) →
      { ρ : RiffleLowerV2.Permutation N // (RiffleLowerV2.Model.sampleRelabel cuts ρ) ω = η } ≃
        RiffleLowerV2.Model.KeyAssignmentFiber (RiffleLowerV2.rowWord ω) (RiffleLowerV2.rowWord η)
```

## RiffleLowerV2.Model.sampleRelabelFiberEquiv._proof_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRelabelFiberEquiv._proof_1 :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω η : RiffleLowerV2.Sample cuts) (ρ : RiffleLowerV2.Permutation N),
  (RiffleLowerV2.Model.sampleRelabel cuts ρ) ω = η ↔
    ∀ (i : Fin N),
      RiffleLowerV2.rowWord ω (((Equiv.refl (RiffleLowerV2.Permutation N)) ρ) i) = RiffleLowerV2.rowWord η i
```

## RiffleLowerV2.Model.sampleRelabel_apply

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRelabel_apply :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (σ : RiffleLowerV2.Permutation N) (ω : RiffleLowerV2.Sample cuts)
  (j : Fin K), (RiffleLowerV2.Model.sampleRelabel cuts σ) ω j = (RiffleLowerV2.Model.columnEquiv cuts j σ) (ω j)
```

## RiffleLowerV2.Model.sampleRelabel_fiber_card

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRelabel_fiber_card :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω η : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.sortedWord ω = RiffleLowerV2.sortedWord η →
    Fintype.card { ρ : RiffleLowerV2.Permutation N // (RiffleLowerV2.Model.sampleRelabel cuts ρ) ω = η } =
      ∏ w : RiffleLowerV2.Word k K, {i : Fin N | RiffleLowerV2.rowWord ω i = w}.card.factorial
```

## RiffleLowerV2.Model.sampleRelabel_fiber_card._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRelabel_fiber_card._simp_1_1 :
∀ {α : Type u_1} [inst : Fintype α], Fintype.card α = Nat.card α
```

## RiffleLowerV2.Model.sampleRelabel_uniform

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRelabel_uniform :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (σ : RiffleLowerV2.Permutation N),
  PMF.map (⇑(RiffleLowerV2.Model.sampleRelabel cuts σ)) (TimeProfile.fixedCountPMF cuts) =
    TimeProfile.fixedCountPMF cuts
```

## RiffleLowerV2.Model.sampleRow_relabel

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sampleRow_relabel :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (σ : RiffleLowerV2.Permutation N) (ω : RiffleLowerV2.Sample cuts)
  (i : Fin N), TimeProfile.sampleRow ((RiffleLowerV2.Model.sampleRelabel cuts σ) ω) i = TimeProfile.sampleRow ω (σ i)
```

## RiffleLowerV2.Model.sample_eq_iff_rowWord

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sample_eq_iff_rowWord :
∀ {k N K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω η : RiffleLowerV2.Sample cuts),
  ω = η ↔ RiffleLowerV2.rowWord ω = RiffleLowerV2.rowWord η
```

## RiffleLowerV2.Model.shuffleComponentFiberEquiv

Kind: definition. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleComponentFiberEquiv :
{N k K : ℕ} →
  {cuts : TimeProfile.Cuts k N K} →
    (ω : RiffleLowerV2.Sample cuts) →
      (σ : RiffleLowerV2.Permutation N) →
        RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ →
          RiffleLowerV2.Model.ComponentSortFiber (RiffleLowerV2.shuffleEdges ω) σ ≃
            RiffleLowerV2.Model.KeyAssignmentFiber (RiffleLowerV2.sortedWord ω)
              (RiffleLowerV2.sortedWord ω ∘ ⇑(Equiv.symm σ))
```

## RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_1 :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N)
  (π : RiffleLowerV2.Model.ComponentSortFiber (RiffleLowerV2.shuffleEdges ω) σ) (i : Fin N),
  RiffleLowerV2.sortedWord ω ((Equiv.symm ↑π) i) = RiffleLowerV2.sortedWord ω ((Equiv.symm σ) i)
```

## RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_2

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_2 :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ →
    ∀
      (τ :
        RiffleLowerV2.Model.KeyAssignmentFiber (RiffleLowerV2.sortedWord ω)
          (RiffleLowerV2.sortedWord ω ∘ ⇑(Equiv.symm σ))),
      RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) (Equiv.symm ↑τ) = σ
```

## RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_3

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_3 :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ →
    ∀ (π : RiffleLowerV2.Model.ComponentSortFiber (RiffleLowerV2.shuffleEdges ω) σ),
      RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) (Equiv.symm ↑⟨Equiv.symm ↑π, ⋯⟩) = σ
```

## RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_4

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_4 :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N)
  (hσ : RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ)
  (π : RiffleLowerV2.Model.ComponentSortFiber (RiffleLowerV2.shuffleEdges ω) σ), ⟨Equiv.symm ↑⟨Equiv.symm ↑π, ⋯⟩, ⋯⟩ = π
```

## RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_5

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_5 :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N)
  (hσ : RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ)
  (τ :
    RiffleLowerV2.Model.KeyAssignmentFiber (RiffleLowerV2.sortedWord ω) (RiffleLowerV2.sortedWord ω ∘ ⇑(Equiv.symm σ)))
  (i : Fin N),
  RiffleLowerV2.sortedWord ω ((Equiv.symm ↑⟨Equiv.symm ↑τ, ⋯⟩) i) = RiffleLowerV2.sortedWord ω ((Equiv.symm σ) i)
```

## RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_6

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleComponentFiberEquiv._proof_6 :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N)
  (hσ : RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ)
  (τ :
    RiffleLowerV2.Model.KeyAssignmentFiber (RiffleLowerV2.sortedWord ω) (RiffleLowerV2.sortedWord ω ∘ ⇑(Equiv.symm σ))),
  ⟨Equiv.symm ↑⟨Equiv.symm ↑τ, ⋯⟩, ⋯⟩ = τ
```

## RiffleLowerV2.Model.shuffleEdges_relabel

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffleEdges_relabel :
∀ {N k K : ℕ} (cuts : TimeProfile.Cuts k N K) (ρ : RiffleLowerV2.Permutation N) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.shuffleEdges ((RiffleLowerV2.Model.sampleRelabel cuts ρ) ω) = RiffleLowerV2.shuffleEdges ω
```

## RiffleLowerV2.Model.shuffle_blockIncreasing_iff

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffle_blockIncreasing_iff :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ ↔
    ∀ (i j : Fin N), i < j → RiffleLowerV2.sortedWord ω i = RiffleLowerV2.sortedWord ω j → σ i < σ j
```

## RiffleLowerV2.Model.shuffle_blockIncreasing_iff._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffle_blockIncreasing_iff._simp_1_1 :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (i j : Fin N),
  (RiffleLowerV2.componentIndex (RiffleLowerV2.shuffleEdges ω) i =
      RiffleLowerV2.componentIndex (RiffleLowerV2.shuffleEdges ω) j) =
    (RiffleLowerV2.sortedWord ω i = RiffleLowerV2.sortedWord ω j)
```

## RiffleLowerV2.Model.shuffle_componentIndex_eq_iff

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffle_componentIndex_eq_iff :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (i j : Fin N),
  RiffleLowerV2.componentIndex (RiffleLowerV2.shuffleEdges ω) i =
      RiffleLowerV2.componentIndex (RiffleLowerV2.shuffleEdges ω) j ↔
    RiffleLowerV2.sortedWord ω i = RiffleLowerV2.sortedWord ω j
```

## RiffleLowerV2.Model.shuffle_componentIndex_lt_iff

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffle_componentIndex_lt_iff :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (i j : Fin N),
  RiffleLowerV2.componentIndex (RiffleLowerV2.shuffleEdges ω) i <
      RiffleLowerV2.componentIndex (RiffleLowerV2.shuffleEdges ω) j ↔
    RiffleLowerV2.sortedWord ω i < RiffleLowerV2.sortedWord ω j
```

## RiffleLowerV2.Model.shuffle_componentSort_fiber_card

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffle_componentSort_fiber_card :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N),
  RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ →
    Fintype.card (RiffleLowerV2.Model.ComponentSortFiber (RiffleLowerV2.shuffleEdges ω) σ) =
      ∏ w : RiffleLowerV2.Word k K, {i : Fin N | RiffleLowerV2.sortedWord ω i = w}.card.factorial
```

## RiffleLowerV2.Model.shuffle_componentSort_fiber_card._simp_1_1

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffle_componentSort_fiber_card._simp_1_1 :
∀ {α : Type u_1} [inst : Fintype α], Fintype.card α = Nat.card α
```

## RiffleLowerV2.Model.shuffle_componentSort_fiber_card_eq

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.shuffle_componentSort_fiber_card_eq :
∀ {N k K : ℕ} {cuts : TimeProfile.Cuts k N K} (ω : RiffleLowerV2.Sample cuts) (σ : RiffleLowerV2.Permutation N),
  Fintype.card (RiffleLowerV2.Model.ComponentSortFiber (RiffleLowerV2.shuffleEdges ω) σ) =
    if RiffleLowerV2.Model.BlockIncreasing (RiffleLowerV2.shuffleEdges ω) σ then
      ∏ w : RiffleLowerV2.Word k K, {i : Fin N | RiffleLowerV2.sortedWord ω i = w}.card.factorial
    else 0
```

## RiffleLowerV2.Model.sort_cons

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sort_cons :
∀ {N : ℕ} {α : Type u_1} [inst : LinearOrder α] (f : Fin N → α) (g : Fin N → List α),
  (Tuple.sort fun (i : Fin N) => f i :: g i) =
    Equiv.trans (Tuple.sort fun (i : Fin N) => f ((Tuple.sort g) i)) (Tuple.sort g)
```

## RiffleLowerV2.Model.sort_pair_preserves_first

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sort_pair_preserves_first :
∀ {N : ℕ} {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] [inst_1 : LinearOrder β] (c : Fin N → α) (v : Fin N → β),
  Monotone c → ∀ (i : Fin N), c ((Tuple.sort fun (j : Fin N) => toLex (c j, v j)) i) = c i
```

## RiffleLowerV2.Model.sort_pair_second_strict

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sort_pair_second_strict :
∀ {N : ℕ} {α : Type u_1} [inst : LinearOrder α] (c : Fin N → α) (π : RiffleLowerV2.Permutation N),
  Monotone c →
    ∀ {i j : Fin N},
      i < j →
        c i = c j →
          π ((Tuple.sort fun (q : Fin N) => toLex (c q, π q)) i) <
            π ((Tuple.sort fun (q : Fin N) => toLex (c q, π q)) j)
```

## RiffleLowerV2.Model.sort_relabel_componentSort

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sort_relabel_componentSort :
∀ {N : ℕ} {α : Type u_1} [inst : LinearOrder α] (f : Fin N → α) (ρ : RiffleLowerV2.Permutation N),
  Tuple.sort (f ∘ ⇑ρ) =
    RiffleLowerV2.componentSort (RiffleLowerV2.Model.keyEdges (f ∘ ⇑(Tuple.sort f)))
      (Equiv.trans (Tuple.sort f) (Equiv.symm ρ))
```

## RiffleLowerV2.Model.sortedWord_relabel

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.sortedWord_relabel :
∀ {N k K : ℕ} (cuts : TimeProfile.Cuts k N K) (ρ : RiffleLowerV2.Permutation N) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.sortedWord ((RiffleLowerV2.Model.sampleRelabel cuts ρ) ω) = RiffleLowerV2.sortedWord ω
```

## RiffleLowerV2.Model.stableSort_physicalPullback

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.stableSort_physicalPullback :
∀ {k N K : ℕ} (cuts : TimeProfile.Cuts k N K) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.stableSort ((RiffleLowerV2.Model.physicalPullbackEquiv cuts) ω) = RiffleLowerV2.physicalInverse ω
```

## RiffleLowerV2.Model.stableSort_relabel

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.stableSort_relabel :
∀ {N k K : ℕ} (cuts : TimeProfile.Cuts k N K) (ρ : RiffleLowerV2.Permutation N) (ω : RiffleLowerV2.Sample cuts),
  RiffleLowerV2.stableSort ((RiffleLowerV2.Model.sampleRelabel cuts ρ) ω) =
    RiffleLowerV2.componentSort (RiffleLowerV2.shuffleEdges ω) (Equiv.trans (RiffleLowerV2.stableSort ω) (Equiv.symm ρ))
```

## RiffleLowerV2.Model.stableTie

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.stableTie :
RiffleLowerV2.Targets.StableTie
```

## RiffleLowerV2.Model.uniform_expect_equiv

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.uniform_expect_equiv :
∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] [inst_2 : Nonempty α] [inst_3 : Nonempty β]
  (e : α ≃ β) (f : β → ℝ),
  (RiffleLowerV2.expect (PMF.uniformOfFintype α) fun (a : α) => f (e a)) =
    RiffleLowerV2.expect (PMF.uniformOfFintype β) f
```

## RiffleLowerV2.Model.uniform_pi_expect_prod

Kind: theorem. Axiom closure: propext, Classical.choice, Quot.sound.

```lean
RiffleLowerV2.Model.uniform_pi_expect_prod :
∀ {T : Type u_1} [inst : Fintype T] {A : T → Type u_2} [inst_1 : (t : T) → Fintype (A t)]
  [inst_2 : ∀ (t : T), Nonempty (A t)] (f : (t : T) → A t → ℝ),
  (RiffleLowerV2.expect (PMF.uniformOfFintype ((t : T) → A t)) fun (ω : (t : T) → A t) => ∏ t : T, f t (ω t)) =
    ∏ t : T, RiffleLowerV2.expect (PMF.uniformOfFintype (A t)) (f t)
```

