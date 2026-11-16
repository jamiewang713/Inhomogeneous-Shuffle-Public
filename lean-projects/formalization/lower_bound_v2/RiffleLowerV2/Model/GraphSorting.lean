import RiffleLowerV2.Shared.Path
import RiffleLowerV2.Model.FiniteLaws

/-! Deterministic component normalization for the concrete shuffle graph.
The sorting characterizations used below are the pinned mathlib `Tuple` theorems.
All cardinality/path arguments are new proofs valid also for an empty deck. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleLowerV2.Model

variable {N : ℕ}

theorem componentIndex_monotone (G : PathEdges N) : Monotone (componentIndex G) := by
  intro i j hij
  apply Finset.card_le_card
  intro e he
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  exact ⟨lt_of_lt_of_le he.1 hij, he.2⟩

theorem componentIndex_lt_of_missing (G : PathEdges N) (e : Fin (N-1)) (he : e ∉ G) :
    componentIndex G (edgeLeft e) < componentIndex G (edgeRight e) := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨by dsimp [edgeLeft, edgeRight] at *; omega, ha.2⟩
  · intro hh
    have hmem : e ∈ Finset.univ.filter
        (fun a : Fin (N-1) => a.val < (edgeRight e).val ∧ a ∉ G) := by
      simp [edgeRight, he]
    rw [← hh] at hmem
    simp [edgeLeft] at hmem

def keyEdges {α : Type*} (f : Fin N → α) : PathEdges N :=
  Finset.univ.filter fun e => f (edgeLeft e) = f (edgeRight e)

@[simp] theorem mem_keyEdges {α : Type*} (f : Fin N → α) (e : Fin (N-1)) :
    e ∈ keyEdges f ↔ f (edgeLeft e) = f (edgeRight e) := by simp [keyEdges]

theorem componentIndex_eq_of_key_eq {α : Type*} [PartialOrder α]
    (f : Fin N → α) (hf : Monotone f) {i j : Fin N} (h : f i = f j) :
    componentIndex (keyEdges f) i = componentIndex (keyEdges f) j := by
  suffices hforward : ∀ a b : Fin N, a ≤ b → f a = f b →
      componentIndex (keyEdges f) a = componentIndex (keyEdges f) b by
    rcases le_total i j with hij | hji
    · exact hforward i j hij h
    · exact (hforward j i hji h.symm).symm
  intro a b hab heq
  unfold componentIndex
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hleft, hmissing⟩
    exact ⟨lt_of_lt_of_le hleft hab, hmissing⟩
  · rintro ⟨hright, hmissing⟩
    refine ⟨?_, hmissing⟩
    by_contra hn
    have hal : a ≤ edgeLeft e := by change a.val ≤ e.val; omega
    have hlr : edgeLeft e ≤ edgeRight e := by change e.val ≤ e.val+1; omega
    have hrb : edgeRight e ≤ b := by change e.val+1 ≤ b.val; omega
    apply hmissing
    apply (mem_keyEdges f e).mpr
    apply le_antisymm (hf hlr)
    exact (hf hrb).trans (heq ▸ hf hal)

theorem key_eq_of_componentIndex_eq {α : Type*} (f : Fin N → α)
    {i j : Fin N} (h : componentIndex (keyEdges f) i = componentIndex (keyEdges f) j) :
    f i = f j := by
  have forward : ∀ d : ℕ, ∀ a b : Fin N, b.val - a.val = d → a ≤ b →
      componentIndex (keyEdges f) a = componentIndex (keyEdges f) b → f a = f b := by
    intro d
    induction d with
    | zero =>
      intro a b hd hab hc
      have : a = b := Fin.ext (by omega)
      simp [this]
    | succ d ih =>
      intro a b hd hab hc
      have hb : 0 < b.val := by omega
      let q : Fin N := ⟨b.val-1, by omega⟩
      have haq : a ≤ q := by change a.val ≤ b.val-1; omega
      have hqb : q ≤ b := by change b.val-1 ≤ b.val; omega
      have hqc : componentIndex (keyEdges f) q = componentIndex (keyEdges f) b :=
        le_antisymm (componentIndex_monotone _ hqb)
          (hc ▸ componentIndex_monotone _ haq)
      have haqc : componentIndex (keyEdges f) a = componentIndex (keyEdges f) q :=
        hc.trans hqc.symm
      have haqf : f a = f q := ih a q (by dsimp [q]; omega) haq haqc
      let e : Fin (N-1) := ⟨b.val-1, by omega⟩
      have hel : edgeLeft e = q := by apply Fin.ext; rfl
      have her : edgeRight e = b := by apply Fin.ext; dsimp [edgeRight, e]; omega
      have hem : e ∈ keyEdges f := by
        by_contra hn
        have hlt := componentIndex_lt_of_missing (keyEdges f) e hn
        rw [hel, her, hqc] at hlt
        exact (lt_irrefl _ hlt)
      exact haqf.trans (by simpa [hel, her] using (mem_keyEdges f e).mp hem)
  rcases le_total i j with hij | hji
  · exact forward (j.val-i.val) i j rfl hij h
  · exact (forward (i.val-j.val) j i rfl hji h.symm).symm

theorem componentIndex_keyEdges_eq_iff {α : Type*} [PartialOrder α]
    (f : Fin N → α) (hf : Monotone f) (i j : Fin N) :
    componentIndex (keyEdges f) i = componentIndex (keyEdges f) j ↔ f i = f j :=
  ⟨key_eq_of_componentIndex_eq f, componentIndex_eq_of_key_eq f hf⟩

/-- Component order records exactly the strict order of the monotone keys. -/
theorem componentIndex_keyEdges_lt_iff {α : Type*} [LinearOrder α]
    (f : Fin N → α) (hf : Monotone f) (i j : Fin N) :
    componentIndex (keyEdges f) i < componentIndex (keyEdges f) j ↔ f i < f j := by
  constructor
  · intro h
    have hij : i < j := lt_of_not_ge (fun hji => (not_lt_of_ge (componentIndex_monotone _ hji)) h)
    apply lt_of_le_of_ne (hf hij.le)
    intro heq
    exact (ne_of_lt h) ((componentIndex_keyEdges_eq_iff f hf i j).mpr heq)
  · intro h
    have hij : i < j := lt_of_not_ge (fun hji => (not_lt_of_ge (hf hji)) h)
    apply lt_of_le_of_ne (componentIndex_monotone _ hij.le)
    intro heq
    exact (ne_of_lt h) ((componentIndex_keyEdges_eq_iff f hf i j).mp heq)

/-- Sorting a lexicographic pair preserves an already monotone first coordinate. -/
theorem sort_pair_preserves_first {α β : Type*} [LinearOrder α] [LinearOrder β]
    (c : Fin N → α) (v : Fin N → β) (hc : Monotone c) (i : Fin N) :
    c (Tuple.sort (fun j => (toLex (c j, v j) : α ×ₗ β)) i) = c i := by
  let p := Tuple.sort (fun j => (toLex (c j, v j) : α ×ₗ β))
  have hcp : Monotone (c ∘ p) := by
    intro a b hab
    exact Prod.Lex.monotone_fst _ _
      (Tuple.monotone_sort (fun j => (toLex (c j, v j) : α ×ₗ β)) hab)
  have hh := Tuple.unique_monotone (σ := p) (τ := Equiv.refl _) hcp hc
  exact congrFun hh i

/-- The second coordinate becomes strictly ordered on equal-first-coordinate blocks. -/
theorem sort_pair_second_strict {α : Type*} [LinearOrder α]
    (c : Fin N → α) (π : Permutation N) (hc : Monotone c)
    {i j : Fin N} (hij : i < j) (heq : c i = c j) :
    π (Tuple.sort (fun q => (toLex (c q, π q) : α ×ₗ Fin N)) i) <
      π (Tuple.sort (fun q => (toLex (c q, π q) : α ×ₗ Fin N)) j) := by
  let p := Tuple.sort (fun q => (toLex (c q, π q) : α ×ₗ Fin N))
  have hkeys := Tuple.monotone_sort (fun q => (toLex (c q, π q) : α ×ₗ Fin N)) hij.le
  have hle : π (p i) ≤ π (p j) := by
    rcases Prod.Lex.toLex_le_toLex.mp hkeys with h | h
    · have hh : c (p i) = c (p j) :=
        (sort_pair_preserves_first c π hc i).trans
          (heq.trans (sort_pair_preserves_first c π hc j).symm)
      exact False.elim ((ne_of_lt h) hh)
    · exact h.2
  exact lt_of_le_of_ne hle (fun h => (ne_of_lt hij) (p.injective (π.injective h)))

/-- The generic deterministic relabelling identity, with explicit word-preserving graph. -/
theorem sort_relabel_componentSort {α : Type*} [LinearOrder α]
    (f : Fin N → α) (ρ : Permutation N) :
    Tuple.sort (f ∘ ρ) = componentSort (keyEdges (f ∘ Tuple.sort f))
      ((Tuple.sort f).trans ρ.symm) := by
  let s := Tuple.sort f
  let w := f ∘ s
  let G := keyEdges w
  let π := s.trans ρ.symm
  let c := componentIndex G
  let p := Tuple.sort (fun i => (toLex (c i, π i) : ℕ ×ₗ Fin N))
  have hc : Monotone c := componentIndex_monotone G
  have hw : Monotone w := Tuple.monotone_sort f
  have hwp (i : Fin N) : w (p i) = w i :=
    (componentIndex_keyEdges_eq_iff w hw (p i) i).mp (sort_pair_preserves_first c π hc i)
  have hwords (i : Fin N) : (f ∘ ρ) ((p.trans π) i) = w i := by
    change f (ρ (ρ.symm (s (p i)))) = w i
    simpa only [Equiv.apply_symm_apply, w, Function.comp_apply] using hwp i
  have hp : p.trans π = Tuple.sort (f ∘ ρ) := by
    apply Tuple.eq_sort_iff.mpr
    constructor
    · intro i j hij
      change (f ∘ ρ) ((p.trans π) i) ≤ (f ∘ ρ) ((p.trans π) j)
      rw [hwords, hwords]
      exact hw hij
    · intro i j hij heq
      have hw_eq : w i = w j := by simpa only [hwords] using heq
      have hc_eq : c i = c j := (componentIndex_keyEdges_eq_iff w hw i j).mpr hw_eq
      exact sort_pair_second_strict c π hc hij hc_eq
  exact hp.symm

@[simp] theorem keyEdges_sortedWord {k K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) : keyEdges (sortedWord ω) = shuffleEdges ω := by
  ext e
  simp [keyEdges, shuffleEdges]

/-- Concrete graph components are precisely the full-word ties. -/
theorem shuffle_componentIndex_eq_iff {k K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) (i j : Fin N) :
    componentIndex (shuffleEdges ω) i = componentIndex (shuffleEdges ω) j ↔
      sortedWord ω i = sortedWord ω j := by
  rw [← keyEdges_sortedWord ω]
  exact componentIndex_keyEdges_eq_iff (sortedWord ω) (Tuple.monotone_sort (rowWord ω)) i j

theorem shuffle_componentIndex_lt_iff {k K : ℕ} {cuts : TimeProfile.Cuts k N K}
    (ω : Sample cuts) (i j : Fin N) :
    componentIndex (shuffleEdges ω) i < componentIndex (shuffleEdges ω) j ↔
      sortedWord ω i < sortedWord ω j := by
  rw [← keyEdges_sortedWord ω]
  exact componentIndex_keyEdges_lt_iff (sortedWord ω) (Tuple.monotone_sort (rowWord ω)) i j

/-- The sorted full multiset is unchanged by relabelling original cards. -/
theorem sortedWord_relabel {k K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (ρ : Permutation N) (ω : Sample cuts) :
    sortedWord (sampleRelabel cuts ρ ω) = sortedWord ω := by
  change ((rowWord ω ∘ ρ) ∘ Tuple.sort (rowWord ω ∘ ρ)) = rowWord ω ∘ Tuple.sort (rowWord ω)
  exact Tuple.comp_perm_comp_sort_eq_comp_sort

@[simp] theorem shuffleEdges_relabel {k K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (ρ : Permutation N) (ω : Sample cuts) :
    shuffleEdges (sampleRelabel cuts ρ ω) = shuffleEdges ω := by
  unfold shuffleEdges
  rw [sortedWord_relabel]

/-- Exact relabelling covariance with stable ties and position-to-label orientation. -/
theorem stableSort_relabel {k K : ℕ} (cuts : TimeProfile.Cuts k N K)
    (ρ : Permutation N) (ω : Sample cuts) :
    stableSort (sampleRelabel cuts ρ ω) =
      componentSort (shuffleEdges ω) ((stableSort ω).trans ρ.symm) := by
  have hrows : rowWord (sampleRelabel cuts ρ ω) = rowWord ω ∘ ρ := by
    funext i
    exact rowWord_relabel cuts ρ ω i
  have hh := sort_relabel_componentSort (rowWord ω) ρ
  have hedges : keyEdges (rowWord ω ∘ Tuple.sort (rowWord ω)) = shuffleEdges ω :=
    keyEdges_sortedWord ω
  rw [hedges] at hh
  simpa only [stableSort, hrows] using hh

/-- Component normalization permutes positions only within their own component. -/
theorem componentSort_preserves_component (G : PathEdges N) (π : Permutation N) (i : Fin N) :
    componentIndex G (π.symm (componentSort G π i)) = componentIndex G i := by
  simpa only [componentSort, Equiv.trans_apply, Equiv.symm_apply_apply] using
    sort_pair_preserves_first (componentIndex G) π (componentIndex_monotone G) i

/-- Labels after normalization are strictly increasing inside each component. -/
theorem componentSort_increasing (G : PathEdges N) (π : Permutation N)
    {i j : Fin N} (hij : i < j) (heq : componentIndex G i = componentIndex G j) :
    componentSort G π i < componentSort G π j :=
  sort_pair_second_strict (componentIndex G) π (componentIndex_monotone G) hij heq

end RiffleLowerV2.Model
