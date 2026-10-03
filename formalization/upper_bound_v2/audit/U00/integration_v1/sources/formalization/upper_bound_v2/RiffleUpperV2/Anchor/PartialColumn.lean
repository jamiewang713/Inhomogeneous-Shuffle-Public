import RiffleUpperV2.Anchor.Definitions
import RiffleUpperV2.Hypergeometric.Sampling

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 300000
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile RiffleLowerV2.Thinning RiffleLowerV2.Thinning.Compat

/-- A relabeling of unobserved labels can map two equally sized residual sets
while fixing every exposed label. -/
theorem exists_perm_fix_map {α : Type*} [Fintype α] [DecidableEq α]
    (A B C : Finset α) (hB : Disjoint A B) (hC : Disjoint A C)
    (hc : B.card = C.card) :
    ∃ σ : Equiv.Perm α, (∀ a ∈ A, σ a = a) ∧ B.map σ.toEmbedding = C := by
  let p : α → Prop := fun a => a ∉ A
  have hb (a : α) (ha : a ∈ B) : p a := fun h => (Finset.disjoint_left.mp hB h ha)
  have hd (a : α) (ha : a ∈ C) : p a := fun h => (Finset.disjoint_left.mp hC h ha)
  have he : (B.subtype p).card = (C.subtype p).card := by
    simpa [Finset.card_subtype, Finset.filter_eq_self.mpr hb,
      Finset.filter_eq_self.mpr hd] using hc
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq (B.subtype p) (C.subtype p) he
  refine ⟨Equiv.Perm.ofSubtype τ, ?_, ?_⟩
  · intro a ha
    exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (not_not.mpr ha)
  · have hm := congrArg (fun S : Finset {a // p a} =>
        S.map (Function.Embedding.subtype p)) hτ
    rw [Finset.map_map, Finset.subtype_map_of_mem hd] at hm
    rw [← Finset.subtype_map_of_mem hb, Finset.map_map]
    convert hm using 1
    congr 1
    ext a
    exact Equiv.Perm.ofSubtype_apply_coe τ a

/-- Fixed values on an explicitly exposed row set. -/
def columnFiber {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (c₀ : ColumnAssignments cuts j) :
    ColumnAssignments cuts j → Prop := fun c => ∀ r ∈ A, c.val r = c₀.val r

def residualAllowed {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    Finset (Fin n) := (Finset.univ.filter fun r => c.val r ∈ D) \ A

def residualMarked {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j) : ℕ :=
  Hypergeometric.allowedCount cuts j D - (A.filter fun r => c₀.val r ∈ D).card

theorem residualAllowed_subset {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c : ColumnAssignments cuts j) :
    residualAllowed A D c ⊆ Finset.univ \ A := by
  intro r hr
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, (Finset.mem_sdiff.mp hr).2⟩

theorem residualAllowed_card {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c₀ c : ColumnAssignments cuts j)
    (hc : columnFiber A c₀ c) :
    (residualAllowed A D c).card = residualMarked A D c₀ := by
  have hi : (Finset.univ.filter fun r => c.val r ∈ D) ∩ A =
      A.filter (fun r => c₀.val r ∈ D) := by
    ext r
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hr, ha⟩
      exact ⟨ha, by simpa only [hc r ha] using hr⟩
    · rintro ⟨ha, hr⟩
      exact ⟨by simpa only [hc r ha] using hr, ha⟩
  have hs := Finset.card_sdiff_add_card_inter
    (Finset.univ.filter fun r => c.val r ∈ D) A
  rw [hi, Hypergeometric.allowed_card D c] at hs
  unfold residualAllowed residualMarked
  omega

def residualSubset {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (c : {c : ColumnAssignments cuts j // columnFiber A c₀ c}) :
    Compat.Sample (Finset.univ \ A) (residualMarked A D c₀) :=
  ⟨residualAllowed A D c.val,
    Finset.mem_powersetCard.mpr ⟨residualAllowed_subset A D c.val,
      residualAllowed_card A D c₀ c.val c.property⟩⟩

theorem residualMarked_le {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j) :
    residualMarked A D c₀ ≤ (Finset.univ \ A).card := by
  rw [← residualAllowed_card A D c₀ c₀ (fun _ _ => rfl)]
  exact Finset.card_le_card (residualAllowed_subset A D c₀)

private theorem fix_iff {α : Type*} [DecidableEq α] (A : Finset α)
    (σ : Equiv.Perm α) (hσ : ∀ a ∈ A, σ a = a) (r : α) :
    σ.symm r ∈ A ↔ r ∈ A := by
  constructor
  · intro h
    have hh := hσ (σ.symm r) h
    rw [σ.apply_symm_apply] at hh
    exact hh.symm ▸ h
  · intro h
    have hh := hσ r h
    have hs : σ.symm r = r := by
      calc
        σ.symm r = σ.symm (σ r) := congrArg σ.symm hh.symm
        _ = r := σ.symm_apply_apply r
    simpa only [hs] using h

private theorem columnFiber_relabel {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (c₀ c : ColumnAssignments cuts j)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a ∈ A, σ a = a) :
    columnFiber A c₀ c ↔ columnFiber A c₀ (columnRelabel σ c) := by
  have hs (r : Fin n) (hr : r ∈ A) : σ.symm r = r := by
    calc
      σ.symm r = σ.symm (σ r) := congrArg σ.symm (hσ r hr).symm
      _ = r := σ.symm_apply_apply r
  constructor <;> intro hc r hr
  · change c.val (σ.symm r) = c₀.val r
    rw [hs r hr]
    exact hc r hr
  · have hh := hc r hr
    change c.val (σ.symm r) = c₀.val r at hh
    rwa [hs r hr] at hh

private theorem residualAllowed_relabel {k n d : ℕ} {cuts : Cuts k n d} {j : Fin d}
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c : ColumnAssignments cuts j)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ a ∈ A, σ a = a) :
    residualAllowed A D (columnRelabel σ c) =
      (residualAllowed A D c).map σ.toEmbedding := by
  have ha : A.map σ.toEmbedding = A := by
    ext r
    simp only [Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨v,hv,rfl⟩
      simpa only [hσ v hv] using hv
    · intro hr
      exact ⟨r,hr,hσ r hr⟩
  change (Hypergeometric.allowedSubset D (columnRelabel σ c)).val \ A =
    ((Hypergeometric.allowedSubset D c).val \ A).map σ.toEmbedding
  rw [Hypergeometric.allowedSubset_relabel, Finset.map_sdiff, ha]

/-- Exact uniform residual marked set after revealing actual digit values on A.
No conditional sampling law is assumed by the caller. -/
theorem partialColumnUniform {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (A : Finset (Fin n)) (D : Finset (Fin k)) (c₀ : ColumnAssignments cuts j)
    (f : Compat.Sample (Finset.univ \ A) (residualMarked A D c₀) → ℝ) :
    letI : Nonempty {c : ColumnAssignments cuts j // columnFiber A c₀ c} :=
      ⟨⟨c₀, fun _ _ => rfl⟩⟩
    expect (PMF.uniformOfFintype {c : ColumnAssignments cuts j // columnFiber A c₀ c})
      (fun c => f (residualSubset A D c₀ c)) =
    (sampleLaw (Finset.univ \ A) (residualMarked A D c₀)
      (residualMarked_le A D c₀)).expect f := by
  letI : Nonempty {c : ColumnAssignments cuts j // columnFiber A c₀ c} :=
    ⟨⟨c₀, fun _ _ => rfl⟩⟩
  letI : Nonempty (Compat.Sample (Finset.univ \ A) (residualMarked A D c₀)) :=
    ⟨residualSubset A D c₀ ⟨c₀, fun _ _ => rfl⟩⟩
  have hf : ∀ b c : Compat.Sample (Finset.univ \ A) (residualMarked A D c₀),
      Fintype.card {v : {c : ColumnAssignments cuts j // columnFiber A c₀ c} //
        residualSubset A D c₀ v = b} =
      Fintype.card {v : {c : ColumnAssignments cuts j // columnFiber A c₀ c} //
        residualSubset A D c₀ v = c} := by
    intro b c
    have hd (u : Compat.Sample (Finset.univ \ A) (residualMarked A D c₀)) :
        Disjoint A u.val := by
      apply Finset.disjoint_left.mpr
      intro r hr hu
      exact (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp u.property).1 hu)).2 hr
    obtain ⟨σ,hσ,hmap⟩ := exists_perm_fix_map A b.val c.val (hd b) (hd c)
      ((Finset.mem_powersetCard.mp b.property).2.trans
        (Finset.mem_powersetCard.mp c.property).2.symm)
    let e : {c : ColumnAssignments cuts j // columnFiber A c₀ c} ≃
        {c : ColumnAssignments cuts j // columnFiber A c₀ c} :=
      (columnRelabelEquiv (cuts := cuts) (j := j) σ).subtypeEquiv
        (fun v => columnFiber_relabel A c₀ v σ hσ)
    apply Fintype.card_congr (e.subtypeEquiv (fun v => ?_))
    change residualSubset A D c₀ v = b ↔ residualSubset A D c₀ (e v) = c
    simp only [Subtype.ext_iff]
    change residualAllowed A D v.val = b.val ↔
      residualAllowed A D (columnRelabel σ v.val) = c.val
    rw [residualAllowed_relabel A D v.val σ hσ, ← hmap]
    exact Finset.map_inj.symm
  have he := uniform_expect_of_equal_fibres
    (Ω := {c : ColumnAssignments cuts j // columnFiber A c₀ c})
    (Γ := Compat.Sample (Finset.univ \ A) (residualMarked A D c₀))
    (residualSubset (cuts := cuts) (j := j) A D c₀)
    (by intro b c; simpa only [Fintype.card_eq_nat_card] using hf b c) f
  trans expect (PMF.uniformOfFintype
    (Compat.Sample (Finset.univ \ A) (residualMarked A D c₀))) f
  · exact he
  · trans (∑ s, f s) / (Fintype.card
      (Compat.Sample (Finset.univ \ A) (residualMarked A D c₀)) : ℝ)
    · exact uniform_expect f
    · change _ = (FiniteLaw.uniform _).expect f
      simp only [FiniteLaw.expect, FiniteLaw.uniform, ← Finset.mul_sum]
      ring

end RiffleUpperV2.Anchor
