import RiffleLowerV2.Thinning.PMFTools
import RiffleLowerV2.Thinning.Compat.SubsetTransform

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning
open TimeProfile

/-- Relabel a fixed-histogram column by a permutation of the row labels. -/
def columnRelabel {k N K : ℕ} {cuts : Cuts k N K} {j : Fin K}
    (σ : Permutation N) (c : ColumnAssignments cuts j) : ColumnAssignments cuts j :=
  ⟨fun i => c.val (σ.symm i), by
    intro a
    have h := Fintype.card_congr
      (σ.symm.subtypeEquiv (p := fun i => c.val (σ.symm i) = a)
        (q := fun i => c.val i = a) (fun _ => Iff.rfl))
    rw [Fintype.card_subtype, Fintype.card_subtype] at h
    exact h.trans (c.property a)⟩

/-- Relabeling preserves the entire assignment space, not only one digit fiber. -/
def columnRelabelEquiv {k N K : ℕ} {cuts : Cuts k N K} {j : Fin K}
    (σ : Permutation N) : ColumnAssignments cuts j ≃ ColumnAssignments cuts j where
  toFun := columnRelabel σ
  invFun := columnRelabel σ.symm
  left_inv c := by
    apply Subtype.ext
    funext i
    simp [columnRelabel]
  right_inv c := by
    apply Subtype.ext
    funext i
    simp [columnRelabel]

def columnDigitSubset {k N K : ℕ} {cuts : Cuts k N K} {j : Fin K}
    (a : Fin k) (c : ColumnAssignments cuts j) :
    Compat.Sample (Finset.univ : Finset (Fin N)) (cuts.count j a) :=
  ⟨Finset.univ.filter (fun i => c.val i = a),
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, c.property a⟩⟩

theorem columnDigitSubset_relabel {k N K : ℕ} {cuts : Cuts k N K} {j : Fin K}
    (σ : Permutation N) (a : Fin k) (c : ColumnAssignments cuts j) :
    (columnDigitSubset a (columnRelabel σ c)).val =
      (columnDigitSubset a c).val.map σ.toEmbedding := by
  ext i
  change i ∈ (Finset.univ.filter (fun i => c.val (σ.symm i) = a)) ↔
    i ∈ (Finset.univ.filter (fun i => c.val i = a)).map σ.toEmbedding
  simp only [Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · intro hi
    exact ⟨σ.symm i, hi, σ.apply_symm_apply i⟩
  · rintro ⟨v, hv, rfl⟩
    simpa using hv

theorem column_count_le {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) (a : Fin k) :
    cuts.count j a ≤ N := by
  calc
    cuts.count j a ≤ ∑ b, cuts.count j b :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    _ = N := cuts.sum_count j

/-- Every selected digit fiber has the actual uniform fixed-size subset law. -/
theorem column_subset_expect {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) (a : Fin k)
    (f : Compat.Sample (Finset.univ : Finset (Fin N)) (cuts.count j a) → ℝ) :
    expect (columnPMF cuts j) (fun c => f (columnDigitSubset a c)) =
      (Compat.sampleLaw (Finset.univ : Finset (Fin N)) (cuts.count j a)
        (by simpa using column_count_le cuts j a)).expect f := by
  let c0 : ColumnAssignments cuts j := Classical.choice inferInstance
  letI : Nonempty (Compat.Sample (Finset.univ : Finset (Fin N)) (cuts.count j a)) :=
    ⟨columnDigitSubset a c0⟩
  change expect (PMF.uniformOfFintype (ColumnAssignments cuts j))
      (fun c => f (columnDigitSubset a c)) =
    (Compat.FiniteLaw.uniform _).expect f
  have he := uniform_expect_of_equal_fibres (columnDigitSubset (cuts := cuts) (j := j) a)
    (g := f)
  have hf : ∀ b c : Compat.Sample (Finset.univ : Finset (Fin N)) (cuts.count j a),
      Fintype.card {v : ColumnAssignments cuts j // columnDigitSubset a v = b} =
        Fintype.card {v : ColumnAssignments cuts j // columnDigitSubset a v = c} := by
    intro b c
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq b.val c.val
      ((Finset.mem_powersetCard.mp b.property).2.trans
        (Finset.mem_powersetCard.mp c.property).2.symm)
    apply Fintype.card_congr ((columnRelabelEquiv (cuts := cuts) (j := j) σ).subtypeEquiv
      (fun v => ?_))
    change columnDigitSubset a v = b ↔ columnDigitSubset a (columnRelabel σ v) = c
    simp only [Subtype.ext_iff]
    rw [columnDigitSubset_relabel, ← hσ]
    exact Finset.map_inj.symm
  rw [he (by intro b c; simpa only [Fintype.card_eq_nat_card] using hf b c), uniform_expect]
  simp only [Compat.FiniteLaw.expect, Compat.FiniteLaw.uniform, ← Finset.mul_sum]
  ring

/-- The one-step transform for the actual shared fixed-histogram column law. -/
theorem column_intersection_transform {k N K : ℕ} (cuts : Cuts k N K)
    (j : Fin K) (a : Fin k) (A : Finset (Fin N)) {s : ℝ} (hs : 0 < s) :
    expect (columnPMF cuts j)
      (fun c => s ^ (A ∩ (Finset.univ.filter (fun i => c.val i = a))).card) ≤
      (1 - (cuts.count j a : ℝ) / N + (cuts.count j a : ℝ) / N * s) ^ A.card := by
  have h := column_subset_expect cuts j a (fun S => s ^ (A ∩ S.val).card)
  change expect (columnPMF cuts j)
    (fun c => s ^ (A ∩ (Finset.univ.filter (fun i => c.val i = a))).card) = _ at h
  rw [h]
  simpa using Compat.sample_expect_pow_intersection_le Finset.univ A (cuts.count j a)
    (by simpa using column_count_le cuts j a) (Finset.subset_univ _) hs

end RiffleLowerV2.Thinning
