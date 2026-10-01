import RiffleLowerV2.Thinning.PMFTools
import RiffleLowerV2.Thinning.Compat.SubsetTransform
import Contracts.v1.AdditionalFinite

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Thinning

/-- Image of a deterministic set under a uniform label permutation. -/
def permSubset {M : ℕ} (B : Finset (Fin M)) (σ : Permutation M) :
    Compat.Sample (Finset.univ : Finset (Fin M)) B.card :=
  ⟨B.map σ.toEmbedding, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by simp⟩⟩

/-- Constant fibre cardinalities prove the exact uniform-subset expectation. -/
theorem permutation_subset_expect {M : ℕ} (B : Finset (Fin M))
    (f : Compat.Sample (Finset.univ : Finset (Fin M)) B.card → ℝ) :
    expect (uniformPermutation M) (fun σ => f (permSubset B σ)) =
      (Compat.sampleLaw (Finset.univ : Finset (Fin M)) B.card (by simpa using Finset.card_le_univ B)).expect f := by
  letI : Nonempty (Compat.Sample (Finset.univ : Finset (Fin M)) B.card) :=
    ⟨⟨B, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩⟩
  change expect (PMF.uniformOfFintype (Permutation M)) (fun σ => f (permSubset B σ)) =
    (Compat.FiniteLaw.uniform (Compat.Sample (Finset.univ : Finset (Fin M)) B.card)).expect f
  have he := uniform_expect_of_equal_fibres (permSubset B) (g := f)
  have hf : ∀ b c : Compat.Sample (Finset.univ : Finset (Fin M)) B.card,
      Fintype.card {σ // permSubset B σ = b} = Fintype.card {σ // permSubset B σ = c} := by
    intro b c
    obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_map_finset_eq b.val c.val
      ((Finset.mem_powersetCard.mp b.property).2.trans (Finset.mem_powersetCard.mp c.property).2.symm)
    apply Fintype.card_congr ((Equiv.mulLeft ρ).subtypeEquiv (fun σ => ?_))
    change permSubset B σ = b ↔ permSubset B (ρ * σ) = c
    simp only [Subtype.ext_iff]
    have hc : (permSubset B (ρ * σ)).val = (permSubset B σ).val.map ρ.toEmbedding := by
      simp only [permSubset, Finset.map_map]
      rfl
    rw [hc, ← hρ]
    exact Finset.map_inj.symm
  rw [he (by intro b c; simpa only [Fintype.card_eq_nat_card] using hf b c), uniform_expect]
  change _ = (Compat.FiniteLaw.uniform _).expect f
  simp only [Compat.FiniteLaw.expect, Compat.FiniteLaw.uniform, ← Finset.mul_sum]
  ring

/-- All-positive transform with an arbitrary deterministic marked subset. -/
theorem permutation_intersection_transform {M : ℕ} (A B : Finset (Fin M))
    {s : ℝ} (hs : 0 < s) :
    expect (uniformPermutation M) (fun σ => s ^ (A ∩ B.map σ.toEmbedding).card) ≤
      (1 - (B.card : ℝ)/M + (B.card : ℝ)/M*s)^A.card := by
  have h := permutation_subset_expect B (fun S => s ^ (A ∩ S.val).card)
  change expect (uniformPermutation M) (fun σ => s ^ (A ∩ B.map σ.toEmbedding).card) = _ at h
  rw [h]
  simpa using Compat.sample_expect_pow_intersection_le Finset.univ A B.card
    (by simpa using Finset.card_le_univ B) (Finset.subset_univ _) hs

theorem map_initial_eq {M m : ℕ} (σ : Permutation M) :
    (Finset.univ.filter (fun i : Fin M => i.val < m)).map σ.toEmbedding =
      Finset.univ.filter (fun i : Fin M => (σ.symm i).val < m) := by
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro hi
    exact ⟨σ.symm i, hi, σ.apply_symm_apply i⟩

/-- Frozen permutation-law target, with every positive transform parameter. -/
theorem hypergeometricTransform : Targets.HypergeometricTransform := by
  intro M x m hM hx hm s hs
  let A := Finset.univ.filter (fun i : Fin M => i.val < x)
  let B := Finset.univ.filter (fun i : Fin M => i.val < m)
  have hA : A.card = x := by simpa [A, min_eq_right hx] using (Fin.card_filter_val_lt (n := M) (m := x))
  have hB : B.card = m := by simpa [B, min_eq_right hm] using (Fin.card_filter_val_lt (n := M) (m := m))
  have h := permutation_intersection_transform A B hs
  rw [hA, hB] at h
  convert h using 1
  congr 1
  funext σ
  congr 1
  congr 1
  rw [show B.map σ.toEmbedding = Finset.univ.filter (fun i : Fin M => (σ.symm i).val < m) from map_initial_eq σ]
  ext i
  simp [A]

end RiffleLowerV2.Thinning
