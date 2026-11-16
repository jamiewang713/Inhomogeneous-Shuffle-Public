import RiffleUpperV2.Shared.Model

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2

/-- A bound on fiber size times each summand bounds the entire sum by the
number of nonempty fibers times the same bound. Neither summands nor the
bound need be nonnegative. -/
theorem sum_le_image_card_mul_of_fiber_bound {I C : Type*} [Fintype I]
    [DecidableEq C] (key : I → C) (f : I → ℝ) (U : ℝ)
    (h : ∀ i, ((Finset.univ.filter (fun j => key j = key i)).card : ℝ) * f i ≤ U) :
    (∑ i, f i) ≤ ((Finset.univ.image key).card : ℝ) * U := by
  classical
  have hf (c : C) (hc : c ∈ Finset.univ.image key) :
      (∑ i ∈ Finset.univ.filter (fun j => key j = c), f i) ≤ U := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    let s := Finset.univ.filter (fun j => key j = c)
    have hs : 0 < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    have hsum : (s.card : ℝ) * (∑ j ∈ s, f j) ≤ (s.card : ℝ) * U := by
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ j ∈ s, U := Finset.sum_le_sum (fun j hj => by
          have he : key j = c := (Finset.mem_filter.mp hj).2
          simpa only [he] using h j)
        _ = _ := by simp
    exact (mul_le_mul_iff_right₀ hs).mp hsum
  calc
    _ = ∑ c ∈ Finset.univ.image key,
        ∑ i ∈ Finset.univ.filter (fun j => key j = c), f i :=
      (Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, rfl⟩) f).symm
    _ ≤ ∑ c ∈ Finset.univ.image key, U := Finset.sum_le_sum hf
    _ = _ := by simp

end RiffleUpperV2
