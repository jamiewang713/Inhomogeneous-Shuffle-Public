import RiffleUpperV2.Shared.FiniteFibers

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2

/-- Count an active subset by a uniform bound for each fiber of its key. -/
theorem card_le_image_card_mul_of_fiber_bound {I C : Type*} [Fintype I]
    [DecidableEq C] (key : I → C) (active : Finset I) (L : ℕ)
    (h : ∀ c ∈ Finset.univ.image key, (active.filter (fun i => key i = c)).card ≤ L) :
    active.card ≤ (Finset.univ.image key).card * L := by
  classical
  calc
    active.card = ∑ c ∈ Finset.univ.image key,
        (active.filter (fun i => key i = c)).card :=
      Finset.card_eq_sum_card_fiberwise (fun i _ =>
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    _ ≤ ∑ c ∈ Finset.univ.image key, L := Finset.sum_le_sum h
    _ = _ := by simp

end RiffleUpperV2
