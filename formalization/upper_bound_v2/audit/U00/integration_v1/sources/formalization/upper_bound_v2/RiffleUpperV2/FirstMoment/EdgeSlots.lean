import RiffleUpperV2.FirstMoment.GraphMarginals

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open Anchor RiffleUpperV2.Localization

/-- The actual global edge slots, viewed as zero-based integer left ranks. -/
def edgeSlots (n : ℕ) : Finset ℤ :=
  Finset.univ.image (fun e : Fin (n-1) => (e.val : ℤ))

theorem edgeRank_injective (n : ℕ) :
    Function.Injective (fun e : Fin (n-1) => (e.val : ℤ)) := by
  intro a b h
  apply Fin.ext
  dsimp only at h
  exact_mod_cast h

@[simp] theorem edgeSlots_card (n : ℕ) : (edgeSlots n).card=n-1 := by
  rw [edgeSlots,Finset.card_image_of_injective _ (edgeRank_injective n)]
  simp

/-- Integer-slot sums exactly preserve the actual finite edge indexing. -/
theorem sum_edgeSlots (n : ℕ) (f : ℤ → ℝ) :
    (∑ m ∈ edgeSlots n, f m) = ∑ e : Fin (n-1), f e.val := by
  rw [edgeSlots,Finset.sum_image]
  intro a _ b _ h
  exact edgeRank_injective n h

@[simp] theorem anchoredDensity_edgeSlots {k n d : ℕ} (cuts : Cuts k n d)
    (c₀ : ℤ) (R : Finset (Fin n)) (x : Prefix k d) :
    anchoredDensity cuts c₀ R x (edgeSlots n) =
      ∑ e : Fin (n-1), anchoredEdgeProbability cuts c₀ R x e.val ^ 2 :=
  sum_edgeSlots n _

end RiffleUpperV2.FirstMoment
