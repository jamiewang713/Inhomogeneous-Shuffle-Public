import RiffleUpperV2.FirstMoment.UniformClassDensity
import RiffleUpperV2.Shared.FiniteFibers

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization

section FiniteClasses
variable {k n d N : ℕ} (hk : 0 < k) (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Fin k → Finset (Fin n))
    (T C chi delta width : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1)
    (hchiK : chi ≤ 1/(k : ℝ)) (hwidth : 0 < width) (hd : (d : ℝ) ≤ T*logScale N)
local notation "Candidate" => RetainedAtPile hk N cuts hn R C chi delta hchiK
local notation "desc" => retainedDescriptor hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd
local notation "classWords" => classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd
local notation "classes" => retainedClasses hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd

/-- Sum the literal retained edge densities using their proved exact fiber sizes. -/
theorem retainedDensity_sum_le (c₀ : Fin k → ℤ) (slots : Finset ℤ) (U : ℝ)
    (hbound : ∀ t : Candidate, ((classWords t).card : ℝ)*
      anchoredDensity cuts (c₀ t.1) (R t.1) t.2.1.2.2 slots ≤ U) :
    (∑ t : Candidate, anchoredDensity cuts (c₀ t.1) (R t.1) t.2.1.2.2 slots) ≤
      ((classes).card : ℝ)*U := by
  apply sum_le_image_card_mul_of_fiber_bound desc
  intro t
  rw [← classPrefixes_card hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd t]
  exact hbound t

/-- The checked N^epsilon actual key count completes the retained-density sum. -/
theorem retainedDensity_sum_power (c₀ : Fin k → ℤ) (slots : Finset ℤ) (epsilon eta : ℝ)
    (hcount : ((classes).card : ℝ) ≤ (N : ℝ)^epsilon)
    (hbound : ∀ t : Candidate, ((classWords t).card : ℝ)*
      anchoredDensity cuts (c₀ t.1) (R t.1) t.2.1.2.2 slots ≤ (N : ℝ)^(-eta/2)) :
    (∑ t : Candidate, anchoredDensity cuts (c₀ t.1) (R t.1) t.2.1.2.2 slots) ≤
      (N : ℝ)^(epsilon-eta/2) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  apply (retainedDensity_sum_le hk hN cuts hn R T C chi delta width
    hchi hchi1 hchiK hwidth hd c₀ slots _ hbound).trans
  calc
    _ ≤ (N : ℝ)^epsilon*(N : ℝ)^(-eta/2) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hNp.le _)
    _ = _ := by rw [← Real.rpow_add hNp]; congr 1; ring

end FiniteClasses
end RiffleUpperV2.FirstMoment
