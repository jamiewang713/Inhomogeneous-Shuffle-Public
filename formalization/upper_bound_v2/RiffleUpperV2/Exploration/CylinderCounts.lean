import RiffleUpperV2.Exploration.AllCylinders
import RiffleUpperV2.Anchor.CylinderExtension
import RiffleUpperV2.Exploration.Positions

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open Hypergeometric Anchor RiffleUpperV2.Localization TimeProfile

@[simp] theorem prefixCylinder_count {k n K : ℕ} (cuts : Cuts k n K)
    (x : Prefix k K) (ω : Sample cuts) :
    cylinderCount cuts Finset.univ (prefixDigits x) ω = prefixCount x ω := by
  unfold cylinderCount
  rw [← prefixRows_eq_cylinderSet cuts]
  rfl

@[simp] theorem prefixCylinder_mean {k n K : ℕ} (cuts : Cuts k n K) (hn : 0 < n)
    (x : Prefix k K) : cylinderMean cuts Finset.univ (prefixDigits x) = prefixMean cuts x := by
  unfold cylinderMean
  rw [prefixDigits_mass cuts hn]
  simp [RiffleLowerV2.prefixMean]

def prefixLaterDigits {k K : ℕ} (x : Prefix k K) (j : Fin K) (a : Fin k) :=
  Function.update (prefixDigits x) j {a}

theorem prefixLaterCylinder_count {k n L : ℕ} (cuts : Cuts k n (L+1))
    (x : Prefix k (L+1)) (j : Fin (L+1)) (a : Fin k) (hj : x.1.val ≤ j.val) (ω : Sample cuts) :
    cylinderCount cuts Finset.univ (prefixLaterDigits x j a) ω = prefixLaterCount cuts x j a ω := by
  unfold cylinderCount prefixLaterDigits
  rw [cylinderSet_update_univ cuts Finset.univ _ j {a} (by simp [prefixDigits, not_lt.mpr hj]),
    ← prefixRows_eq_cylinderSet cuts]
  congr 1
  ext r
  simp only [Anchor.prefixRows, prefixLaterCount, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton, RiffleLowerV2.rowWord_get]

theorem prefixLaterCylinder_mean {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (x : Prefix k (L+1)) (j : Fin (L+1)) (a : Fin k) (hj : x.1.val ≤ j.val) :
    cylinderMean cuts Finset.univ (prefixLaterDigits x j a) =
      prefixMean cuts x * ((cuts.count j a : ℝ)/n) := by
  unfold cylinderMean prefixLaterDigits
  rw [cylinderMass_update_univ cuts hn _ j {a} (by simp [prefixDigits, not_lt.mpr hj]),
    prefixDigits_mass cuts hn]
  simp only [allowedCount, Finset.sum_singleton, Finset.card_univ, Fintype.card_fin,
    RiffleLowerV2.prefixMean]
  ring

def outsideDigits {k L : ℕ} (p : Fin k) (j : Fin (L+1)) (a : Fin k) :=
  Function.update (singleDigits 0 (Finset.univ.erase p)) j {a}

theorem outsideCylinder_count {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (j : Fin (L+1)) (a : Fin k) (hj : 0 < j.val) (ω : Sample cuts) :
    cylinderCount cuts Finset.univ (outsideDigits p j a) ω = outsideCount cuts p j a ω := by
  have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
  unfold cylinderCount outsideDigits
  rw [cylinderSet_update_univ cuts Finset.univ _ j {a}
    (by simp [singleDigits, Function.update_of_ne hj0]), singleDigits_set]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Finset.mem_erase, and_true, RiffleLowerV2.rowWord_get, ne_comm]

theorem allowedCount_erase {k n K : ℕ} (cuts : Cuts k n K) (j : Fin K) (a : Fin k) :
    allowedCount cuts j (Finset.univ.erase a) = n-cuts.count j a := by
  unfold allowedCount
  have hh := Finset.sum_erase_add (Finset.univ : Finset (Fin k)) (cuts.count j) (Finset.mem_univ a)
  rw [cuts.sum_count] at hh
  omega

theorem outsideCylinder_mean {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (p : Fin k) (j : Fin (L+1)) (a : Fin k) (hj : 0 < j.val) :
    cylinderMean cuts Finset.univ (outsideDigits p j a) =
      (n-pileSize cuts p : ℕ) * ((cuts.count j a : ℝ)/n) := by
  have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
  unfold cylinderMean outsideDigits
  rw [cylinderMass_update_univ cuts hn _ j {a}
    (by simp [singleDigits, Function.update_of_ne hj0]), singleDigits_mass cuts hn]
  rw [allowedCount_erase]
  simp only [allowedCount, Finset.sum_singleton,
    Finset.card_univ, Fintype.card_fin, pileSize]
  field_simp

/-- Counts/probabilities at one digit remain in [0,1], including zero piles. -/
theorem digitFraction_bounds {k n K : ℕ} (cuts : Cuts k n K) (j : Fin K) (a : Fin k) :
    0 ≤ (cuts.count j a : ℝ)/n ∧ (cuts.count j a : ℝ)/n ≤ 1 := by
  refine ⟨by positivity, div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)⟩
  exact_mod_cast ((Finset.single_le_sum (fun q _ => Nat.zero_le (cuts.count j q))
    (Finset.mem_univ a)).trans_eq (cuts.sum_count j))

theorem allCylinder_prefix_and_later {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    {ξ : ℝ} {ω : Sample cuts} (h : allCylinderEvent cuts ξ ω)
    (x : Prefix k (L+1)) (hx : (n : ℝ)^ξ ≤ prefixMean cuts x) :
    |(prefixCount x ω : ℝ)-prefixMean cuts x| ≤ (prefixMean cuts x)^((2:ℝ)/3) ∧
    ∀ j a, x.1.val ≤ j.val →
      |(prefixLaterCount cuts x j a ω : ℝ)-(prefixCount x ω : ℝ)*((cuts.count j a : ℝ)/n)| ≤
        (prefixMean cuts x)^((2:ℝ)/3) := by
  have hpx := allCylinderEvent_bound cuts h (prefixDigits x) hx (by rw [prefixCylinder_mean cuts hn])
  rw [prefixCylinder_count, prefixCylinder_mean cuts hn] at hpx
  have ht : 0 ≤ (prefixMean cuts x)^((2:ℝ)/3) := Real.rpow_nonneg
    (RiffleLowerV2.Thinning.prefixMean_nonneg cuts x) _
  refine ⟨by linarith, ?_⟩
  intro j a hj
  have hp := digitFraction_bounds cuts j a
  have hm : cylinderMean cuts Finset.univ (prefixLaterDigits x j a) ≤ prefixMean cuts x := by
    rw [prefixLaterCylinder_mean cuts hn x j a hj]
    exact mul_le_of_le_one_right (RiffleLowerV2.Thinning.prefixMean_nonneg cuts x) hp.2
  have hl := allCylinderEvent_bound cuts h (prefixLaterDigits x j a) hx hm
  rw [prefixLaterCylinder_count cuts x j a hj, prefixLaterCylinder_mean cuts hn x j a hj] at hl
  have he : (prefixLaterCount cuts x j a ω : ℝ)-(prefixCount x ω : ℝ)*((cuts.count j a : ℝ)/n) =
      ((prefixLaterCount cuts x j a ω : ℝ)-prefixMean cuts x*((cuts.count j a : ℝ)/n)) +
      ((prefixMean cuts x-(prefixCount x ω : ℝ))*((cuts.count j a : ℝ)/n)) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_sub_comm (prefixMean cuts x), abs_of_nonneg hp.1]
  have hh := mul_le_mul_of_nonneg_right hpx hp.1
  have hh' := mul_le_of_le_one_right (by linarith : 0 ≤ (prefixMean cuts x)^((2:ℝ)/3)/2) hp.2
  linarith

theorem allCylinder_outside {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    {ξ : ℝ} (hξ : ξ ≤ 1) {ω : Sample cuts} (h : allCylinderEvent cuts ξ ω)
    (p : Fin k) (j : Fin (L+1)) (a : Fin k) (hj : 0 < j.val) :
    |(outsideCount cuts p j a ω : ℝ)-(n-pileSize cuts p : ℕ)*((cuts.count j a : ℝ)/n)| ≤
      (n : ℝ)^((2:ℝ)/3) := by
  have hb : (n : ℝ)^ξ ≤ n := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hξ
  have hm : cylinderMean cuts Finset.univ (outsideDigits p j a) ≤ n := by
    unfold cylinderMean
    simpa using mul_le_of_le_one_right (Nat.cast_nonneg n) (cylinderMass_bounds cuts _).2
  have hh := allCylinderEvent_bound cuts h (outsideDigits p j a) hb hm
  rw [outsideCylinder_count cuts p j a hj, outsideCylinder_mean cuts hn p j a hj] at hh
  have ht := Real.rpow_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n) ((2:ℝ)/3)
  linarith

end RiffleUpperV2.Exploration
