import RiffleUpperV2.Localization.Definitions
import RiffleUpperV2.Hypergeometric.CylinderMean

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor Hypergeometric

/-- Singleton restrictions at used future columns, with unrestricted remaining columns. -/
def prefixDigits {k d : ℕ} (x : Prefix k d) (j : Fin d) : Finset (Fin k) :=
  if h : j.val < x.1.val then {x.2.get ⟨j.val,h⟩} else Finset.univ

theorem prefixRows_eq_cylinderSet {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (ω : Sample cuts) :
    prefixRows R x ω = cylinderSet cuts R (prefixDigits x) ω := by
  ext r
  simp only [prefixRows, cylinderSet, RiffleLowerV2.Thinning.intersectionWithin,
    Finset.mem_filter, Finset.mem_univ, true_and]
  apply and_congr_right
  intro _
  rw [RiffleLowerV2.Thinning.prefix_coordinates_iff]
  constructor
  · intro he j
    unfold prefixDigits
    split_ifs with hj
    · simp only [Finset.mem_singleton]
      exact he ⟨j.val,hj⟩
    · exact Finset.mem_univ _
  · intro he j
    simpa [prefixDigits, prefixColumn, j.isLt, TimeProfile.sampleEntry, Fin.castLE] using he (prefixColumn x j)

theorem prefixDigits_mass {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (x : Prefix k d) : cylinderMass cuts (prefixDigits x) = prefixMass cuts x := by
  change _ = RiffleLowerV2.prefixMass cuts x
  rw [← RiffleLowerV2.Thinning.prefixColumnFraction_product]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j.val < x.1.val
  · simp [prefixDigits, RiffleLowerV2.Thinning.prefixColumnFraction, hj, allowedCount]
  · simp [prefixDigits, RiffleLowerV2.Thinning.prefixColumnFraction, hj, hn.ne']

theorem prefixDigits_mean {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) :
    cylinderMean cuts R (prefixDigits x) = anchoredMean cuts R x := by
  unfold cylinderMean anchoredMean
  rw [prefixDigits_mass cuts hn]

theorem prefixRows_expect {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) :
    expect (fixedCountPMF cuts) (fun ω => ((prefixRows R x ω).card : ℝ)) =
      anchoredMean cuts R x := by
  simp_rw [prefixRows_eq_cylinderSet cuts]
  change RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
    (fun ω => (cylinderCount cuts R (prefixDigits x) ω : ℝ)) = _
  rw [← cylinderMean_eq_expect, prefixDigits_mean cuts hn]

/-- Actual anchored prefix concentration, including means strictly below one. -/
theorem prefixRows_tail {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (x : Prefix k d) {t : ℝ} (ht : 0 < t) :
    probability (fixedCountPMF cuts)
      (fun ω => t ≤ |((prefixRows R x ω).card : ℝ) - anchoredMean cuts R x|) ≤
      2 * Real.exp (-t^2 / (4*(anchoredMean cuts R x + t))) := by
  have h := (anchorCylinderTail cuts R (prefixDigits x) ht).1
  simpa only [cylinderCount, ← prefixRows_eq_cylinderSet cuts,
    prefixDigits_mean cuts hn] using h

end RiffleUpperV2.Localization
