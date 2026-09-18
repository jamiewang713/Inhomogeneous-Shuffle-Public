import RiffleProfiles.Estimates
import RiffleTimeProfile.Ambient

/-!
Frozen S04–S05: finite crossing and fluctuation comparisons for the
existing TimeProfile product masses. These statements make no claim
about a stochastic variance or a shuffle expectation.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace RiffleProfiles

variable {k K : ℕ}

private theorem prefix_mass_split (N : ℕ) (p : Fin K → TimeProfile.Simplex k)
    (x : Fin K → Fin k) {a b : ℕ} (hab : a ≤ b) :
    TimeProfile.prefixMass N p x b = TimeProfile.prefixMass N p x a *
      ∏ j ∈ TimeProfile.positions K a b, TimeProfile.prob (p j) (x j) := by
  have hs : TimeProfile.positions K 0 b =
      TimeProfile.positions K 0 a ∪ TimeProfile.positions K a b := by
    ext j
    simp only [TimeProfile.positions, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_union]
    omega
  have hd : Disjoint (TimeProfile.positions K 0 a) (TimeProfile.positions K a b) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [TimeProfile.positions, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    omega
  simp only [TimeProfile.prefixMass, TimeProfile.prefixWeight, hs, Finset.prod_union hd]
  ring

/-- S04: a positive crossing bounds the entire continuation mass. -/
theorem source_sideMaximum_ge_prefixMass (N : ℕ) (p : Fin K → TimeProfile.Simplex k)
    (x : Fin K → Fin k) (side : TimeProfile.Simplex k → Fin k → ℝ)
    {w v : ℕ} {chi : ℝ} (hN : 2 ≤ N) (hchi : 0 < chi)
    (_hwv : w ≤ v) (_hvK : v ≤ K) (hlegal : TimeProfile.LegalPrefix p x v)
    {j : Fin K} (hj : j ∈ TimeProfile.positions K w v)
    (hcross : chi ≤ side (p j) (x j)) :
    chi * TimeProfile.prefixMass N p x v ≤ TimeProfile.sideMaximum N p x w v side := by
  have hjw : w ≤ j.val := (Finset.mem_filter.mp hj).2.1
  have hjv : j.val < v := (Finset.mem_filter.mp hj).2.2
  have hlegalj : TimeProfile.LegalPrefix p x j.val :=
    fun i hi => hlegal i (hi.trans hjv)
  have hearlier : 0 < TimeProfile.prefixMass N p x j.val :=
    TimeProfile.prefixMass_pos N p x (by omega) hlegalj
  have hside_eq : TimeProfile.sideMass N p x w side j =
      TimeProfile.prefixMass N p x j.val * side (p j) (x j) := by
    rw [TimeProfile.sideMass, ← prefix_mass_split N p x hjw]
  have hside : chi * TimeProfile.prefixMass N p x j.val ≤
      TimeProfile.sideMass N p x w side j := by
    rw [hside_eq]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hcross hearlier.le
  have hcontinuation := prefix_mass_split N p x hjv.le
  have hlower := side_mass_ge_continuation (TimeProfile.positions K j.val v)
    (fun i => TimeProfile.prob (p i) (x i)) hchi hearlier.le
    (fun _ _ => TimeProfile.prob_nonneg _ _)
    (fun _ _ => TimeProfile.prob_le_one _ _) hside
  rw [← hcontinuation] at hlower
  have hmass : 0 < TimeProfile.prefixMass N p x v :=
    TimeProfile.prefixMass_pos N p x (by omega) hlegal
  have hsidepos : 0 < TimeProfile.sideMass N p x w side j :=
    (mul_pos hchi hmass).trans_le hlower
  have hsup : (Real.toNNReal (TimeProfile.sideMass N p x w side j) : ℝ) ≤
      TimeProfile.sideMaximum N p x w v side := by
    exact_mod_cast (Finset.le_sup (s := TimeProfile.positions K w v)
      (f := fun i => Real.toNNReal (TimeProfile.sideMass N p x w side i)) hj)
  rw [Real.coe_toNNReal _ hsidepos.le] at hsup
  exact hlower.trans hsup

private theorem logExponent_sqrt_of_pos (N : ℕ) {z : ℝ} (hz : 0 < z) :
    TimeProfile.logExponent N (Real.sqrt z) =
      ((Real.log z / (2 * TimeProfile.logScale N) : ℝ) : WithBot ℝ) := by
  rw [TimeProfile.logExponent, if_neg (ne_of_gt (Real.sqrt_pos.2 hz)), Real.log_sqrt hz.le]
  congr 1
  ring

/-- S05: the exact ambient mass error remains in the finite exponent bound. -/
theorem source_fluctuation_comparison (N : ℕ) (p : Fin K → TimeProfile.Simplex k)
    (x : Fin K → Fin k) (b : ℝ) {w v : ℕ} {chi : ℝ}
    (hN : 2 ≤ N) (hchi : 0 < chi) (hwv : w ≤ v) (hvK : v ≤ K)
    (hlegal : TimeProfile.LegalPrefix p x v)
    (hcross : TimeProfile.Crossings p x w v chi) :
    (((TimeProfile.cL N p x b w v +
        (Real.log (TimeProfile.prefixMass N p x w) / TimeProfile.logScale N - b) +
        Real.log chi / TimeProfile.logScale N) / 2 : ℝ) : WithBot ℝ) ≤
      TimeProfile.cF N p x w v := by
  obtain ⟨⟨jl, hjl, hcl⟩, ⟨jr, hjr, hcr⟩⟩ := hcross
  have hleft := source_sideMaximum_ge_prefixMass N p x TimeProfile.leftProbability
    hN hchi hwv hvK hlegal hjl hcl
  have hright := source_sideMaximum_ge_prefixMass N p x TimeProfile.rightProbability
    hN hchi hwv hvK hlegal hjr hcr
  have hmass : 0 < TimeProfile.prefixMass N p x v :=
    TimeProfile.prefixMass_pos N p x (by omega) hlegal
  have hleftpos : 0 < TimeProfile.sideMaximum N p x w v TimeProfile.leftProbability :=
    (mul_pos hchi hmass).trans_le hleft
  have hrightpos : 0 < TimeProfile.sideMaximum N p x w v TimeProfile.rightProbability :=
    (mul_pos hchi hmass).trans_le hright
  have hlog := fluctuation_log_comparison (TimeProfile.logScale_pos hN) hchi
    hmass hleftpos hrightpos hleft hright
  have hfinite :
      (((Real.log (TimeProfile.prefixMass N p x v) + Real.log chi) /
        (2 * TimeProfile.logScale N) : ℝ) : WithBot ℝ) ≤ TimeProfile.cF N p x w v := by
    rw [TimeProfile.cF, logExponent_sqrt_of_pos N hleftpos,
      logExponent_sqrt_of_pos N hrightpos, ← WithBot.coe_min]
    exact WithBot.coe_le_coe.mpr hlog
  have hmass_exponent := TimeProfile.cL_exact_mass_exponent N p x b hN hwv hvK hlegal
  have hlower_eq : (TimeProfile.cL N p x b w v +
      (Real.log (TimeProfile.prefixMass N p x w) / TimeProfile.logScale N - b) +
      Real.log chi / TimeProfile.logScale N) / 2 =
      (Real.log (TimeProfile.prefixMass N p x v) + Real.log chi) /
        (2 * TimeProfile.logScale N) := by
    rw [← hmass_exponent]
    ring
  rw [hlower_eq]
  exact hfinite

end RiffleProfiles
