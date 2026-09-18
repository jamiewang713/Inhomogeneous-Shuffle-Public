import RiffleTimeProfile.Ambient

/-!
# Finite side-mass exponents

These are the frozen B01–B04 statements. The exponent is a deterministic
side-mass quantity; no assertion about variance or anti-concentration is made.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace TimeProfile

variable {k K : ℕ}

/-- B01: both side masses are nonnegative. -/
theorem sideMass_nonneg (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w : ℕ) (j : Fin K) :
    0 ≤ sideMass N p x w leftProbability j ∧
      0 ≤ sideMass N p x w rightProbability j := by
  have hmass : 0 ≤ prefixMass N p x w := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact Finset.prod_nonneg fun _ _ => prob_nonneg _ _
  have hprod : 0 ≤ ∏ h ∈ positions K w j.val, prob (p h) (x h) :=
    Finset.prod_nonneg fun _ _ => prob_nonneg _ _
  constructor
  · exact mul_nonneg (mul_nonneg hmass hprod)
      (Finset.sum_nonneg fun _ _ => prob_nonneg _ _)
  · exact mul_nonneg (mul_nonneg hmass hprod)
      (Finset.sum_nonneg fun _ _ => prob_nonneg _ _)

/-- B01: side masses before a common prefix length do not depend on its continuation. -/
theorem sideMass_prefix_eq (N : ℕ) (p : Fin K → Simplex k)
    (x y : Fin K → Fin k) {w v : ℕ} (hwv : w ≤ v)
    (hprefix : ∀ j : Fin K, j.val < v → x j = y j)
    (j : Fin K) (hj : j.val < v) :
    sideMass N p x w leftProbability j = sideMass N p y w leftProbability j ∧
      sideMass N p x w rightProbability j = sideMass N p y w rightProbability j := by
  have hmass : prefixMass N p x w = prefixMass N p y w := by
    unfold prefixMass prefixWeight
    congr 1
    apply Finset.prod_congr rfl
    intro h hh
    rw [hprefix h (lt_of_lt_of_le (Finset.mem_filter.mp hh).2.2 hwv)]
  have hprod : (∏ h ∈ positions K w j.val, prob (p h) (x h)) =
      ∏ h ∈ positions K w j.val, prob (p h) (y h) := by
    apply Finset.prod_congr rfl
    intro h hh
    rw [hprefix h (lt_trans (Finset.mem_filter.mp hh).2.2 hj)]
  constructor <;> simp only [sideMass, hmass, hprod, hprefix j hj]

/-- B01: the empty side-index set has maximum zero on both sides. -/
theorem sideMaximum_self (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w : ℕ) :
    sideMaximum N p x w w leftProbability = 0 ∧
      sideMaximum N p x w w rightProbability = 0 := by
  have hpos : positions K w w = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    omega
  simp [sideMaximum, hpos]

/-- B02: the extended exponent is unchanged by continuation beyond the boundary join. -/
theorem cF_prefix_eq (N : ℕ) (p : Fin K → Simplex k)
    (x y : Fin K → Fin k) {w v : ℕ} (hwv : w ≤ v)
    (hprefix : ∀ j : Fin K, j.val < v → x j = y j) :
    cF N p x w v = cF N p y w v := by
  have hl : sideMaximum N p x w v leftProbability =
      sideMaximum N p y w v leftProbability := by
    unfold sideMaximum
    apply congrArg (fun z : NNReal => (z : ℝ))
    apply Finset.sup_congr rfl
    intro j hj
    rw [(sideMass_prefix_eq N p x y hwv hprefix j (Finset.mem_filter.mp hj).2.2).1]
  have hr : sideMaximum N p x w v rightProbability =
      sideMaximum N p y w v rightProbability := by
    unfold sideMaximum
    apply congrArg (fun z : NNReal => (z : ℝ))
    apply Finset.sup_congr rfl
    intro j hj
    rw [(sideMass_prefix_eq N p x y hwv hprefix j (Finset.mem_filter.mp hj).2.2).2]
  simp only [cF, hl, hr]

/-- B03: bottom is exactly the zero-side case, including empty maxima. -/
theorem cF_eq_bot_iff (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w v : ℕ) :
    cF N p x w v = ⊥ ↔
      sideMaximum N p x w v leftProbability = 0 ∨
        sideMaximum N p x w v rightProbability = 0 := by
  have hlog : ∀ z : ℝ, logExponent N z = ⊥ ↔ z = 0 := by
    intro z
    unfold logExponent
    split_ifs with hz <;> simp_all
  have hl : 0 ≤ sideMaximum N p x w v leftProbability := NNReal.coe_nonneg _
  have hr : 0 ≤ sideMaximum N p x w v rightProbability := NNReal.coe_nonneg _
  rw [cF, min_eq_bot, hlog, hlog, Real.sqrt_eq_zero hl, Real.sqrt_eq_zero hr]

/-- B03: a join at the ambient length has extended exponent bottom. -/
theorem cF_self (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w : ℕ) : cF N p x w w = ⊥ := by
  exact (cF_eq_bot_iff N p x w w).mpr (Or.inl (sideMaximum_self N p x w).1)

/-- B03: positivity of both side maxima identifies the finite real value. -/
theorem cF_eq_coe_of_pos (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    (w v : ℕ)
    (hl : 0 < sideMaximum N p x w v leftProbability)
    (hr : 0 < sideMaximum N p x w v rightProbability) :
    cF N p x w v =
      ((min (Real.log (Real.sqrt (sideMaximum N p x w v leftProbability)) / logScale N)
        (Real.log (Real.sqrt (sideMaximum N p x w v rightProbability)) / logScale N) : ℝ) :
        WithBot ℝ) := by
  simp only [cF, logExponent, ne_of_gt (Real.sqrt_pos.mpr hl),
    ne_of_gt (Real.sqrt_pos.mpr hr), if_false]
  rfl

/-- B04: genuine crossing mass gives positive maxima and the explicit cL comparison. -/
theorem cF_lower_bound_of_crossings
    (N : ℕ) (p : Fin K → Simplex k) (x : Fin K → Fin k)
    {w v M : ℕ} {chi b e_b : ℝ}
    (hN : 2 ≤ N) (hchi : 0 < chi) (hwv : w ≤ v) (hvM : v ≤ M) (hMK : M ≤ K)
    (hlegal : LegalPrefix p x M) (hcross : Crossings p x w v chi)
    (hambient : |Real.log (prefixMass N p x w) / logScale N - b| ≤ e_b) :
    chi * prefixMass N p x M ≤ sideMaximum N p x w v leftProbability ∧
    chi * prefixMass N p x M ≤ sideMaximum N p x w v rightProbability ∧
    0 < sideMaximum N p x w v leftProbability ∧
    0 < sideMaximum N p x w v rightProbability ∧
    ∃ F : ℝ, cF N p x w v = (F : WithBot ℝ) ∧
      cL N p x b w M / 2 - (e_b + Real.log (1 / chi) / logScale N) / 2 ≤ F := by
  have hmpos : 0 < prefixMass N p x M := prefixMass_pos N p x (by omega) hlegal
  have hscale : 0 < logScale N := logScale_pos hN
  have hcross_bound : ∀ (side : Simplex k → Fin k → ℝ),
      (∃ j ∈ positions K w v, chi ≤ side (p j) (x j)) →
      chi * prefixMass N p x M ≤ sideMaximum N p x w v side := by
    intro side hs
    obtain ⟨j, hj, hside⟩ := hs
    have hwj : w ≤ j.val := (Finset.mem_filter.mp hj).2.1
    have hjv : j.val < v := (Finset.mem_filter.mp hj).2.2
    have hjM : j.val ≤ M := by omega
    have hsplit : positions K 0 j.val = positions K 0 w ∪ positions K w j.val := by
      ext h
      simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdis : Disjoint (positions K 0 w) (positions K w j.val) := by
      apply Finset.disjoint_left.mpr
      intro h hh hh'
      simp only [positions, Finset.mem_filter, Finset.mem_univ, true_and] at hh hh'
      omega
    have hmassj : prefixMass N p x j.val = prefixMass N p x w *
        ∏ h ∈ positions K w j.val, prob (p h) (x h) := by
      simp only [prefixMass, prefixWeight, hsplit, Finset.prod_union hdis]
      ring
    have hmono : prefixMass N p x M ≤ prefixMass N p x j.val :=
      mul_le_mul_of_nonneg_left (prefixWeight_extension_le p x hjM hlegal) (Nat.cast_nonneg _)
    have hmj : 0 ≤ prefixMass N p x j.val := le_trans hmpos.le hmono
    have hmassside : chi * prefixMass N p x M ≤ sideMass N p x w side j := by
      calc
        chi * prefixMass N p x M ≤ chi * prefixMass N p x j.val :=
          mul_le_mul_of_nonneg_left hmono hchi.le
        _ ≤ side (p j) (x j) * prefixMass N p x j.val :=
          mul_le_mul_of_nonneg_right hside hmj
        _ = sideMass N p x w side j := by rw [hmassj]; unfold sideMass; ring
    have hsup : Real.toNNReal (sideMass N p x w side j) ≤
        (positions K w v).sup (fun h => Real.toNNReal (sideMass N p x w side h)) :=
      Finset.le_sup (f := fun h : Fin K => Real.toNNReal (sideMass N p x w side h)) hj
    have hmax : sideMass N p x w side j ≤ sideMaximum N p x w v side := by
      exact le_trans (Real.le_coe_toNNReal _) (NNReal.coe_le_coe.mpr hsup)
    exact le_trans hmassside hmax
  have hlbound := hcross_bound leftProbability hcross.1
  have hrbound := hcross_bound rightProbability hcross.2
  have hlpos : 0 < sideMaximum N p x w v leftProbability :=
    lt_of_lt_of_le (mul_pos hchi hmpos) hlbound
  have hrpos : 0 < sideMaximum N p x w v rightProbability :=
    lt_of_lt_of_le (mul_pos hchi hmpos) hrbound
  have hexact := cL_exact_mass_exponent N p x b (w := w) (M := M) hN
    (le_trans hwv hvM) hMK hlegal
  have hbirth : -e_b ≤ Real.log (prefixMass N p x w) / logScale N - b :=
    (abs_le.mp hambient).1
  have hlog_bound : ∀ z : ℝ, chi * prefixMass N p x M ≤ z →
      0 < z →
      cL N p x b w M / 2 - (e_b + Real.log (1 / chi) / logScale N) / 2 ≤
        Real.log (Real.sqrt z) / logScale N := by
    intro z hz hzpos
    have hlog := Real.log_le_log (mul_pos hchi hmpos) hz
    rw [Real.log_mul (ne_of_gt hchi) (ne_of_gt hmpos)] at hlog
    have hdiv := div_le_div_of_nonneg_right hlog hscale.le
    rw [add_div] at hdiv
    have hcost : cL N p x b w M - e_b ≤ Real.log (prefixMass N p x M) / logScale N := by
      linarith
    have hsqrt : Real.log (Real.sqrt z) / logScale N =
        (Real.log z / logScale N) / 2 := by
      rw [Real.log_sqrt hzpos.le]
      ring
    rw [hsqrt]
    simp only [one_div, Real.log_inv, neg_div]
    linarith
  refine ⟨hlbound, hrbound, hlpos, hrpos, ?_⟩
  refine ⟨min (Real.log (Real.sqrt (sideMaximum N p x w v leftProbability)) / logScale N)
      (Real.log (Real.sqrt (sideMaximum N p x w v rightProbability)) / logScale N),
    cF_eq_coe_of_pos N p x w v hlpos hrpos, ?_⟩
  exact le_min (hlog_bound _ hlbound hlpos) (hlog_bound _ hrbound hrpos)

end TimeProfile
