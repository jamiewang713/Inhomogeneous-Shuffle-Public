import FirstMoment.Counting
import RiffleTimeProfile.AnalyticParameters

namespace RiffleUpperV2.Compat
open InhomogeneousShuffle.FirstMoment

noncomputable section
open scoped BigOperators
open Filter

theorem profileCount_uniform_eventually (k d : ℕ) (T a b tb te : ℝ)
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (htb : 0 < tb) (htb1 : tb ≤ 1) (hte : 0 < te) (hte1 : te ≤ 1)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N K qb qe : ℕ, N0 ≤ N →
      (K : ℝ) ≤ T * Real.log (N : ℝ) →
      (qb : ℝ) ≤ a * Real.log (N : ℝ) →
      (qe : ℝ) ≤ b * Real.log (N : ℝ) →
      (profileCountBound K k qb qe d : ℝ) ≤
        (N : ℝ) ^ (2 * a * Real.log (1 / tb) + b * Real.log (1 / te) +
          (k : ℝ) * T * (2 * tb + te) + eps) := by
  have hlogb : 0 ≤ Real.log (1 / tb) :=
    Real.log_nonneg ((le_div_iff₀ htb).mpr (by simpa using htb1))
  have hloge : 0 ≤ Real.log (1 / te) :=
    Real.log_nonneg ((le_div_iff₀ hte).mpr (by simpa using hte1))
  let C0 : ℝ := 4 * ((k : ℝ) + 1) ^ 2 * (T + 1) ^ (d + 3)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hpoly : ∀ᶠ N : ℕ in atTop,
      C0 * Real.log (N : ℝ) ^ (d + 3) ≤ (N : ℝ) ^ eps := by
    have ho := (isLittleO_log_rpow_rpow_atTop
      ((d + 3 : ℕ) : ℝ) heps).const_mul_left C0
    have hh := (tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
        (ho.bound (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hh, eventually_ge_atTop 1] with N h hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    rw [Real.rpow_natCast] at h
    simpa only [Real.norm_of_nonneg (mul_nonneg hC0 (pow_nonneg hlogN _)),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) eps), one_mul] using h
  have hlog : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp (hpoly.and hlog)
  refine ⟨max 2 N1, le_max_left _ _, ?_⟩
  intro N K qb qe hN hK hqb hqe
  obtain ⟨hpN, hlogN⟩ := hN1 N ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hK1 : (K : ℝ) + 1 ≤ (T + 1) * Real.log (N : ℝ) := by
    nlinarith
  have hpref : 4 * ((k : ℝ) + 1) ^ 2 * ((K : ℝ) + 1) ^ (d + 3) ≤
      (N : ℝ) ^ eps := by
    apply le_trans _ hpN
    calc
      _ ≤ 4 * ((k : ℝ) + 1) ^ 2 *
          ((T + 1) * Real.log (N : ℝ)) ^ (d + 3) := by gcongr
      _ = C0 * Real.log (N : ℝ) ^ (d + 3) := by
        dsimp [C0]
        rw [mul_pow]
        ring
  have hrate : 2 * (qb : ℝ) * Real.log (1 / tb) +
      (qe : ℝ) * Real.log (1 / te) + (k : ℝ) * (K : ℝ) * (2 * tb + te) ≤
      (2 * a * Real.log (1 / tb) + b * Real.log (1 / te) +
        (k : ℝ) * T * (2 * tb + te)) * Real.log (N : ℝ) := by
    calc
      _ ≤ 2 * (a * Real.log (N : ℝ)) * Real.log (1 / tb) +
          (b * Real.log (N : ℝ)) * Real.log (1 / te) +
          (k : ℝ) * (T * Real.log (N : ℝ)) * (2 * tb + te) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 4 * ((k : ℝ) + 1) ^ 2 * ((K : ℝ) + 1) ^ (d + 3) *
        Real.exp (2 * (qb : ℝ) * Real.log (1 / tb) +
          (qe : ℝ) * Real.log (1 / te) + (k : ℝ) * (K : ℝ) * (2 * tb + te)) :=
      profileCount_exp_bound K k qb qe d htb htb1 hte hte1
    _ ≤ (N : ℝ) ^ eps *
        Real.exp ((2 * a * Real.log (1 / tb) + b * Real.log (1 / te) +
          (k : ℝ) * T * (2 * tb + te)) * Real.log (N : ℝ)) := by gcongr
    _ = _ := by
      rw [Real.rpow_def_of_pos hNpos eps, Real.rpow_def_of_pos hNpos,
        ← Real.exp_add]
      congr 1
      ring

theorem profileCount_small_chi (k : ℕ) (T C eps : ℝ)
    (hk : 2 ≤ k) (hT : 0 ≤ T) (hC : 0 < C) (heps : 0 < eps) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < min 1 (1 / (k : ℝ)) ∧
      ∀ chi : ℝ, 0 < chi → chi < chi0 → ∀ d : ℕ,
        ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N K : ℕ, N0 ≤ N →
          (K : ℝ) ≤ T * Real.log (N : ℝ) →
          (profileCountBound K k
            (Nat.floor ((C / Real.log (1 / chi)) * Real.log (N : ℝ)))
            (Nat.floor (TimeProfile.exceptionalAllowance chi * Real.log (N : ℝ)))
            d : ℝ) ≤ (N : ℝ) ^ eps := by
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  let t : ℝ := min (1 / 2) (eps / (12 * (k : ℝ) * (T + 1)))
  have ht : 0 < t := lt_min (by norm_num) (div_pos heps (by positivity))
  have htHalf : t ≤ 1 / 2 := min_le_left _ _
  have ht1 : t ≤ 1 := by linarith
  have htRate : 3 * (k : ℝ) * T * t ≤ eps / 4 := by
    have hm := (le_div_iff₀ (show 0 < 12 * (k : ℝ) * (T + 1) by positivity)).mp
      (show t ≤ eps / (12 * (k : ℝ) * (T + 1)) from min_le_right _ _)
    have hp := mul_nonneg hkpos.le ht.le
    nlinarith
  let h : ℝ := Real.log (1 / t)
  have hh : 0 < h := by
    apply Real.log_pos
    exact (lt_div_iff₀ ht).mpr (by linarith)
  let B : ℝ := 1 + 16 * C * h / eps + (8 * h / eps) ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  let chi0 : ℝ := min (1 / (2 * (k : ℝ))) (Real.exp (-B))
  have hchi0 : 0 < chi0 :=
    lt_min (one_div_pos.mpr (by positivity)) (Real.exp_pos _)
  have hhalf1 : 1 / (2 * (k : ℝ)) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  have hhalfk : 1 / (2 * (k : ℝ)) < 1 / (k : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) hkpos).mpr
    nlinarith
  refine ⟨chi0, hchi0, lt_min ((min_le_left _ _).trans_lt hhalf1)
    ((min_le_left _ _).trans_lt hhalfk), ?_⟩
  intro chi hchi hsmall d
  have hexp : chi < Real.exp (-B) := hsmall.trans_le (min_le_right _ _)
  have hlog : B < Real.log (1 / chi) := by
    have hhlog := Real.log_lt_log hchi hexp
    rw [Real.log_exp] at hhlog
    simpa only [one_div, Real.log_inv, neg_neg] using neg_lt_neg hhlog
  have hu : 0 < Real.log (1 / chi) := hB.trans hlog
  have hlinear : 16 * C * h / eps ≤ Real.log (1 / chi) := by
    dsimp [B] at hlog
    nlinarith [sq_nonneg (8 * h / eps)]
  have hsquare : (8 * h / eps) ^ 2 ≤ Real.log (1 / chi) := by
    have hnonneg : 0 ≤ 16 * C * h / eps := by positivity
    dsimp [B] at hlog
    linarith
  have hsqrt : 8 * h / eps ≤ Real.sqrt (Real.log (1 / chi)) :=
    Real.le_sqrt_of_sq_le hsquare
  have hsqrtpos : 0 < Real.sqrt (Real.log (1 / chi)) :=
    (div_pos (mul_pos (by norm_num) hh) heps).trans_le hsqrt
  have hboundary : 2 * (C / Real.log (1 / chi)) * h ≤ eps / 8 := by
    have hm := (div_le_iff₀ heps).mp hlinear
    calc
      _ = (2 * C * h) / Real.log (1 / chi) := by ring
      _ ≤ eps / 8 := (div_le_iff₀ hu).mpr (by nlinarith)
  have hexception : TimeProfile.exceptionalAllowance chi * h ≤ eps / 8 := by
    have hm := (div_le_iff₀ heps).mp hsqrt
    change (1 / Real.sqrt (Real.log (1 / chi))) * h ≤ eps / 8
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ hsqrtpos).mpr (by nlinarith)
  have ha : 0 ≤ C / Real.log (1 / chi) := (div_pos hC hu).le
  have hb : 0 ≤ TimeProfile.exceptionalAllowance chi :=
    TimeProfile.exceptionalAllowance_nonneg chi
  obtain ⟨N0, hN0, hbound⟩ := profileCount_uniform_eventually k d T
    (C / Real.log (1 / chi)) (TimeProfile.exceptionalAllowance chi) t t
    hT ha hb ht ht1 ht ht1 (eps / 2) (by positivity)
  refine ⟨N0, hN0, ?_⟩
  intro N K hN hK
  have hN2 : 2 ≤ N := hN0.trans hN
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNreal
  have hqb : ((Nat.floor ((C / Real.log (1 / chi)) * Real.log (N : ℝ))) : ℝ) ≤
      (C / Real.log (1 / chi)) * Real.log (N : ℝ) :=
    Nat.floor_le (mul_nonneg ha hlogN)
  have hqe : ((Nat.floor (TimeProfile.exceptionalAllowance chi * Real.log (N : ℝ))) : ℝ) ≤
      TimeProfile.exceptionalAllowance chi * Real.log (N : ℝ) :=
    Nat.floor_le (mul_nonneg hb hlogN)
  apply (hbound N K _ _ hN hK hqb hqe).trans
  apply Real.rpow_le_rpow_of_exponent_le hNreal
  change 2 * (C / Real.log (1 / chi)) * h +
    TimeProfile.exceptionalAllowance chi * h + (k : ℝ) * T * (2 * t + t) + eps / 2 ≤ eps
  nlinarith

end
end RiffleUpperV2.Compat
