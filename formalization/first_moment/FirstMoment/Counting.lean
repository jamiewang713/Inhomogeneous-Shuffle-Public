import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

noncomputable section

open scoped BigOperators
open Filter

namespace InhomogeneousShuffle.FirstMoment

def SparseAssignment (K k q : ℕ) :=
  Σ Q : {S : Finset (Fin K) // S.card ≤ q}, (↥Q.val → Fin k)

instance (K k q : ℕ) : Fintype (SparseAssignment K k q) := by
  unfold SparseAssignment
  infer_instance

def sparseCount (K k q : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (q + 1), K.choose j * k ^ j

def BoundaryCode (K k qb : ℕ) :=
  Fin (K + 1) × Fin (k + 1) × SparseAssignment K k qb

def ProfileKey (K k qb qe d : ℕ) :=
  BoundaryCode K k qb × BoundaryCode K k qb × Fin (K + 1) ×
    (Fin d → Fin (K + 1)) × SparseAssignment K k qe × Fin 4

instance (K k qb qe d : ℕ) : Fintype (ProfileKey K k qb qe d) := by
  unfold ProfileKey BoundaryCode
  infer_instance

def profileCountBound (K k qb qe d : ℕ) : ℕ :=
  4 * (k + 1) ^ 2 * (K + 1) ^ (d + 3) * sparseCount K k qb ^ 2 *
    sparseCount K k qe

theorem card_sparseAssignment (K k q : ℕ) :
    Fintype.card (SparseAssignment K k q) = sparseCount K k q := by
  classical
  unfold SparseAssignment
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  unfold sparseCount
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.range (q + 1))
    (g := fun Q : {S : Finset (Fin K) // S.card ≤ q} => Q.val.card)
    (by intro Q _; exact Finset.mem_range.mpr (Nat.lt_succ_of_le Q.property))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjq : j ≤ q := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  let filtered := Finset.univ.filter
    (fun Q : {S : Finset (Fin K) // S.card ≤ q} => Q.val.card = j)
  have hc : filtered.card = K.choose j := by
    let e : ↥filtered ≃ ↥((Finset.univ : Finset (Fin K)).powersetCard j) :=
      { toFun := fun Q => ⟨Q.val.val, by
          have h := (Finset.mem_filter.mp Q.property).2
          exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, h⟩⟩
        invFun := fun Q => ⟨⟨Q.val, by
          rw [(Finset.mem_powersetCard.mp Q.property).2]
          exact hjq⟩, by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, (Finset.mem_powersetCard.mp Q.property).2⟩⟩
        left_inv := by intro Q; rfl
        right_inv := by intro Q; rfl }
    have h := Fintype.card_congr e
    simpa only [Fintype.card_coe, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin] using h
  calc
    _ = ∑ _Q ∈ filtered, k ^ j := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [(Finset.mem_filter.mp hQ).2]
    _ = filtered.card * k ^ j := by simp
    _ = K.choose j * k ^ j := by rw [hc]

theorem sparseCount_weighted (K k q : ℕ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    t ^ q * (sparseCount K k q : ℝ) ≤ (1 + (k : ℝ) * t) ^ K := by
  have hbin : (∑ j ∈ Finset.range (K + 1),
      (K.choose j : ℝ) * ((k : ℝ) * t) ^ j) = (1 + (k : ℝ) * t) ^ K := by
    rw [add_comm (1 : ℝ), add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_comm]
  have hpartial : (∑ j ∈ Finset.range (q + 1),
      (K.choose j : ℝ) * ((k : ℝ) * t) ^ j) ≤ (1 + (k : ℝ) * t) ^ K := by
    rw [← hbin]
    by_cases hq : q ≤ K
    · apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hq))
      intro i _ _
      positivity
    · have hKq : K ≤ q := le_of_lt (Nat.lt_of_not_ge hq)
      apply le_of_eq
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hKq))
      intro j _ hj
      have hKj : K < j := by
        have h : ¬ j < K + 1 := by simpa only [Finset.mem_range] using hj
        omega
      simp [Nat.choose_eq_zero_of_lt hKj]
  calc
    t ^ q * (sparseCount K k q : ℝ) =
        ∑ j ∈ Finset.range (q + 1), t ^ q * ((K.choose j : ℝ) * (k : ℝ) ^ j) := by
      simp [sparseCount, Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (q + 1), (K.choose j : ℝ) * ((k : ℝ) * t) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have htq := pow_le_pow_of_le_one ht.le ht1
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      calc
        _ ≤ t ^ j * ((K.choose j : ℝ) * (k : ℝ) ^ j) :=
          mul_le_mul_of_nonneg_right htq (by positivity)
        _ = _ := by rw [mul_pow]; ring
    _ ≤ _ := hpartial

theorem sparseCount_le (K k q : ℕ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    (sparseCount K k q : ℝ) ≤ (t ^ q)⁻¹ * (1 + (k : ℝ) * t) ^ K := by
  have h := sparseCount_weighted K k q ht ht1
  have hpow : 0 < t ^ q := pow_pos ht q
  have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hpow.le)
  simpa [← mul_assoc, ne_of_gt hpow] using h'

theorem card_profileKey (K k qb qe d : ℕ) :
    Fintype.card (ProfileKey K k qb qe d) = profileCountBound K k qb qe d := by
  simp only [ProfileKey, BoundaryCode, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, card_sparseAssignment, profileCountBound]
  ring

theorem profile_card_le_of_injective (K k qb qe d : ℕ) {C : Type*} [Fintype C]
    (encode : C → ProfileKey K k qb qe d) (hinj : Function.Injective encode) :
    Fintype.card C ≤ profileCountBound K k qb qe d := by
  rw [← card_profileKey]
  exact Fintype.card_le_of_injective encode hinj

theorem sparseCount_exp_bound (K k q : ℕ) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) :
    (sparseCount K k q : ℝ) ≤
      Real.exp ((q : ℝ) * Real.log (1 / t) + (k : ℝ) * t * K) := by
  have hI : (t ^ q)⁻¹ = Real.exp ((q : ℝ) * Real.log (1 / t)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
    simp [one_div, inv_pow]
  have hbase : 1 + (k : ℝ) * t ≤ Real.exp ((k : ℝ) * t) := by
    simpa only [add_comm] using Real.add_one_le_exp ((k : ℝ) * t)
  calc
    (sparseCount K k q : ℝ) ≤ (t ^ q)⁻¹ * (1 + (k : ℝ) * t) ^ K :=
      sparseCount_le K k q ht ht1
    _ ≤ (t ^ q)⁻¹ * (Real.exp ((k : ℝ) * t)) ^ K := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) hbase K
    _ = _ := by
      rw [hI, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem profileCount_exp_bound (K k qb qe d : ℕ) {tb te : ℝ}
    (htb : 0 < tb) (htb1 : tb ≤ 1) (hte : 0 < te) (hte1 : te ≤ 1) :
    (profileCountBound K k qb qe d : ℝ) ≤
      4 * ((k : ℝ) + 1) ^ 2 * ((K : ℝ) + 1) ^ (d + 3) *
        Real.exp (2 * (qb : ℝ) * Real.log (1 / tb) +
          (qe : ℝ) * Real.log (1 / te) + (k : ℝ) * K * (2 * tb + te)) := by
  have hb := sparseCount_exp_bound K k qb htb htb1
  have he := sparseCount_exp_bound K k qe hte hte1
  push_cast [profileCountBound]
  calc
    _ ≤ 4 * ((k : ℝ) + 1) ^ 2 * ((K : ℝ) + 1) ^ (d + 3) *
        (Real.exp ((qb : ℝ) * Real.log (1 / tb) + (k : ℝ) * tb * K)) ^ 2 *
        Real.exp ((qe : ℝ) * Real.log (1 / te) + (k : ℝ) * te * K) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, mul_assoc
        (4 * ((k : ℝ) + 1) ^ 2 * ((K : ℝ) + 1) ^ (d + 3)), ← Real.exp_add]
      congr 1
      congr 1
      push_cast
      ring

theorem profileCount_eventually (k d : ℕ) (T a b tb te : ℝ)
    (hT : 0 ≤ T) (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (htb : 0 < tb) (htb1 : tb ≤ 1) (hte : 0 < te) (hte1 : te ≤ 1)
    (K qb qe : ℕ → ℕ)
    (hK : ∀ᶠ N in atTop, (K N : ℝ) ≤ T * Real.log (N : ℝ))
    (hqb : ∀ᶠ N in atTop, (qb N : ℝ) ≤ a * Real.log (N : ℝ))
    (hqe : ∀ᶠ N in atTop, (qe N : ℝ) ≤ b * Real.log (N : ℝ))
    (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ N in atTop, (profileCountBound (K N) k (qb N) (qe N) d : ℝ) ≤
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
  filter_upwards [hK, hqb, hqe, hpoly, hlog, eventually_ge_atTop 1]
    with N hKN hqbN hqeN hpN hlogN hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hKN1 : (K N : ℝ) + 1 ≤ (T + 1) * Real.log (N : ℝ) := by
    nlinarith
  have hpref : 4 * ((k : ℝ) + 1) ^ 2 * ((K N : ℝ) + 1) ^ (d + 3) ≤
      (N : ℝ) ^ eps := by
    apply le_trans _ hpN
    calc
      _ ≤ 4 * ((k : ℝ) + 1) ^ 2 *
          ((T + 1) * Real.log (N : ℝ)) ^ (d + 3) := by
        gcongr
      _ = C0 * Real.log (N : ℝ) ^ (d + 3) := by
        dsimp [C0]
        rw [mul_pow]
        ring
  have hrate : 2 * (qb N : ℝ) * Real.log (1 / tb) +
        (qe N : ℝ) * Real.log (1 / te) + (k : ℝ) * (K N : ℝ) * (2 * tb + te) ≤
      (2 * a * Real.log (1 / tb) + b * Real.log (1 / te) +
        (k : ℝ) * T * (2 * tb + te)) * Real.log (N : ℝ) := by
    calc
      _ ≤ 2 * (a * Real.log (N : ℝ)) * Real.log (1 / tb) +
          (b * Real.log (N : ℝ)) * Real.log (1 / te) +
          (k : ℝ) * (T * Real.log (N : ℝ)) * (2 * tb + te) := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ 4 * ((k : ℝ) + 1) ^ 2 * ((K N : ℝ) + 1) ^ (d + 3) *
        Real.exp (2 * (qb N : ℝ) * Real.log (1 / tb) +
          (qe N : ℝ) * Real.log (1 / te) + (k : ℝ) * (K N : ℝ) * (2 * tb + te)) :=
      profileCount_exp_bound (K N) k (qb N) (qe N) d htb htb1 hte hte1
    _ ≤ (N : ℝ) ^ eps *
        Real.exp ((2 * a * Real.log (1 / tb) + b * Real.log (1 / te) +
          (k : ℝ) * T * (2 * tb + te)) * Real.log (N : ℝ)) := by
      gcongr
    _ = _ := by
      rw [Real.rpow_def_of_pos hNpos eps, Real.rpow_def_of_pos hNpos,
        ← Real.exp_add]
      congr 1
      ring

end InhomogeneousShuffle.FirstMoment
