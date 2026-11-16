import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
Finite product-law and first-moment aggregation lemmas from the frozen contract.
These results do not assert localization or density estimates for shuffle graphs.
-/

open scoped BigOperators Topology
open Filter

namespace InhomogeneousShuffle.FirstMoment

noncomputable section

structure FiniteGraphLaw (Ω M : Type*) [Fintype Ω] [Fintype M] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1
  graph : Ω → Finset M

def FiniteGraphLaw.edgeMarginal {Ω M : Type*} [Fintype Ω] [Fintype M]
    (law : FiniteGraphLaw Ω M) (m : M) : ℝ := by
  classical
  exact ∑ ω, law.weight ω * if m ∈ law.graph ω then 1 else 0

def FiniteGraphLaw.expectedCommonEdges {Ω M : Type*} [Fintype Ω] [Fintype M]
    (law : FiniteGraphLaw Ω M) : ℝ := by
  classical
  exact ∑ ω, ∑ ω', law.weight ω * law.weight ω' *
    ((law.graph ω ∩ law.graph ω').card : ℝ)

theorem expectedCommonEdges_eq_sum_sq {Ω M : Type*} [Fintype Ω] [Fintype M]
    (law : FiniteGraphLaw Ω M) :
    law.expectedCommonEdges = ∑ m, law.edgeMarginal m ^ 2 := by
  classical
  have hcard (s t : Finset M) :
      ((s ∩ t).card : ℝ) = ∑ m : M, (if m ∈ s then (1 : ℝ) else 0) *
        (if m ∈ t then (1 : ℝ) else 0) := by
    calc
      ((s ∩ t).card : ℝ) = ∑ m : M, if m ∈ s ∩ t then (1 : ℝ) else 0 := by
        rw [← Finset.sum_filter]
        have heq : Finset.univ.filter (fun m : M => m ∈ s ∩ t) = s ∩ t := by
          ext m
          simp
        rw [heq]
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        by_cases hs : m ∈ s <;> by_cases ht : m ∈ t <;> simp [hs, ht]
  unfold FiniteGraphLaw.expectedCommonEdges FiniteGraphLaw.edgeMarginal
  simp_rw [hcard, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext ω
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω' hω'
  ring

theorem localized_sum_sq {M I C : Type*} [Fintype M] [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C]
    (classOf : I → C) (active : M → Finset I)
    (p d : M → ℝ) (q : I → M → ℝ) (L : ℕ)
    (hp : ∀ m, 0 ≤ p m) (_hd : ∀ m, 0 ≤ d m) (hq : ∀ i m, 0 ≤ q i m)
    (hactive : ∀ m, (active m).card ≤ L)
    (hloc : ∀ m, p m ≤ d m + ∑ i ∈ active m, q i m) :
    ∑ m, p m ^ 2 ≤ 2 * ∑ m, d m ^ 2 +
      2 * (L : ℝ) * ∑ c, ∑ i ∈ Finset.univ.filter (fun i => classOf i = c),
        ∑ m, q i m ^ 2 := by
  classical
  have hpoint (m : M) :
      p m ^ 2 ≤ 2 * d m ^ 2 + 2 * (L : ℝ) * ∑ i : I, q i m ^ 2 := by
    let s : ℝ := ∑ i ∈ active m, q i m
    have hs : 0 ≤ s := Finset.sum_nonneg fun i hi => hq i m
    have hcs : s ^ 2 ≤ ((active m).card : ℝ) * ∑ i ∈ active m, q i m ^ 2 := by
      simpa [s] using Finset.sum_mul_sq_le_sq_mul_sq (active m)
        (fun _ : I => (1 : ℝ)) (fun i => q i m)
    have hcard : ((active m).card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hactive m
    have hsub : (∑ i ∈ active m, q i m ^ 2) ≤ ∑ i : I, q i m ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
    have hsq : s ^ 2 ≤ (L : ℝ) * ∑ i : I, q i m ^ 2 :=
      hcs.trans ((mul_le_mul_of_nonneg_right hcard
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg L)))
    have hbase : p m ^ 2 ≤ (d m + s) ^ 2 :=
      pow_le_pow_left₀ (hp m) (hloc m) 2
    nlinarith [sq_nonneg (d m - s)]
  have hfiber :
      (∑ c, ∑ i ∈ Finset.univ.filter (fun i => classOf i = c), ∑ m, q i m ^ 2) =
        ∑ i : I, ∑ m, q i m ^ 2 := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    simp
  rw [hfiber]
  calc
    (∑ m, p m ^ 2) ≤ ∑ m, (2 * d m ^ 2 + 2 * (L : ℝ) * ∑ i : I, q i m ^ 2) :=
      Finset.sum_le_sum fun m hm => hpoint m
    _ = 2 * ∑ m, d m ^ 2 + 2 * (L : ℝ) * ∑ i : I, ∑ m, q i m ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_comm]

theorem localized_sum_sq_bound {M I C : Type*} [Fintype M] [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C]
    (classOf : I → C) (active : M → Finset I)
    (p d : M → ℝ) (q : I → M → ℝ) (L : ℕ) (D U : ℝ)
    (hp : ∀ m, 0 ≤ p m) (hd : ∀ m, 0 ≤ d m) (hq : ∀ i m, 0 ≤ q i m)
    (hactive : ∀ m, (active m).card ≤ L)
    (hloc : ∀ m, p m ≤ d m + ∑ i ∈ active m, q i m)
    (hD : ∑ m, d m ^ 2 ≤ D)
    (hU : ∀ c, (∑ i ∈ Finset.univ.filter (fun i => classOf i = c),
      ∑ m, q i m ^ 2) ≤ U) :
    ∑ m, p m ^ 2 ≤ 2 * D + 2 * (L : ℝ) * (Fintype.card C : ℝ) * U := by
  have hsum : (∑ c, ∑ i ∈ Finset.univ.filter (fun i => classOf i = c),
      ∑ m, q i m ^ 2) ≤ (Fintype.card C : ℝ) * U := by
    simpa using Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hU c)
  calc
    _ ≤ 2 * ∑ m, d m ^ 2 + 2 * (L : ℝ) *
        ∑ c, ∑ i ∈ Finset.univ.filter (fun i => classOf i = c), ∑ m, q i m ^ 2 :=
      localized_sum_sq classOf active p d q L hp hd hq hactive hloc
    _ ≤ 2 * D + 2 * (L : ℝ) * ((Fintype.card C : ℝ) * U) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hD (by norm_num))
        (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by ring

theorem expectedCommonEdges_bound {Ω M I C : Type*}
    [Fintype Ω] [Fintype M] [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C]
    (law : FiniteGraphLaw Ω M) (classOf : I → C) (active : M → Finset I)
    (d : M → ℝ) (q : I → M → ℝ) (L : ℕ) (D U : ℝ)
    (hd : ∀ m, 0 ≤ d m) (hq : ∀ i m, 0 ≤ q i m)
    (hactive : ∀ m, (active m).card ≤ L)
    (hloc : ∀ m, law.edgeMarginal m ≤ d m + ∑ i ∈ active m, q i m)
    (hD : ∑ m, d m ^ 2 ≤ D)
    (hU : ∀ c, (∑ i ∈ Finset.univ.filter (fun i => classOf i = c),
      ∑ m, q i m ^ 2) ≤ U) :
    law.expectedCommonEdges ≤ 2 * D + 2 * (L : ℝ) * (Fintype.card C : ℝ) * U := by
  classical
  rw [expectedCommonEdges_eq_sum_sq]
  apply localized_sum_sq_bound classOf active law.edgeMarginal d q L D U
    _ hd hq hactive hloc hD hU
  intro m
  unfold FiniteGraphLaw.edgeMarginal
  exact Finset.sum_nonneg fun ω hω => mul_nonneg (law.weight_nonneg ω) (by positivity)

theorem profileClass_sum_bound {I : Type*} (s : Finset I)
    (f z : I → ℝ) (N H margin loss countLoss : ℝ)
    (hN : 1 < N) (hcard : (s.card : ℝ) ≤ N ^ (H + countLoss))
    (hf : ∀ x ∈ s, f x ≤ N ^ (z x + loss))
    (hz : ∀ x ∈ s, z x + H ≤ -margin) :
    ∑ x ∈ s, f x ≤ N ^ (-margin + loss + countLoss) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  calc
    (∑ x ∈ s, f x) ≤ ∑ x ∈ s, N ^ (-margin - H + loss) := by
      apply Finset.sum_le_sum
      intro x hx
      exact (hf x hx).trans (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith [hz x hx]))
    _ = (s.card : ℝ) * N ^ (-margin - H + loss) := by simp
    _ ≤ N ^ (H + countLoss) * N ^ (-margin - H + loss) :=
      mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _)
    _ = N ^ (-margin + loss + countLoss) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring

theorem expectedCommonEdges_power_bound {Ω M I C : Type*}
    [Fintype Ω] [Fintype M] [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C]
    (law : FiniteGraphLaw Ω M) (classOf : I → C) (active : M → Finset I)
    (err : M → ℝ) (q : I → M → ℝ) (L : ℕ) (D U : ℝ)
    (hd : ∀ m, 0 ≤ err m) (hq : ∀ i m, 0 ≤ q i m)
    (hactive : ∀ m, (active m).card ≤ L)
    (hloc : ∀ m, law.edgeMarginal m ≤ err m + ∑ i ∈ active m, q i m)
    (hD : ∑ m, err m ^ 2 ≤ D)
    (hU : ∀ c, (∑ i ∈ Finset.univ.filter (fun i => classOf i = c),
      ∑ m, q i m ^ 2) ≤ U)
    (N d a ell c : ℝ) (hN : 1 < N)
    (hDpow : D ≤ N ^ (-d)) (hLpow : (L : ℝ) ≤ N ^ ell)
    (hCpow : (Fintype.card C : ℝ) ≤ N ^ c) (hUpow : U ≤ N ^ (-a)) :
    law.expectedCommonEdges ≤ 2 * N ^ (-d) + 2 * N ^ (ell + c - a) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hprod : (L : ℝ) * (Fintype.card C : ℝ) ≤ N ^ ell * N ^ c :=
    mul_le_mul hLpow hCpow (Nat.cast_nonneg _) (Real.rpow_nonneg hN0.le _)
  calc
    _ ≤ 2 * D + 2 * (L : ℝ) * (Fintype.card C : ℝ) * U :=
      expectedCommonEdges_bound law classOf active err q L D U hd hq hactive hloc hD hU
    _ ≤ 2 * N ^ (-d) + 2 * (L : ℝ) * (Fintype.card C : ℝ) * N ^ (-a) :=
      add_le_add (mul_le_mul_of_nonneg_left hDpow (by norm_num))
        (mul_le_mul_of_nonneg_left hUpow (by positivity))
    _ ≤ 2 * N ^ (-d) + 2 * (N ^ ell * N ^ c) * N ^ (-a) := by
      apply add_le_add le_rfl
      calc
        2 * (L : ℝ) * (Fintype.card C : ℝ) * N ^ (-a) =
            (2 * ((L : ℝ) * (Fintype.card C : ℝ))) * N ^ (-a) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprod (by norm_num)) (Real.rpow_nonneg hN0.le _)
    _ = 2 * N ^ (-d) + 2 * N ^ (ell + c - a) := by
      rw [← Real.rpow_add hN0, mul_assoc, ← Real.rpow_add hN0]
      simp only [sub_eq_add_neg]

theorem two_power_terms_eventually (d a ell c delta : ℝ)
    (_hdelta : 0 < delta) (hd : delta < d) (ha : delta < a - ell - c) :
    ∀ᶠ N : ℕ in atTop,
      2 * (N : ℝ) ^ (-d) + 2 * (N : ℝ) ^ (ell + c - a) ≤ (N : ℝ) ^ (-delta) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h₁ : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d - delta))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < d - delta)).comp hcast
  have h₂ : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(a - ell - c - delta))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : 0 < a - ell - c - delta)).comp hcast
  have he₁ : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(d - delta)) < (1 / 4 : ℝ) :=
    h₁.eventually (gt_mem_nhds (by norm_num))
  have he₂ : ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (-(a - ell - c - delta)) < (1 / 4 : ℝ) :=
    h₂.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [he₁, he₂, eventually_gt_atTop (0 : ℕ)] with N hn₁ hn₂ hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have heq₁ : (N : ℝ) ^ (-d) = (N : ℝ) ^ (-delta) * (N : ℝ) ^ (-(d - delta)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have heq₂ : (N : ℝ) ^ (ell + c - a) =
      (N : ℝ) ^ (-delta) * (N : ℝ) ^ (-(a - ell - c - delta)) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [heq₁, heq₂]
  have hpos := Real.rpow_pos_of_pos hN0 (-delta)
  nlinarith

end
end InhomogeneousShuffle.FirstMoment
