import RiffleLowerV2.Shared

-- Verbatim mathematical port of Witness/Empirical.lean into an independent lane.
-- See audit/LB07/empirical_provenance_v1.md.
noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.ProfileTransfer
open TimeProfile

private theorem clamp_identity (x : ℝ) :
    max 0 (min 1 x) = max 0 x - max 0 (x-1) := by
  by_cases hx : x ≤ 0
  · rw [min_eq_right (by linarith), max_eq_left hx,
      max_eq_left (by linarith : x-1 ≤ 0)]
    ring
  · have hx0 : 0 ≤ x := (not_le.mp hx).le
    by_cases hx1 : 1 ≤ x
    · rw [min_eq_left hx1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1),
        max_eq_right hx0, max_eq_right (by linarith : 0 ≤ x-1)]
      ring
    · rw [min_eq_right (not_le.mp hx1).le, max_eq_right hx0,
        max_eq_left (by linarith : x-1 ≤ 0)]
      ring

theorem columnFraction_mono {K N : ℕ} (hN : 2 ≤ N) (j : Fin K) :
    Monotone (columnFraction N j) := by
  intro r s hrs
  exact max_le_max_left _ (min_le_min_left _
    (sub_le_sub_right (mul_le_mul_of_nonneg_right hrs (logScale_pos hN).le) _))

theorem columnFraction_sum {K N : ℕ} (hN : 2 ≤ N) {t : ℝ}
    (ht0 : 0 ≤ t) (htK : t ≤ horizon N K) :
    (∑ j : Fin K, columnFraction N j t) = t * logScale N := by
  have hL := logScale_pos hN
  have ht : t * logScale N ≤ (K : ℝ) :=
    (le_div_iff₀ hL).mp htK
  simp_rw [columnFraction, clamp_identity]
  have heq : (∑ j : Fin K,
      (max 0 (t * logScale N - (j.val : ℝ)) -
        max 0 (t * logScale N - (j.val : ℝ) - 1))) =
      ∑ i ∈ Finset.range K,
        (max 0 (t * logScale N - (i : ℝ)) -
          max 0 (t * logScale N - ((i+1 : ℕ) : ℝ))) := by
    simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]
    exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      max 0 (t * logScale N - (i : ℝ)) -
        max 0 (t * logScale N - (i : ℝ) - 1)) K
  rw [heq, Finset.sum_range_sub']
  simp only [Nat.cast_zero, sub_zero]
  rw [max_eq_right (mul_nonneg ht0 hL.le), max_eq_left (sub_nonpos.mpr ht), sub_zero]

theorem empiricalIntegral_const {K N : ℕ} (hN : 2 ≤ N) (c : ℝ) {r s : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (horizon N K)) (hs : s ∈ Icc (0 : ℝ) (horizon N K)) :
    empiricalIntegral N (fun _ : Fin K => c) r s = (s-r)*c := by
  simp only [empiricalIntegral, ← Finset.sum_div, ← Finset.sum_mul,
    Finset.sum_sub_distrib, columnFraction_sum hN hs.1 hs.2,
    columnFraction_sum hN hr.1 hr.2]
  field_simp [(logScale_pos hN).ne']

theorem empiricalIntegral_mono {K N : ℕ} (hN : 2 ≤ N)
    {f g : Fin K → ℝ} (hfg : ∀ j, f j ≤ g j) {r s : ℝ} (hrs : r ≤ s) :
    empiricalIntegral N f r s ≤ empiricalIntegral N g r s := by
  apply Finset.sum_le_sum
  intro j _
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hfg j)
      (sub_nonneg.mpr (columnFraction_mono hN j hrs))) (logScale_pos hN).le

theorem empiricalIntegral_nonneg {K N : ℕ} (hN : 2 ≤ N)
    {f : Fin K → ℝ} (hf : ∀ j, 0 ≤ f j) {r s : ℝ} (hrs : r ≤ s) :
    0 ≤ empiricalIntegral N f r s := by
  unfold empiricalIntegral
  exact Finset.sum_nonneg fun j _ => div_nonneg
    (mul_nonneg (sub_nonneg.mpr (columnFraction_mono hN j hrs)) (hf j))
    (logScale_pos hN).le

theorem empiricalIntegral_le {K N : ℕ} (hN : 2 ≤ N)
    {f : Fin K → ℝ} {M r s : ℝ} (hf : ∀ j, f j ≤ M)
    (hr0 : 0 ≤ r) (hrs : r ≤ s) (hsK : s ≤ horizon N K) :
    empiricalIntegral N f r s ≤ (s-r)*M := by
  calc
    empiricalIntegral N f r s ≤ empiricalIntegral N (fun _ => M) r s :=
      empiricalIntegral_mono hN hf hrs
    _ = (s-r)*M := empiricalIntegral_const hN M ⟨hr0, hrs.trans hsK⟩ ⟨hr0.trans hrs, hsK⟩

theorem empiricalIntegral_swap {K N : ℕ} (f : Fin K → ℝ) (r s : ℝ) :
    empiricalIntegral N f s r = -empiricalIntegral N f r s := by
  unfold empiricalIntegral
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem empiricalIntegral_abs_le {K N : ℕ} (hN : 2 ≤ N)
    {f : Fin K → ℝ} {M r s : ℝ} (hf : ∀ j, |f j| ≤ M)
    (hr : r ∈ Icc (0 : ℝ) (horizon N K)) (hs : s ∈ Icc (0 : ℝ) (horizon N K)) :
    |empiricalIntegral N f r s| ≤ |s-r| *M := by
  have hforward : ∀ a b : ℝ, a ∈ Icc (0 : ℝ) (horizon N K) →
      b ∈ Icc (0 : ℝ) (horizon N K) → a ≤ b →
      |empiricalIntegral N f a b| ≤ (b-a)*M := by
    intro a b ha hb hab
    apply abs_le.mpr
    constructor
    · have hlo := empiricalIntegral_mono hN (fun j => (abs_le.mp (hf j)).1) hab
      rw [empiricalIntegral_const hN (-M) ha hb] at hlo
      nlinarith
    · exact empiricalIntegral_le hN (fun j => (abs_le.mp (hf j)).2) ha.1 hab hb.2
  rcases le_total r s with hrs | hsr
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hrs)] using hforward r s hr hs hrs
  · rw [← neg_neg (empiricalIntegral N f r s), ← empiricalIntegral_swap,
      abs_neg, abs_of_nonpos (sub_nonpos.mpr hsr)]
    convert hforward s r hs hr hsr using 1; ring

theorem empiricalIntegral_endpoint_bound {K N : ℕ} (hN : 2 ≤ N)
    {f : Fin K → ℝ} {M r s r' s' : ℝ} (hf : ∀ j, |f j| ≤ M)
    (hr : r ∈ Icc (0 : ℝ) (horizon N K)) (hs : s ∈ Icc (0 : ℝ) (horizon N K))
    (hr' : r' ∈ Icc (0 : ℝ) (horizon N K)) (hs' : s' ∈ Icc (0 : ℝ) (horizon N K)) :
    |empiricalIntegral N f r s - empiricalIntegral N f r' s'| ≤
      (|r-r'|+|s-s'|)*M := by
  have heq : empiricalIntegral N f r s - empiricalIntegral N f r' s' =
      empiricalIntegral N f r r' + empiricalIntegral N f s' s := by
    have h1 := empiricalIntegral_add N f r r' s
    have h2 := empiricalIntegral_add N f r' s' s
    linarith
  rw [heq]
  calc
    _ ≤ |empiricalIntegral N f r r'| + |empiricalIntegral N f s' s| := abs_add_le _ _
    _ ≤ |r'-r| *M+|s-s'| *M := add_le_add
      (empiricalIntegral_abs_le hN hf hr hr') (empiricalIntegral_abs_le hN hf hs' hs)
    _ = (|r-r'|+|s-s'|)*M := by rw [abs_sub_comm r' r]; ring

theorem continuous_columnFraction {K N : ℕ} (j : Fin K) :
    Continuous (columnFraction N j) := by
  unfold columnFraction
  fun_prop

theorem continuous_empiricalIntegral {K N : ℕ} (f : Fin K → ℝ) :
    Continuous (fun rs : ℝ × ℝ => empiricalIntegral N f rs.1 rs.2) := by
  unfold empiricalIntegral
  apply continuous_finsetSum
  intro j _
  exact (((continuous_columnFraction j).comp continuous_snd).sub
    ((continuous_columnFraction j).comp continuous_fst)).mul_const (f j) |>.div_const _

theorem continuousOn_empiricalIntegral_param {K N : ℕ} {D : Set ℝ}
    {f : ℝ → Fin K → ℝ} (hf : ∀ j, ContinuousOn (fun a => f a j) D) (r s : ℝ) :
    ContinuousOn (fun a => empiricalIntegral N (f a) r s) D := by
  unfold empiricalIntegral
  apply continuousOn_finsetSum
  intro j _
  exact ((hf j).const_mul _).div_const _

theorem empiricalIntegral_linear {K N : ℕ} (f g : Fin K → ℝ) (a r s : ℝ) :
    empiricalIntegral N (fun j => a*f j-g j) r s =
      a*empiricalIntegral N f r s - empiricalIntegral N g r s := by
  simp only [empiricalIntegral, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end RiffleLowerV2.ProfileTransfer
