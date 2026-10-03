import RiffleUpperV2.Margins.Empirical
import RiffleUpperV2.Shared.Infimum
import RiffleLowerV2.ProfileTransfer.Empirical

noncomputable section
open Set
open scoped BigOperators
namespace RiffleUpperV2.Margins
open TimeProfile RiffleLowerV2

def suffixIndex {L : ℕ} (r : ℕ) (j : Fin (L-r)) : Fin L := ⟨r+j.val, by omega⟩

/-- Delete an integer number of columns, leaving their counts unchanged. -/
def suffixCuts {k n L : ℕ} (cuts : Cuts k n L) (r : ℕ) : Cuts k n (L-r) where
  count j l := cuts.count (suffixIndex r j) l
  sum_count j := cuts.sum_count (suffixIndex r j)

@[simp] theorem suffixCuts_profile {k n L : ℕ} (cuts : Cuts k n L)
    (r : ℕ) (hn : 0 < n) (j : Fin (L-r)) :
    (suffixCuts cuts r).profile hn j = cuts.profile hn (suffixIndex r j) := rfl

/-- Reindex the retained columns without changing original scale N. -/
theorem gridSum_suffix {N L : ℕ} (f : Fin L → ℝ) (r s u : ℕ) (hrs : r ≤ s) :
    gridSum N (fun j => f (suffixIndex r j)) (s-r) (u-r) = gridSum N f s u := by
  classical
  unfold gridSum
  congr 1
  apply Finset.sum_bij (fun j _ => suffixIndex r j)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    dsimp [suffixIndex]
    omega
  · intro j hj j' hj' h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp [suffixIndex] at this
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hrj : r ≤ j.val := hrs.trans hj.1
    refine ⟨⟨j.val-r, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor <;> omega
    · apply Fin.ext
      dsimp [suffixIndex]
      omega
  · intro j _
    rfl

theorem empiricalA_suffix {k N n L : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    (r s u : ℕ) (hrs : r ≤ s) :
    empiricalA N r (suffixCuts cuts r) hn s u = empiricalA N 0 cuts hn s u := by
  simp only [empiricalA, suffixCuts_profile, Nat.sub_zero]
  exact gridSum_suffix (N := N) (L := L) (fun j => maxCost (cuts.profile hn j)) r s u hrs

theorem empiricalB_suffix {k N n L : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    (r s u : ℕ) (hrs : r ≤ s) (θ : ℝ) :
    empiricalB N r (suffixCuts cuts r) hn θ s u = empiricalB N 0 cuts hn θ s u := by
  simp only [empiricalB, suffixCuts_profile, Nat.sub_zero]
  exact gridSum_suffix (N := N) (L := L) (fun j => psi (cuts.profile hn j) θ) r s u hrs

theorem empiricalA_add {k N n L : ℕ} (hN : 2 ≤ N) (a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) {r s u : ℕ} (hrs : r ≤ s) (hsu : s ≤ u) :
    empiricalA N a cuts hn r u = empiricalA N a cuts hn r s + empiricalA N a cuts hn s u := by
  rw [empiricalA_grid_adapter hN a cuts hn (hrs.trans hsu),
    empiricalA_grid_adapter hN a cuts hn hrs, empiricalA_grid_adapter hN a cuts hn hsu]
  exact empiricalIntegral_add _ _ _ _ _

/-- One-sided error propagation keeps the coefficient 7/2, even for negative
size exponents. -/
theorem expression_error {θ β β' B B' D D' E F : ℝ}
    (hθ : θ ∈ Icc (3 : ℝ) 4) (hE : 0 ≤ E)
    (hβ : β' ≤ β+E) (hB : |B'-B| ≤ F) (hD : |D'-D| ≤ F) :
    (θ+3)/2*β'-B'-2*D' ≤ (θ+3)/2*β-B-2*D + (7/2 : ℝ)*E+3*F := by
  have hc0 : 0 ≤ (θ+3)/2 := by linarith [hθ.1]
  have hc : (θ+3)/2 ≤ (7/2 : ℝ) := by linarith [hθ.2]
  have hp := mul_le_mul_of_nonneg_left hβ hc0
  have he := mul_le_mul_of_nonneg_right hc hE
  linarith [(abs_le.mp hB).1, (abs_le.mp hD).1]

/-- The retained suffix inherits the empirical negative margin solely from
concrete coordinate closeness and the original-scale population bound. -/
theorem inducedMargin {k N m K r : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (p : Cuts k N K) (q : Cuts k m (K-r)) (hm : 0 < m) (hrK : r ≤ K)
    {T η e ζ : ℝ} (he : 0 ≤ e) (hζ : 0 ≤ ζ) (hK : (K : ℝ) ≤ T*logScale N)
    (hmargin : EmpiricalNegativeMargin N 0 p (by omega) η)
    (hsize : Real.log (m : ℝ)/Real.log (N : ℝ) ≤
      1-empiricalA N 0 p (by omega) 0 r+e)
    (hpq : ∀ j l, |prob (p.profile (by omega) (suffixIndex r j)) l-
      prob (q.profile hm j) l| ≤ ζ) :
    EmpiricalNegativeMargin N r q hm
      (η-(7/2 : ℝ)*(e+(k : ℝ)*T*ζ)-12*(k : ℝ)^4*T*ζ) := by
  let hn : 0 < N := by omega
  have hT : 0 ≤ T := by nlinarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K), logScale_pos hN]
  have hLenK : ((K-r : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (Nat.sub_le K r)
  have hLen : ((K-r : ℕ) : ℝ) ≤ T*logScale N := hLenK.trans hK
  have hEnd : r+(K-r) = K := Nat.add_sub_of_le hrK
  have hA (s u : ℕ) (hrs : r ≤ s) :
      |empiricalA N r q hm s u-empiricalA N 0 p hn s u| ≤ (k : ℝ)*T*ζ := by
    have hh := (costStability hk hN r (suffixCuts p r) q hn hm hζ hLen hpq s u).1
    rw [empiricalA_suffix p hn r s u hrs] at hh
    simpa only [abs_sub_comm] using hh
  have hB (s u : ℕ) (hrs : r ≤ s) (θ : ℝ) (hθ : θ ∈ Icc (2 : ℝ) 4) :
      |empiricalB N r q hm θ s u-empiricalB N 0 p hn θ s u| ≤ 4*(k : ℝ)^4*T*ζ := by
    have hh := (costStability hk hN r (suffixCuts p r) q hn hm hζ hLen hpq s u).2 θ hθ
    rw [empiricalB_suffix p hn r s u hrs θ] at hh
    simpa only [abs_sub_comm] using hh
  have hβ (s : ℕ) (hrs : r ≤ s) :
      empiricalBeta N r q hm s ≤ empiricalBeta N 0 p hn s+(e+(k : ℝ)*T*ζ) := by
    have hAdd := empiricalA_add hN 0 p hn (Nat.zero_le r) hrs
    have hErr := (abs_le.mp (hA r s le_rfl)).1
    have hLog : Real.log (N : ℝ) ≠ 0 := (logScale_pos hN).ne'
    simp only [empiricalBeta, div_self hLog]
    linarith
  have hE : 0 ≤ e+(k : ℝ)*T*ζ := by positivity
  have hF : 0 ≤ 4*(k : ℝ)^4*T*ζ := by positivity
  constructor
  · rw [hEnd]
    have hp := hmargin.1
    simp only [zero_add] at hp
    have hq := hβ K hrK
    nlinarith
  · intro s u hrs hsu hu
    obtain ⟨θ, hθ, hmin⟩ := empiricalInf_attained N 0 p hn s u
    have hp := hmargin.2 s u (Nat.zero_le s) hsu (by omega)
    have hcomp := expression_error hθ hE (hβ s hrs)
      (hB s u hrs θ ⟨by linarith [hθ.1], hθ.2⟩)
      (hB u K (hrs.trans hsu) 2 (by norm_num))
    have hq := empiricalInf_le N r q hm s u hθ
    simp only [empiricalExpression, hEnd, zero_add] at hmin hq
    linarith

theorem negativeMargin_mono {k N n L a : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    {η η' : ℝ} (hη : η' ≤ η) (h : EmpiricalNegativeMargin N a cuts hn η) :
    EmpiricalNegativeMargin N a cuts hn η' :=
  ⟨h.1.trans (neg_le_neg hη), fun s u hs hsu hu =>
    (h.2 s u hs hsu hu).trans (neg_le_neg hη)⟩

/-- Exact finite deletion loss, before any asymptotic rounding is absorbed. -/
theorem deletePrefixMargin {k N K r : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (p : Cuts k N K) (hrK : r ≤ K) {η : ℝ}
    (hmargin : EmpiricalNegativeMargin N 0 p (by omega) η) :
    EmpiricalNegativeMargin N r (suffixCuts p r) (by omega)
      (η-(7/2 : ℝ)*((r : ℝ)*Real.log (k : ℝ)/logScale N)) := by
  let hn : 0 < N := by omega
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hprefix : empiricalA N 0 p hn 0 r ≤ (r : ℝ)*Real.log (k : ℝ)/logScale N := by
    rw [empiricalA_grid_adapter hN 0 p hn (Nat.zero_le r)]
    simp only [Nat.sub_zero, gridTime, Nat.cast_zero, zero_div]
    have hh := RiffleLowerV2.ProfileTransfer.empiricalIntegral_le hN
      (fun j => (TimeProfile.maxCost_bounds hk (p.profile hn j)).2)
      (le_refl 0) (div_nonneg (Nat.cast_nonneg r) (logScale_pos hN).le)
      (show (r : ℝ)/logScale N ≤ horizon N K from
        div_le_div_of_nonneg_right (by exact_mod_cast hrK) (logScale_pos hN).le)
    convert hh using 1 <;> first | rfl | ring
  have hscale : Real.log (N : ℝ)/Real.log (N : ℝ) = 1 :=
    div_self (logScale_pos hN).ne'
  have h := inducedMargin hk hN p (suffixCuts p r) hn hrK
    (T := (K : ℝ)/logScale N) (e := (r : ℝ)*Real.log (k : ℝ)/logScale N)
    (ζ := 0) (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog) (logScale_pos hN).le) (by rfl)
    (by rw [div_mul_cancel₀ _ (logScale_pos hN).ne']) hmargin
    (by rw [hscale]; linarith) (by intro j l; simp)
  simpa using h

/-- If at most rho*log N+b columns are removed, the rounding loss is displayed
as (7/2)*b*log k/log N; b is an explicit finite constant. -/
theorem deletePrefixMargin_rounding {k N K r : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (p : Cuts k N K) (hrK : r ≤ K) {η ρ b : ℝ}
    (hlength : (r : ℝ) ≤ ρ*logScale N+b)
    (hmargin : EmpiricalNegativeMargin N 0 p (by omega) η) :
    EmpiricalNegativeMargin N r (suffixCuts p r) (by omega)
      (η-(7/2 : ℝ)*ρ*Real.log (k : ℝ)-
        (7/2 : ℝ)*b*Real.log (k : ℝ)/logScale N) := by
  apply negativeMargin_mono _ _ _ (deletePrefixMargin hk hN p hrK hmargin)
  have hlog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hlength hlog)
    (logScale_pos hN).le
  have heq : (ρ*logScale N+b)*Real.log (k : ℝ)/logScale N =
      ρ*Real.log (k : ℝ)+b*Real.log (k : ℝ)/logScale N := by
    field_simp [(logScale_pos hN).ne']
  rw [heq] at hh
  convert sub_le_sub_left (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 7/2)) η using 1 <;> first | rfl | ring

end RiffleUpperV2.Margins
