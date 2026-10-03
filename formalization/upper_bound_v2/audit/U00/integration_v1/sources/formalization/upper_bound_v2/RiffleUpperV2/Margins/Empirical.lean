import RiffleUpperV2.Shared.Empirical
import RiffleUpperV2.Margins.Scalar
import RiffleLowerV2.Thinning.MaximalWord

noncomputable section
open Set
open scoped BigOperators
namespace RiffleUpperV2.Margins
open TimeProfile RiffleLowerV2

/-- A finite scalar comparison on the original logarithmic scale. -/
theorem gridSum_stability {N L : ℕ} (hN : 2 ≤ N) {f g : Fin L → ℝ}
    {T D : ℝ} (hD : 0 ≤ D) (hL : (L : ℝ) ≤ T*logScale N)
    (hfg : ∀ j, |f j-g j| ≤ D) (s u : ℕ) :
    |gridSum N f s u-gridSum N g s u| ≤ T*D := by
  classical
  let I := Finset.univ.filter (fun j : Fin L => s ≤ j.val ∧ j.val < u)
  have hcard : (I.card : ℝ) ≤ L := by
    exact_mod_cast ((Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
      (Finset.card_fin L))
  have hsum : |∑ j ∈ I, (f j-g j)| ≤ (L : ℝ)*D := by
    calc
      _ ≤ ∑ j ∈ I, |f j-g j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ I, D := Finset.sum_le_sum fun j _ => hfg j
      _ = (I.card : ℝ)*D := by simp
      _ ≤ (L : ℝ)*D := mul_le_mul_of_nonneg_right hcard hD
  have hnum : |∑ j ∈ I, (f j-g j)| ≤ T*D*logScale N :=
    hsum.trans (by nlinarith [mul_le_mul_of_nonneg_right hL hD])
  unfold gridSum
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos (logScale_pos hN)]
  exact (div_le_iff₀ (logScale_pos hN)).mpr hnum

/-- Literal upper scalar-cost bounds for arbitrary populations n and m.
Neither probability vector is required to remain in a partition cell. -/
theorem costStability {k N n m L : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (a : ℕ) (p : Cuts k n L) (q : Cuts k m L) (hn : 0 < n) (hm : 0 < m)
    {T ζ : ℝ} (hζ : 0 ≤ ζ) (hL : (L : ℝ) ≤ T*logScale N)
    (hpq : ∀ j l, |prob (p.profile hn j) l-prob (q.profile hm j) l| ≤ ζ)
    (s u : ℕ) :
    |empiricalA N a p hn s u-empiricalA N a q hm s u| ≤ (k : ℝ)*T*ζ ∧
    ∀ θ ∈ Icc (2 : ℝ) 4,
      |empiricalB N a p hn θ s u-empiricalB N a q hm θ s u| ≤ 4*(k : ℝ)^4*T*ζ := by
  constructor
  · convert gridSum_stability hN (by positivity : 0 ≤ (k : ℝ)*ζ) hL
      (fun j => maxCost_stability hk (p.profile hn j) (q.profile hm j) hζ (hpq j))
      (s-a) (u-a) using 1 <;> first | rfl | ring
  · intro θ hθ
    convert gridSum_stability hN (by positivity : 0 ≤ 4*(k : ℝ)^4*ζ) hL
      (fun j => psi_stability hk (p.profile hn j) (q.profile hm j) hθ hζ (hpq j))
      (s-a) (u-a) using 1 <;> first | rfl | ring

/-- At integer absolute endpoints, the interpolated lower scalar API equals
the new upper sum after the explicit shift by a. -/
theorem empiricalA_grid_adapter {k N n L : ℕ} (hN : 2 ≤ N)
    (a : ℕ) (cuts : Cuts k n L) (hn : 0 < n) {s u : ℕ} (hsu : s ≤ u) :
    empiricalA N a cuts hn s u =
      empiricalIntegral N (fun j => maxCost (cuts.profile hn j))
        (gridTime N (s-a)) (gridTime N (u-a)) :=
  (empiricalIntegral_grid hN _ _ _ (Nat.sub_le_sub_right hsu a)).symm

theorem empiricalB_grid_adapter {k N n L : ℕ} (hN : 2 ≤ N)
    (a : ℕ) (cuts : Cuts k n L) (hn : 0 < n) (θ : ℝ)
    {s u : ℕ} (hsu : s ≤ u) :
    empiricalB N a cuts hn θ s u =
      empiricalIntegral N (fun j => psi (cuts.profile hn j) θ)
        (gridTime N (s-a)) (gridTime N (u-a)) :=
  (empiricalIntegral_grid hN _ _ _ (Nat.sub_le_sub_right hsu a)).symm

/-- The maximum-word product expressed on original scale N, for any current
population n and absolute initial column a. Empty products are included. -/
theorem maximalWordIdentity {k N n L : ℕ} (hN : 2 ≤ N)
    (a : ℕ) (cuts : Cuts k n L) (hn : 0 < n) :
    maximalMean cuts hn = (N : ℝ)^(empiricalBeta N a cuts hn (a+L)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hLog : logScale N ≠ 0 := (logScale_pos hN).ne'
  have hp : 0 < ∏ j, pileMax (cuts.profile hn j) :=
    Finset.prod_pos fun j _ => pileMax_pos _
  have hA : empiricalA N a cuts hn a (a+L) =
      (∑ j, maxCost (cuts.profile hn j))/logScale N := by
    simp [empiricalA, gridSum]
  rw [Real.rpow_def_of_pos hNr]
  apply Real.log_injOn_pos (mul_pos hnr hp) (Real.exp_pos _)
  change Real.log ((n : ℝ)*(∏ j, pileMax (cuts.profile hn j))) = _
  rw [Real.log_exp, Real.log_mul hnr.ne' hp.ne']
  rw [Real.log_prod (fun j _ => (pileMax_pos (cuts.profile hn j)).ne')]
  rw [empiricalBeta, hA]
  simp only [maxCost, digitCost, one_div, Real.log_inv, Finset.sum_neg_distrib]
  change _ = logScale N * (Real.log (n : ℝ)/logScale N - _)
  field_simp [hLog]
  ring

theorem maximalMean_le_of_terminalMargin {k N n L : ℕ} (hN : 2 ≤ N)
    (a : ℕ) (cuts : Cuts k n L) (hn : 0 < n) {η : ℝ}
    (hmargin : empiricalBeta N a cuts hn (a+L) ≤ -η) :
    maximalMean cuts hn ≤ (N : ℝ)^(-η) := by
  rw [maximalWordIdentity hN a cuts hn]
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (by omega : 1 ≤ N)) hmargin

end RiffleUpperV2.Margins
