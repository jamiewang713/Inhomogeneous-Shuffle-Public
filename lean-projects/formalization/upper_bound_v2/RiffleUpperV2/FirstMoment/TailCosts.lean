import RiffleUpperV2.FirstMoment.TailGrid
import RiffleUpperV2.Localization.CollisionMass

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization Hypergeometric

/-- The literal future collision product in probability coordinates. -/
theorem tailSquareMass_product {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (x : Prefix k d) :
    tailSquareMass cuts x = ∏ j ∈ empiricalPositions d 0 x.1.val d,
      powerSum (cuts.profile hn j) 2 := by
  classical
  unfold tailSquareMass empiricalPositions
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j.val < x.1.val
  · simp [hj,show ¬x.1.val ≤ j.val by omega]
  · simp [hj,show x.1.val ≤ j.val by omega,j.isLt,powerSum,Cuts.profile_prob,Real.rpow_two]

theorem tailSquareMass_pos {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (x : Prefix k d) : 0 < tailSquareMass cuts x := by
  rw [tailSquareMass_product cuts hn]
  exact Finset.prod_pos (fun j _ => powerSum_pos _ (by norm_num))

/-- Exact suffix collision exponent on the original logarithmic scale. -/
theorem tailSquareMass_log {k n d N : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (a : ℕ) (x : Prefix k d) :
    Real.log (tailSquareMass cuts x)/logScale N =
      -empiricalB N a cuts hn 2 (a+x.1.val) (a+d) := by
  rw [tailSquareMass_product cuts hn,Real.log_prod
    (fun j _ => (powerSum_pos (cuts.profile hn j) (by norm_num : (1 : ℝ) ≤ 2)).ne')]
  simp [empiricalB,RiffleLowerV2.gridSum,empiricalPositions,psi,Finset.sum_neg_distrib,neg_div]

/-- Positive scalars are exactly recovered from their original-scale exponent. -/
theorem rpow_normalizedExponent {N : ℕ} (hN : 2 ≤ N) (mu : ℝ) (hmu : 0 < mu) :
    (N : ℝ)^(normalizedExponent N mu) = mu := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Real.rpow_def_of_pos hNpos,normalizedExponent]
  rw [mul_div_cancel₀ _ (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne']
  exact Real.exp_log hmu

theorem tailSquareMass_rpow {k n d N : ℕ} (hN : 2 ≤ N) (cuts : Cuts k n d)
    (hn : 0 < n) (a : ℕ) (x : Prefix k d) :
    tailSquareMass cuts x = (N : ℝ)^(-empiricalB N a cuts hn 2 (a+x.1.val) (a+d)) := by
  rw [← tailSquareMass_log cuts hn a x]
  exact (rpow_normalizedExponent hN _ (tailSquareMass_pos cuts hn x)).symm

/-- After first-column exposure, the exact suffix exponent is the one in the
original array's margin, with no anchor or prefix column counted twice. -/
theorem firstPileTail_rpow {k n d N : ℕ} (hN : 2 ≤ N) (cuts : Cuts k n (d+1))
    (hn : 0 < n) (a : ℕ) (x : Prefix k d) :
    tailSquareMass (tailCuts cuts) x =
      (N : ℝ)^(-empiricalB N a cuts hn 2 (a+1+x.1.val) (a+(d+1))) := by
  have h := tailSquareMass_rpow hN (tailCuts cuts) hn (a+1) x
  rw [empiricalB_tailCuts cuts hn a (a+1+x.1.val) (a+1+d) (by omega) 2] at h
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

/-- The mean factor appearing in the literal density estimates is exactly N^ell. -/
theorem anchoredMean_rpow {k n d N : ℕ} (hN : 2 ≤ N) (cuts : Cuts k n d)
    (R : Finset (Fin n)) (x : Prefix k d) (hx : Legal cuts R x) :
    anchoredMean cuts R x = (N : ℝ)^(meanExponent N cuts R x) :=
  (rpow_normalizedExponent hN _ hx).symm

end RiffleUpperV2.FirstMoment
