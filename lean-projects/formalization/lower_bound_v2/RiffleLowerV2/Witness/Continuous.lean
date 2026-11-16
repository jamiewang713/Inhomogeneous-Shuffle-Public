import RiffleLowerV2.Witness.OneColumn
import RiffleLowerV2.Witness.Empirical
import RiffleLowerV2.Witness.Selection

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.Witness
open TimeProfile

private theorem tilt_interval_subset : Icc (3 : ℝ) 4 ⊆ Icc (2 : ℝ) 4 := by
  intro a ha
  exact ⟨by linarith [ha.1], ha.2⟩

private theorem continuous_B_alpha {k N K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (s u : ℝ) :
    ContinuousOn (fun a => B cuts hN a s u) (Icc (3 : ℝ) 4) := by
  exact continuousOn_empiricalIntegral_param
    (fun j => (continuousOn_psi (cuts.profile hN j)).mono tilt_interval_subset) s u

private theorem witness_B_nonneg {k N K : ℕ} (hk : 2 ≤ k) (hN2 : 2 ≤ N)
    (cuts : Cuts k N K) (hN : 0 < N) {a s u : ℝ}
    (ha : a ∈ Icc (2 : ℝ) 4) (hsu : s ≤ u) : 0 ≤ B cuts hN a s u :=
  empiricalIntegral_nonneg hN2 (fun j => (psi_sharp_bounds hk (cuts.profile hN j) ha).1) hsu

/-- The exact change under a backward endpoint displacement. -/
theorem F_move_eq {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (a s v u : ℝ) :
    F cuts hN a s v - F cuts hN a s u =
      B cuts hN a v u - 2*B cuts hN 2 v u := by
  have h1 := empiricalIntegral_add N (fun j => psi (cuts.profile hN j) a) s v u
  have h2 := empiricalIntegral_add N (fun j => psi (cuts.profile hN j) 2)
    v u (horizon N K)
  change B cuts hN a s u = B cuts hN a s v + B cuts hN a v u at h1
  change B cuts hN 2 v (horizon N K) =
    B cuts hN 2 v u + B cuts hN 2 u (horizon N K) at h2
  unfold F
  linarith

private theorem witness_integral_smul {N K : ℕ} (f : Fin K → ℝ) (a s u : ℝ) :
    empiricalIntegral N (fun j => a*f j) s u = a*empiricalIntegral N f s u := by
  simp only [empiricalIntegral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The continuous, shortened witness, prior to the deterministic grid construction. -/
theorem continuousWitness {k N K : ℕ} (hk : 2 ≤ k) (hN2 : 2 ≤ N)
    (cuts : Cuts k N K) (hN : 0 < N) {eta : ℝ} (heta : 0 < eta)
    (hmargin : eta ≤ lambda1 cuts hN) :
    ∃ s u theta : ℝ, (s,u) ∈ triangle (horizon N K) ∧
      theta ∈ Icc (3 : ℝ) 4 ∧ eta/4 ≤ beta cuts hN s ∧
      J cuts hN theta s u ≤ beta cuts hN s/2-4*kappa eta ∧
      (theta = 3 ∨ J cuts hN theta s u = beta cuts hN s/2-4*kappa eta) ∧
      7*eta/8-16*kappa eta ≤ F cuts hN theta s u := by
  have hL := logScale_pos hN2
  have hS : 0 ≤ horizon N K := by unfold horizon; positivity
  have hFcont (su : ℝ × ℝ) (_hsu : su ∈ triangle (horizon N K)) :
      ContinuousOn (fun a => F cuts hN a su.1 su.2) (Icc (3 : ℝ) 4) := by
    unfold F
    exact (((continuousOn_id.add continuousOn_const).div_const 2).mul continuousOn_const).sub
      (continuous_B_alpha cuts hN su.1 su.2) |>.sub continuousOn_const
  have hFbound (su : ℝ × ℝ) (hsu : su ∈ triangle (horizon N K)) :
      F cuts hN 3 su.1 su.2 ≤ 3 := by
    obtain ⟨hs, hsu, hu⟩ := hsu
    have hA : 0 ≤ A cuts hN 0 su.1 :=
      empiricalIntegral_nonneg hN2 (fun j => (maxCost_bounds hk (cuts.profile hN j)).1) hs
    have hB := witness_B_nonneg hk hN2 cuts hN (by norm_num : (3 : ℝ) ∈ Icc 2 4) hsu
    have hB2 := witness_B_nonneg hk hN2 cuts hN (by norm_num : (2 : ℝ) ∈ Icc 2 4) hu
    unfold F beta
    norm_num
    linarith
  obtain ⟨s, u, hsu, hall⟩ := variational_pair (fun a s u => F cuts hN a s u)
    (horizon N K) eta 3 hS heta hFcont hFbound hmargin
  obtain ⟨hs0, hsule, huS⟩ := hsu
  have hb : eta/4 ≤ beta cuts hN s := by
    have hf := hall 4 (by norm_num)
    have hB := witness_B_nonneg hk hN2 cuts hN (by norm_num : (4 : ℝ) ∈ Icc 2 4) hsule
    have hB2 := witness_B_nonneg hk hN2 cuts hN (by norm_num : (2 : ℝ) ∈ Icc 2 4) huS
    unfold F at hf
    norm_num at hf
    linarith
  have hJa : ContinuousOn (fun a => J cuts hN a s u) (Icc (3 : ℝ) 4) :=
    continuousOn_empiricalIntegral_param
      (fun j => (continuousOn_tiltedCost (cuts.profile hN j)).mono tilt_interval_subset) s u
  have hJt (a : ℝ) (_ha : a ∈ Icc (3 : ℝ) 4) :
      ContinuousOn (fun v => J cuts hN a s v) (Icc s u) := by
    exact ((continuous_empiricalIntegral (fun j => tiltedCost (cuts.profile hN j) a)).comp
      (continuous_const.prodMk continuous_id)).continuousOn
  have hJzero (a : ℝ) (_ha : a ∈ Icc (3 : ℝ) 4) : J cuts hN a s s = 0 :=
    empiricalIntegral_self _ _ _
  have hB2J (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) (v : ℝ) (hv : v ∈ Icc s u) :
      B cuts hN 2 v u ≤ 2*J cuts hN a v u := by
    have hpoint (j : Fin K) : psi (cuts.profile hN j) 2 ≤
        2*tiltedCost (cuts.profile hN j) a :=
      (psi_two_le_maxCost _).trans (mul_le_mul_of_nonneg_left
        (maxCost_le_tiltedCost _ (by linarith [ha.1])) (by norm_num))
    have hi := empiricalIntegral_mono hN2 hpoint hv.2
    rw [witness_integral_smul] at hi
    exact hi
  have hloss (a : ℝ) (ha : a ∈ Icc (3 : ℝ) 4) (v : ℝ) (hv : v ∈ Icc s u) :
      -4*(J cuts hN a s u-J cuts hN a s v) ≤
        F cuts hN a s v-F cuts hN a s u := by
    rw [F_move_eq]
    have hB := witness_B_nonneg hk hN2 cuts hN (tilt_interval_subset ha) hv.2
    have hcomp := hB2J a ha v hv
    have hsplit := empiricalIntegral_add N
      (fun j => tiltedCost (cuts.profile hN j) a) s v u
    change J cuts hN a s u = J cuts hN a s v + J cuts hN a v u at hsplit
    linarith
  have hfour (v : ℝ) (hv : v ∈ Icc s u) :
      F cuts hN 4 s u ≤ F cuts hN 4 s v := by
    have hpoint (j : Fin K) : 2*psi (cuts.profile hN j) 2 ≤ psi (cuts.profile hN j) 4 :=
      psi_four_ge_two _
    have hi := empiricalIntegral_mono hN2 hpoint hv.2
    rw [witness_integral_smul] at hi
    change 2*B cuts hN 2 v u ≤ B cuts hN 4 v u at hi
    have hmove := F_move_eq cuts hN 4 s v u
    linarith
  obtain ⟨theta, htheta, v, hv, hjup, hjlo, hf⟩ :=
    shorten_selection (fun a v => J cuts hN a s v) (fun a v => F cuts hN a s v)
      s u (beta cuts hN s) eta heta hsule hb hJa hJt hJzero hall hloss hfour
  exact ⟨s, v, theta, ⟨hs0, hv.1, hv.2.trans huS⟩, htheta, hb, hjup, hjlo, hf⟩

end RiffleLowerV2.Witness
