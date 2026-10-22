import RiffleLowerV2.Witness.Empirical
import RiffleLowerV2.Witness.OneColumn

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2.Witness
open TimeProfile

private theorem column_bounds (hc : Targets.OneColumnTiltTarget) {k : ℕ}
    (hk : 2 ≤ k) (p : Simplex k) {a : ℝ} (ha : a ∈ Icc (2 : ℝ) 4) :
    0 ≤ tiltedEntropy p a ∧ tiltedEntropy p a ≤ tiltedCost p a ∧
    tiltedCost p a ≤ Real.log k ∧ maxCost p ≤ tiltedCost p a ∧
    0 ≤ psi p a ∧ psi p a ≤ (a-1)*Real.log k ∧
    tiltedEntropy p a = a*tiltedCost p a - psi p a :=
  (hc k hk p).2.2.2.2.1 a ha

theorem A_bounds {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) (hpos : 0 < N) {r s : ℝ}
    (hr0 : 0 ≤ r) (hrs : r ≤ s) (hsK : s ≤ horizon N K) :
    0 ≤ A cuts hpos r s ∧ A cuts hpos r s ≤ (s-r)*Real.log k := by
  exact ⟨empiricalIntegral_nonneg hN (fun j => (maxCost_bounds hk _).1) hrs,
    empiricalIntegral_le hN (fun j => (maxCost_bounds hk _).2) hr0 hrs hsK⟩

theorem J_bounds (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s : ℝ} (ha : a ∈ Icc (2 : ℝ) 4)
    (hr0 : 0 ≤ r) (hrs : r ≤ s) (hsK : s ≤ horizon N K) :
    0 ≤ J cuts hpos a r s ∧ J cuts hpos a r s ≤ (s-r)*Real.log k := by
  exact ⟨empiricalIntegral_nonneg hN
    (fun j => (column_bounds hc hk _ ha).1.trans (column_bounds hc hk _ ha).2.1) hrs,
    empiricalIntegral_le hN (fun j => (column_bounds hc hk _ ha).2.2.1) hr0 hrs hsK⟩

theorem H_bounds (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s : ℝ} (ha : a ∈ Icc (2 : ℝ) 4) (hrs : r ≤ s) :
    0 ≤ H cuts hpos a r s ∧ H cuts hpos a r s ≤ J cuts hpos a r s := by
  exact ⟨empiricalIntegral_nonneg hN (fun j => (column_bounds hc hk _ ha).1) hrs,
    empiricalIntegral_mono hN (fun j => (column_bounds hc hk _ ha).2.1) hrs⟩

theorem B_bounds (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s : ℝ} (ha : a ∈ Icc (2 : ℝ) 4)
    (hr0 : 0 ≤ r) (hrs : r ≤ s) (hsK : s ≤ horizon N K) :
    0 ≤ B cuts hpos a r s ∧
    B cuts hpos a r s ≤ (s-r)*((a-1)*Real.log k) := by
  exact ⟨empiricalIntegral_nonneg hN (fun j => (column_bounds hc hk _ ha).2.2.2.2.1) hrs,
    empiricalIntegral_le hN (fun j => (column_bounds hc hk _ ha).2.2.2.2.2.1) hr0 hrs hsK⟩

theorem H_identity (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (cuts : Cuts k N K) (hpos : 0 < N)
    {a : ℝ} (ha : a ∈ Icc (2 : ℝ) 4) (r s : ℝ) :
    H cuts hpos a r s = a*J cuts hpos a r s-B cuts hpos a r s := by
  unfold H J B
  simp_rw [(column_bounds hc hk _ ha).2.2.2.2.2.2]
  exact empiricalIntegral_linear _ _ _ _ _

theorem A_le_J (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s : ℝ} (ha : a ∈ Icc (2 : ℝ) 4) (hrs : r ≤ s) :
    A cuts hpos r s ≤ J cuts hpos a r s :=
  empiricalIntegral_mono hN (fun _j => (column_bounds hc hk _ ha).2.2.2.1) hrs

theorem B_two_le_A (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {r s : ℝ} (hrs : r ≤ s) : B cuts hpos 2 r s ≤ 2*A cuts hpos r s := by
  have hi := empiricalIntegral_mono hN
    (fun j => (hc k hk (cuts.profile hpos j)).2.2.2.2.2.1) hrs
  have heq := empiricalIntegral_linear (N := N)
    (fun j => maxCost (cuts.profile hpos j)) (fun _ => 0) 2 r s
  simp only [sub_zero, empiricalIntegral, mul_zero, zero_div, Finset.sum_const_zero] at heq
  exact hi.trans_eq heq

theorem B_four_ge_two (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {r s : ℝ} (hrs : r ≤ s) : 2*B cuts hpos 2 r s ≤ B cuts hpos 4 r s := by
  have hi := empiricalIntegral_mono hN
    (fun j => (hc k hk (cuts.profile hpos j)).2.2.2.2.2.2) hrs
  have heq := empiricalIntegral_linear (N := N)
    (fun j => psi (cuts.profile hpos j) 2) (fun _ => 0) 2 r s
  simp only [sub_zero, empiricalIntegral, mul_zero, zero_div, Finset.sum_const_zero] at heq
  change 2*(∑ j, _*psi (cuts.profile hpos j) 2/logScale N) ≤ _
  rw [← heq]
  exact hi

theorem B_two_le_J (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s : ℝ} (ha : a ∈ Icc (2 : ℝ) 4) (hrs : r ≤ s) :
    B cuts hpos 2 r s ≤ 2*J cuts hpos a r s :=
  (B_two_le_A hc hk hN cuts hpos hrs).trans
    (mul_le_mul_of_nonneg_left (A_le_J hc hk hN cuts hpos ha hrs) (by norm_num))

theorem continuousOn_J_alpha (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (cuts : Cuts k N K) (hpos : 0 < N) (r s : ℝ) :
    ContinuousOn (fun a => J cuts hpos a r s) (Icc (2 : ℝ) 4) :=
  continuousOn_empiricalIntegral_param (fun j => (hc k hk (cuts.profile hpos j)).1) r s

theorem continuousOn_B_alpha (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (cuts : Cuts k N K) (hpos : 0 < N) (r s : ℝ) :
    ContinuousOn (fun a => B cuts hpos a r s) (Icc (2 : ℝ) 4) :=
  continuousOn_empiricalIntegral_param (fun j => (hc k hk (cuts.profile hpos j)).2.2.2.1) r s

theorem continuousOn_H_alpha (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (cuts : Cuts k N K) (hpos : 0 < N) (r s : ℝ) :
    ContinuousOn (fun a => H cuts hpos a r s) (Icc (2 : ℝ) 4) :=
  continuousOn_empiricalIntegral_param (fun j => (hc k hk (cuts.profile hpos j)).2.2.1) r s

theorem antitoneOn_J_alpha (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {r s : ℝ} (hrs : r ≤ s) :
    AntitoneOn (fun a => J cuts hpos a r s) (Icc (2 : ℝ) 4) := by
  intro a ha b hb hab
  exact empiricalIntegral_mono hN
    (fun j => (hc k hk (cuts.profile hpos j)).2.1 ha hb hab) hrs

theorem continuous_J_time {k N K : ℕ} (cuts : Cuts k N K) (hpos : 0 < N)
    (a r : ℝ) : Continuous (J cuts hpos a r) := by
  unfold J
  exact (continuous_empiricalIntegral _).comp (continuous_const.prodMk continuous_id)

theorem continuous_B_time {k N K : ℕ} (cuts : Cuts k N K) (hpos : 0 < N)
    (a r : ℝ) : Continuous (B cuts hpos a r) := by
  unfold B
  exact (continuous_empiricalIntegral _).comp (continuous_const.prodMk continuous_id)

theorem continuous_H_time {k N K : ℕ} (cuts : Cuts k N K) (hpos : 0 < N)
    (a r : ℝ) : Continuous (H cuts hpos a r) := by
  unfold H
  exact (continuous_empiricalIntegral _).comp (continuous_const.prodMk continuous_id)

theorem A_endpoint_bound {k N K : ℕ} (hk : 2 ≤ k) (hN : 2 ≤ N)
    (cuts : Cuts k N K) (hpos : 0 < N) {r s r' s' : ℝ}
    (hr : r ∈ Icc (0 : ℝ) (horizon N K)) (hs : s ∈ Icc (0 : ℝ) (horizon N K))
    (hr' : r' ∈ Icc (0 : ℝ) (horizon N K)) (hs' : s' ∈ Icc (0 : ℝ) (horizon N K)) :
    |A cuts hpos r s-A cuts hpos r' s'| ≤ (|r-r'|+|s-s'|)*Real.log k :=
  empiricalIntegral_endpoint_bound hN (fun j => by
    rw [abs_of_nonneg (maxCost_bounds hk _).1]; exact (maxCost_bounds hk _).2) hr hs hr' hs'

theorem J_endpoint_bound (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s r' s' : ℝ} (ha : a ∈ Icc (2 : ℝ) 4)
    (hr : r ∈ Icc (0 : ℝ) (horizon N K)) (hs : s ∈ Icc (0 : ℝ) (horizon N K))
    (hr' : r' ∈ Icc (0 : ℝ) (horizon N K)) (hs' : s' ∈ Icc (0 : ℝ) (horizon N K)) :
    |J cuts hpos a r s-J cuts hpos a r' s'| ≤ (|r-r'|+|s-s'|)*Real.log k :=
  empiricalIntegral_endpoint_bound hN (fun j => by
    rw [abs_of_nonneg ((column_bounds hc hk _ ha).1.trans (column_bounds hc hk _ ha).2.1)]
    exact (column_bounds hc hk _ ha).2.2.1) hr hs hr' hs'

theorem B_endpoint_bound (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s r' s' : ℝ} (ha : a ∈ Icc (2 : ℝ) 4)
    (hr : r ∈ Icc (0 : ℝ) (horizon N K)) (hs : s ∈ Icc (0 : ℝ) (horizon N K))
    (hr' : r' ∈ Icc (0 : ℝ) (horizon N K)) (hs' : s' ∈ Icc (0 : ℝ) (horizon N K)) :
    |B cuts hpos a r s-B cuts hpos a r' s'| ≤ (|r-r'|+|s-s'|)*((a-1)*Real.log k) :=
  empiricalIntegral_endpoint_bound hN (fun j => by
    rw [abs_of_nonneg (column_bounds hc hk _ ha).2.2.2.2.1]
    exact (column_bounds hc hk _ ha).2.2.2.2.2.1) hr hs hr' hs'

theorem H_endpoint_bound (hc : Targets.OneColumnTiltTarget) {k N K : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (cuts : Cuts k N K) (hpos : 0 < N)
    {a r s r' s' : ℝ} (ha : a ∈ Icc (2 : ℝ) 4)
    (hr : r ∈ Icc (0 : ℝ) (horizon N K)) (hs : s ∈ Icc (0 : ℝ) (horizon N K))
    (hr' : r' ∈ Icc (0 : ℝ) (horizon N K)) (hs' : s' ∈ Icc (0 : ℝ) (horizon N K)) :
    |H cuts hpos a r s-H cuts hpos a r' s'| ≤ (|r-r'|+|s-s'|)*Real.log k :=
  empiricalIntegral_endpoint_bound hN (fun j => by
    rw [abs_of_nonneg (column_bounds hc hk _ ha).1]
    exact (column_bounds hc hk _ ha).2.1.trans (column_bounds hc hk _ ha).2.2.1) hr hs hr' hs'

theorem empiricalTiltFrom (hc : Targets.OneColumnTiltTarget) : Targets.EmpiricalTiltTarget := by
  intro k N K hk hN cuts hpos a ha r s hr0 hrs hsK
  obtain ⟨hj0, hjle⟩ := J_bounds hc hk hN cuts hpos ha hr0 hrs hsK
  obtain ⟨hh0, hhle⟩ := H_bounds hc hk hN cuts hpos ha hrs
  exact ⟨hj0, hjle, hh0, hhle, H_identity hc hk cuts hpos ha r s⟩

theorem empiricalTilt : Targets.EmpiricalTiltTarget := empiricalTiltFrom oneColumnTilt

end RiffleLowerV2.Witness
