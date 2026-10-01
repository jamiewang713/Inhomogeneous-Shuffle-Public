import RiffleLowerV2.Occupancy.ConditionalInputs
import RiffleLowerV2.Occupancy.Marginal

noncomputable section
open scoped Topology
open Filter
namespace RiffleLowerV2.Occupancy
open TimeProfile

theorem logScale_le_two_logScale_sub {N b : ℕ}
    (hM : 2 ≤ N-b) (hNM : (N : ℝ) ≤ 2*(N-b : ℕ)) :
    logScale N ≤ 2*logScale (N-b) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMr : (0 : ℝ) < (N-b : ℕ) := by exact_mod_cast (show 0 < N-b by omega)
  have hlog := Real.log_le_log hNr hNM
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show (2 : ℝ) ≤ (N-b : ℕ) by exact_mod_cast hM)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hMr.ne'] at hlog
  dsimp [logScale]
  linarith

theorem tau_sub_le_two_tau {N b : ℕ}
    (hN : 0 < N) (hNM : (N : ℝ) ≤ 2*(N-b : ℕ)) :
    tau (N-b) ≤ 2*tau N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < (N-b : ℕ) := by nlinarith
  have hpow := Real.rpow_le_rpow_of_nonpos hNr hNM
    (by norm_num : (-1/100 : ℝ) ≤ 0)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hMr.le] at hpow
  have h2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (-1 : ℝ) ≤ -1/100)
  norm_num only [Real.rpow_neg_one] at h2
  have hh := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hMr.le (-1/100))
  dsimp [tau]
  nlinarith

/-- A single threshold handles every bounded deletion, before the cuts and word. -/
theorem eventual_residual_budgets (c C D : ℝ) (hc : 0 < c)
    (b0 M0 : ℕ) :
    ∃ N0 : ℕ, b0 < N0 ∧ 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ b ≤ b0,
      b < N ∧ 2 ≤ N-b ∧ M0 ≤ N-b ∧
      2*(b : ℝ) ≤ c*N ∧ (N : ℝ) ≤ 2*(N-b : ℕ) ∧
      logScale N ≤ 2*logScale (N-b) ∧ tau (N-b) ≤ 2*tau N ∧ tau N ≤ 1/2 ∧
      D*(C*logScale N+1)*(b0 : ℝ)/N ≤ tau N := by
  have herr := eventually_log_affine_mul_rpow_le (D*C*b0) (D*b0) (-1) (-1/100)
    (by norm_num)
  have ht := eventually_negative_rpow_le (by norm_num : (-1/100 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1/2)
  obtain ⟨N1,hN1⟩ := eventually_atTop.mp (herr.and ht)
  let N0 := max N1 (max (2*b0+2) (max (M0+b0) ⌈2*(b0 : ℝ)/c⌉₊))
  have hN02 : 2 ≤ N0 := by dsimp [N0]; omega
  have hb0N0 : b0 < N0 := by dsimp [N0]; omega
  refine ⟨N0,hb0N0,hN02,?_⟩
  intro N hN b hb
  have hNN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hlarge : 2*b0+2 ≤ N := by dsimp [N0] at hN; omega
  have hM0 : M0+b0 ≤ N := by dsimp [N0] at hN; omega
  have hceil : ⌈2*(b0 : ℝ)/c⌉₊ ≤ N := by dsimp [N0] at hN; omega
  have hbN : b < N := by omega
  have hbNr : (b : ℝ) ≤ N := by exact_mod_cast hbN.le
  have hcast : ((N-b : ℕ) : ℝ) = (N : ℝ)-b := Nat.cast_sub hbN.le
  have hNM : (N : ℝ) ≤ 2*(N-b : ℕ) := by
    rw [hcast]
    have hlargeR : 2*(b0 : ℝ)+2 ≤ N := by exact_mod_cast hlarge
    have hbR : (b : ℝ) ≤ b0 := by exact_mod_cast hb
    linarith
  have hbc0 : 2*(b0 : ℝ) ≤ c*N := by
    have hh : 2*(b0 : ℝ)/c ≤ N :=
      (Nat.le_ceil (2*(b0 : ℝ)/c)).trans (by exact_mod_cast hceil)
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith
  have hbc : 2*(b : ℝ) ≤ c*N := by
    have hbR : (b : ℝ) ≤ b0 := by exact_mod_cast hb
    linarith
  have hM2 : 2 ≤ N-b := by omega
  obtain ⟨herror,htN⟩ := hN1 N hNN1
  have herrN : D*(C*logScale N+1)*(b0 : ℝ)/N ≤ tau N := by
    rw [Real.rpow_neg_one] at herror
    dsimp [tau]
    convert herror using 1; ring
  exact ⟨hbN,hM2,by omega,hbc,hNM,logScale_le_two_logScale_sub hM2 hNM,
    tau_sub_le_two_tau (by omega) hNM,htN,herrN⟩

theorem residual_selected_piles {N k K b : ℕ} (cuts : Cuts k N K)
    (p : RowPrescription N k K b) (w : Word k K)
    (residual : Cuts k (N-b) K)
    (hres : ∀ j a, residual.count j a = cuts.count j a - usedCount p j a)
    {c : ℝ} (hc : 0 < c) (hbc : 2*(b : ℝ) ≤ c*N)
    (hpiles : ∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) :
    ∀ j, (c/2)*(N-b : ℕ) ≤ (residual.count j (w.get j) : ℝ) := by
  intro j
  have hu : (usedCount p j (w.get j) : ℝ) ≤ b := by
    exact_mod_cast Factorial.usedCount_le p j (w.get j)
  have hcN : 0 ≤ c*N := mul_nonneg hc.le (Nat.cast_nonneg N)
  have hused : usedCount p j (w.get j) ≤ cuts.count j (w.get j) := by
    exact_mod_cast (show (usedCount p j (w.get j) : ℝ) ≤ cuts.count j (w.get j) by
      linarith [hpiles j])
  rw [hres, Nat.cast_sub hused]
  have hpop : ((N-b : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N b
  have hpopc := mul_le_mul_of_nonneg_left hpop hc.le
  linarith [hpiles j]

/-- Actual-model conditional stability for arbitrary bounded prescriptions.
The tested word may itself be prescribed; all its prescribed copies are deleted. -/
theorem conditionalCollisionStability : Targets.ConditionalCollisionStability := by
  intro c C hc hC b0
  obtain ⟨D,hD,N1,hb1,hN12,hMean⟩ := Factorial.residualMeanComparison c C hc hC b0
  obtain ⟨M0,hM02,hMarginal⟩ := uniform_marginal (c/2) (2*C) (by positivity) (by positivity)
  obtain ⟨N2,hb2,hN22,hBudget⟩ := eventual_residual_budgets c C D hc b0 M0
  refine ⟨64,by norm_num,max N1 N2,lt_of_lt_of_le hb2 (le_max_right _ _),
    hN22.trans (le_max_right _ _),?_⟩
  intro N hN k K b hb hK cuts p w hinj hprob hpiles
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : N2 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hbN,hM2,hM0,hbc,hNM,hlog,htM,htN,herror⟩ := hBudget N hN2 b hb
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have ht0 := (tau_pos hNp).le
  obtain ⟨residual,hres,_hexpect,hprobability,hmean⟩ :=
    exists_residual_word_law cuts p hbN hinj hprob
  have hresPiles := residual_selected_piles cuts p w residual hres hc hbc hpiles
  have hKres : (K : ℝ) ≤ (2*C)*logScale (N-b) := by
    have hh := mul_le_mul_of_nonneg_left hlog hC.le
    nlinarith
  have hmarg := hMarginal (N-b) hM0 k K hKres residual w hresPiles
  let μ : ℝ := (N : ℝ)*wordMass cuts w
  let ν : ℝ := Targets.residualWordMean cuts p w
  let Q : ℝ := conditionalProbability (fixedCountPMF cuts)
    (fun ω => 2 ≤ wordCount w ω - (Finset.univ.filter fun q => p.word q = w).card)
    (prescriptionEvent p)
  have hμ : 0 < μ := wordMean_pos cuts w hc hNp hpiles
  have hclose := hMean N hN1 k K b hb hK cuts p w hinj hprob hpiles
  have hKplus : (K : ℝ)+1 ≤ C*logScale N+1 := by linarith
  have hplus : 0 ≤ C*logScale N+1 :=
    (by positivity : 0 ≤ (K : ℝ)+1).trans hKplus
  have hcoef : D*(K+1)*(b : ℝ)/N ≤ D*(C*logScale N+1)*(b0 : ℝ)/N := by
    apply div_le_div_of_nonneg_right _ hNr.le
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hKplus hD.le
    · exact_mod_cast hb
    · exact Nat.cast_nonneg b
    · exact mul_nonneg hD.le hplus
  have hmeanClose : |ν-μ| ≤ tau N*μ :=
    hclose.trans (mul_le_mul_of_nonneg_right (hcoef.trans herror) hμ.le)
  have hν : 0 < ν := by
    have hh := (abs_le.mp hmeanClose).1
    have hh' := mul_le_mul_of_nonneg_right htN hμ.le
    nlinarith
  have hstable := poissonCollision_stability hμ hν ht0 (by linarith : tau N ≤ 1) hmeanClose
  have hmarg' : |Q-poissonCollision ν| ≤ 8*tau (N-b)*poissonCollision ν := by
    rw [hmean w] at hmarg
    change |probability (fixedCountPMF residual) (fun ω => 2 ≤ wordCount w ω) -
      poissonCollision ν| ≤ 8*tau (N-b)*poissonCollision ν at hmarg
    rw [← hprobability w (fun n => 2 ≤ n)] at hmarg
    exact hmarg
  have hfμ := (poissonCollision_pos hμ).le
  have hfν := (poissonCollision_pos hν).le
  have hmarg'' : |Q-poissonCollision ν| ≤ 16*tau N*poissonCollision ν := by
    have hh := mul_le_mul_of_nonneg_right htM hfν
    nlinarith
  have hfbound : poissonCollision ν ≤ (5/2)*poissonCollision μ := by
    have hh := (abs_le.mp hstable).2
    have hh' := mul_le_mul_of_nonneg_right htN hfμ
    nlinarith
  have hbound := mul_le_mul_of_nonneg_left hfbound (by positivity : 0 ≤ 16*tau N)
  have htri := abs_sub_le Q (poissonCollision ν) (poissonCollision μ)
  change |Q-poissonCollision μ| ≤ 64*tau N*poissonCollision μ
  nlinarith [mul_nonneg ht0 hfμ]

end RiffleLowerV2.Occupancy
