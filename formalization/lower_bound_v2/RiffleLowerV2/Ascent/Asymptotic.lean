import RiffleLowerV2.Ascent.Quantitative
import RiffleLowerV2.Ascent.Selection

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology
namespace RiffleLowerV2.Ascent

/-- Finite graph scan success, using the fixed graph-only least successful translate. -/
theorem graph_scan_ge_of_comparison (hc : Targets.ComponentComparison)
    {N : ℕ} (H0 : Finset ℤ) (G : PathEdges N) {D δ : ℝ}
    (hM : (0 : ℝ) < H0.card)
    (hsize : 576 ≤ (H0.card : ℝ)^δ) (hD : 24*D ≤ (H0.card : ℝ)^δ)
    (hd : ∀ q : Fin (N+1), ((boundary (clipTranslate N H0 q.val)).card : ℝ) ≤
      D * Real.sqrt H0.card)
    (hr : ∃ q : Fin (N+1), ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ) ≥
      (H0.card : ℝ)^(1/2+δ)) :
    1 - Real.exp (-(H0.card : ℝ)^(2*δ)/144) ≤
      probability (uniformPermutation N) (fun π =>
        scan H0 ((H0.card : ℝ)^(1/2+δ/2)) (componentSort G π)) := by
  let q := chosenTranslate H0 G ((H0.card : ℝ)^(1/2+δ))
  have hq := (chosenTranslate_spec H0 G ((H0.card : ℝ)^(1/2+δ)) hr).1
  have hf := quantitative_component_failure hc G (clipTranslate N H0 q.val) hM
    (by exact_mod_cast clipTranslate_card_le N H0 q.val) hsize hD hq (hd q)
  let failure := fun π =>
    (ascentCount (clipTranslate N H0 q.val) (componentSort G π) : ℝ) ≤
      ((internalEdges (clipTranslate N H0 q.val)).card : ℝ)/2+
        (H0.card : ℝ)^(1/2+δ/2)
  calc
    _ ≤ 1 - probability (uniformPermutation N) failure := sub_le_sub_left hf 1
    _ = probability (uniformPermutation N) (fun π => ¬ failure π) :=
      (probability_not _ _).symm
    _ ≤ _ := by
      apply probability_mono
      intro π hπ
      exact ⟨q, lt_of_not_ge hπ⟩

/-- The conditional failure envelope tends to zero uniformly once M≥N^a. -/
theorem failure_envelope_tendsto_zero {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)^(a*(2*δ))/144)) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(a*(2*δ))) atTop atTop :=
    (tendsto_rpow_atTop (mul_pos ha (mul_pos (by norm_num) hδ))).comp
      tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hp.atTop_div_const (by norm_num : (0 : ℝ) < 144))
  simpa only [Function.comp_def, neg_div] using hh

/-- Quantifier order is uniform in every graph and every deterministic integer set. -/
theorem uniformGraphScan_of_comparison (hc : Targets.ComponentComparison) :
    Targets.UniformGraphScan := by
  intro a δ D ε ha hδ _hD hε
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^(a*δ)) atTop atTop :=
    (tendsto_rpow_atTop (mul_pos ha hδ)).comp tendsto_natCast_atTop_atTop
  have he := (failure_envelope_tendsto_zero ha hδ).eventually (gt_mem_nhds hε)
  have hall : ∀ᶠ N : ℕ in atTop, ∀ (H0 : Finset ℤ) (G : PathEdges N),
      (N : ℝ)^a ≤ (H0.card : ℝ) →
      (∀ q : Fin (N+1), ((boundary (clipTranslate N H0 q.val)).card : ℝ) ≤
        D * Real.sqrt H0.card) →
      (∃ q : Fin (N+1), ((G ∩ internalEdges (clipTranslate N H0 q.val)).card : ℝ) ≥
        (H0.card : ℝ)^(1/2+δ)) →
      probability (uniformPermutation N) (fun π =>
        scan H0 ((H0.card : ℝ)^(1/2+δ/2)) (componentSort G π)) ≥ 1-ε := by
    filter_upwards [eventually_ge_atTop (1 : ℕ), hp.eventually (eventually_ge_atTop 576),
      hp.eventually (eventually_ge_atTop (24*D)), he] with N hN hsize hD' he'
    intro H0 G hNM hd hr
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hM : (0 : ℝ) < H0.card := (Real.rpow_pos_of_pos hNpos a).trans_le hNM
    have hpow : (N : ℝ)^(a*δ) ≤ (H0.card : ℝ)^δ := by
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hNM hδ.le
    have hpow₂ : (N : ℝ)^(a*(2*δ)) ≤ (H0.card : ℝ)^(2*δ) := by
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hNM (by positivity)
    have hbound := graph_scan_ge_of_comparison hc H0 G hM
      (hsize.trans hpow) (hD'.trans hpow) hd hr
    have hsmall : Real.exp (-(H0.card : ℝ)^(2*δ)/144) < ε := by
      refine lt_of_le_of_lt (Real.exp_le_exp.mpr ?_) he'
      exact div_le_div_of_nonneg_right (neg_le_neg hpow₂) (by norm_num)
    linarith
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hall
  refine ⟨max N0 1, ?_⟩
  intro N hN
  exact hN0 N (le_trans (le_max_left N0 1) hN)

/-- Exact exponent at the observable test threshold. -/
theorem scan_threshold_sq_div {M δ : ℝ} (hM : 0 < M) :
    (M^(1/2+δ/2))^2/M = M^δ := by
  have hp : (M^(1/2+δ/2))^2 = M*M^δ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (1/2+δ/2)*(2 : ℝ) = 1+δ by ring,
      Real.rpow_add hM, Real.rpow_one]
  rw [hp]
  field_simp

/-- The polynomial number of shifts is dominated by stretched-exponential decay. -/
theorem null_scan_envelope_tendsto_zero {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun N : ℕ => ((N : ℝ)+1)*Real.exp (-(N : ℝ)^β)) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ)^β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp tendsto_natCast_atTop_atTop
  have hfirst := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/β) 1
    (by norm_num)).comp hp
  have hrexp (N : ℕ) : ((N : ℝ)^β)^(1/β) = N := by
    rw [← Real.rpow_mul (Nat.cast_nonneg N), mul_one_div_cancel hβ.ne', Real.rpow_one]
  simp only [Function.comp_def, hrexp, neg_mul, one_mul] at hfirst
  have hsecond := Real.tendsto_exp_neg_atTop_nhds_zero.comp hp
  convert hfirst.add hsecond using 1
  · funext N
    simp only [Function.comp_apply]
    ring
  · norm_num

/-- Uniform finite null scan estimate, with arbitrary integer support and no M≤N bound. -/
theorem uniform_null_scan_bound (hs : Targets.UniformScan) {N : ℕ}
    (hN : 0 < N) (H0 : Finset ℤ) {a δ : ℝ} (_ha : 0 < a) (hδ : 0 < δ)
    (hNM : (N : ℝ)^a ≤ (H0.card : ℝ)) :
    probability (uniformPermutation N) (scan H0 ((H0.card : ℝ)^(1/2+δ/2))) ≤
      ((N : ℝ)+1) * Real.exp (-(N : ℝ)^(a*δ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hM : (0 : ℝ) < H0.card := (Real.rpow_pos_of_pos hNpos a).trans_le hNM
  have hf := hs N H0 ((H0.card : ℝ)^(1/2+δ/2))
    (by exact_mod_cast hM) (Real.rpow_pos_of_pos hM _)
  rw [neg_div, scan_threshold_sq_div hM] at hf
  refine hf.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  apply neg_le_neg
  rw [Real.rpow_mul hNpos.le]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hNM hδ.le

/-- Eventual null rejection is uniform after a,delta,epsilon and before N,H0. -/
theorem uniform_null_scan_eventually (hs : Targets.UniformScan)
    (a δ ε : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N ≥ N0, ∀ H0 : Finset ℤ,
      (N : ℝ)^a ≤ (H0.card : ℝ) →
      probability (uniformPermutation N) (scan H0 ((H0.card : ℝ)^(1/2+δ/2))) ≤ ε := by
  have he := (null_scan_envelope_tendsto_zero (mul_pos ha hδ)).eventually (gt_mem_nhds hε)
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp he
  refine ⟨max n0 1, le_max_right _ _, ?_⟩
  intro N hN H0 hM
  have hNp : 0 < N := by omega
  exact (uniform_null_scan_bound hs hNp H0 ha hδ hM).trans
    (hn0 N (le_trans (le_max_left _ _) hN)).le

end RiffleLowerV2.Ascent
