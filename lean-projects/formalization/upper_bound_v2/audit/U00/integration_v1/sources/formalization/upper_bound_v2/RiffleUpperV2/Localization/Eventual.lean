import RiffleUpperV2.Localization.IrrelevantLoss
import RiffleUpperV2.Localization.Density
import RiffleUpperV2.Shared.WindowRates

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open Filter Topology
namespace RiffleUpperV2.Localization
open Anchor

theorem sideScale_eq_rpow {k n d : ℕ} (N : ℕ) (hN : 1 < N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    {χ : ℝ} {y z v : Prefix k d} (hpair : GenuineBoundaryPair cuts R χ y z v) :
    sideScale cuts R v = (N : ℝ)^(2*boundaryFluctuation N cuts R v) := by
  have hω : 0 < sideScale cuts R v :=
    (genuine_sideScale_pos cuts hn R hpair).1.trans_le (genuine_sideScale_pos cuts hn R hpair).2
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  unfold boundaryFluctuation fluctuation normalizedExponent
  rw [Real.rpow_def_of_pos hNpos]
  have he : Real.log (N : ℝ) * (2*(Real.log (sideScale cuts R v)/Real.log (N : ℝ)/2)) =
      Real.log (sideScale cuts R v) := by field_simp
  rw [he,Real.exp_log hω]

theorem crossingPenalty_eventually (χ δ : ℝ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → crossingPenalty N χ ≤ δ/2 := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlog.eventually (eventually_ge_atTop (Real.log (1/χ)/(δ/2))))
  refine ⟨max M 2,le_max_right _ _,?_⟩
  intro N hN
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  apply (div_le_iff₀ hl).mpr
  have h := (div_le_iff₀ (by positivity : (0:ℝ)<δ/2)).mp
    (hM N ((le_max_left _ _).trans hN))
  simpa only [Function.comp_apply,mul_comm] using h

/-- Uniform endpoint-window rate; N0 precedes all population, cut, anchor and word data. -/
theorem endpointWindow_eventually (T χ δ : ℝ) (hT : 0 ≤ T) (hχ : 0 < χ) (hδ : 0 < δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ (N k n d : ℕ), N0 ≤ N → (d : ℝ) ≤ T*Real.log (N : ℝ) →
      ∀ (cuts : Cuts k n d) (hn : 0<n) (c₀ : ℤ) (R : Finset (Fin n))
        (y z v x : Prefix k d), GenuineBoundaryPair cuts R χ y z v → IsPrefix v x →
        δ/2 ≤ boundaryFluctuation N cuts R v →
      probability (fixedCountPMF cuts) (fun ω =>
        (N : ℝ)^(boundaryFluctuation N cuts R v+δ/4) <
          max |(lowerEndpoint c₀ R x ω : ℝ)-meanLower cuts c₀ R x|
            |(upperEndpoint c₀ R x ω : ℝ)-meanUpper cuts c₀ R x|) ≤
        Real.exp (-(N : ℝ)^(δ/8)) := by
  obtain ⟨N0,hN0,h⟩ := endpointWindow_rate T χ δ hT hχ hδ
  refine ⟨N0,hN0,?_⟩
  intro N k n d hN hd cuts hn c₀ R y z v x hpair hvx hF
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hw := endpointWindow cuts hn c₀ R hpair hvx
    (Real.rpow_pos_of_pos hNp (boundaryFluctuation N cuts R v+δ/4))
  rw [sideScale_eq_rpow N (by omega) cuts hn R hpair] at hw
  exact hw.trans (h N d hN hd _ hF)

/-- Source per-edge sparsity, with every scalar and probabilistic premise discharged. -/
theorem relevantParents (k : ℕ) (hk : 0<k) (T χ δ : ℝ)
    (hT : 0≤T) (hχ : 0<χ) (hδ : 0<δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ (N n d : ℕ), N0 ≤ N → (d : ℝ) ≤ T*Real.log (N : ℝ) →
      ∀ (cuts : Cuts k n d) (hn : 0<n) (c₀ : ℤ) (R : Finset (Fin n))
        (y z v : Prefix k d), GenuineBoundaryPair cuts R χ y z v → ∀ m : ℤ,
      (relevantLeaves N cuts c₀ R v δ m (Real.exp (-(N : ℝ)^(δ/16)))).card ≤ 2*k*d := by
  obtain ⟨N1,hN1,hq⟩ := crossingPenalty_eventually χ δ hδ
  obtain ⟨N2,hN2,hw⟩ := endpointWindow_rate T χ δ hT hχ hδ
  obtain ⟨N3,hN3,hgap⟩ := Compat.fixed_polynomial_le_rpow 3 T 0 (3*δ/4)
    (by norm_num) hT (by positivity)
  refine ⟨max N1 (max N2 N3),hN1.trans (le_max_left _ _),?_⟩
  intro N n d hN hd cuts hn c₀ R y z v hpair m
  have hn1 : N1≤N := (le_max_left _ _).trans hN
  have hn2 : N2≤N := (le_max_left N2 N3).trans ((le_max_right _ _).trans hN)
  have hn3 : N3≤N := (le_max_right N2 N3).trans ((le_max_right _ _).trans hN)
  have hNgt : 1<N := by omega
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  by_cases he : (relevantLeaves N cuts c₀ R v δ m (Real.exp (-(N : ℝ)^(δ/16)))).Nonempty
  · obtain ⟨x,hx⟩ := he
    have hF := properStableFluctuationPositive N hNgt cuts hn R hpair
      ((Finset.mem_filter.mp hx).2).1 (hq N hn1)
    apply relevantParents_finite N hNgt hk cuts hn c₀ R m hpair
      (Real.rpow_pos_of_pos hNp (boundaryFluctuation N cuts R v+δ/4))
    · unfold endpointError
      rw [sideScale_eq_rpow N hNgt cuts hn R hpair]
      apply (hw N d hn2 hd _ hF).trans_lt
      apply Real.exp_lt_exp.mpr
      apply neg_lt_neg
      exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hNgt) (by linarith)
    · have hg : 2 < (N : ℝ)^(3*δ/4) := by
        have hh := hgap N d hn3 hd
        norm_num only [pow_zero,mul_one] at hh
        linarith
      exact parentMean_gt_two_windows hNgt (le_refl _) hg
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty]
    exact Nat.zero_le _

/-- The complete omitted-cover contribution at the source rate. -/
theorem irrelevantLoss_eventually (k : ℕ) (hk : 0<k) (T δ : ℝ) (hT : 0≤T) (hδ : 0<δ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ (N n d : ℕ), N0 ≤ N → (d : ℝ) ≤ T*Real.log (N : ℝ) →
      ∀ (cuts : Cuts k n d) (c₀ : ℤ) (R : Finset (Fin n)) (v : Prefix k d) (m : ℤ),
      probability (fixedCountPMF cuts) (fun ω =>
        (∃ x, ProperStable N cuts R v δ x ∧ m ∈ anchoredInterval c₀ R x ω) ∧
        ¬∃ x, ProperStable N cuts R v δ x ∧
          Relevant cuts c₀ R m (Real.exp (-(N : ℝ)^(δ/16))) x ∧ m ∈ anchoredInterval c₀ R x ω) ≤
        Real.exp (-(N : ℝ)^(δ/32)) := by
  obtain ⟨N0,hN0,h⟩ := countedWindowError_rate k hk T δ hT hδ
  refine ⟨N0,hN0,?_⟩
  intro N n d hN hd cuts c₀ R v m
  apply (irrelevantLoss N hk cuts c₀ R v δ (Real.exp (-(N : ℝ)^(δ/16))) (Real.exp_pos _).le m).trans
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using h N d hN hd

end RiffleUpperV2.Localization
