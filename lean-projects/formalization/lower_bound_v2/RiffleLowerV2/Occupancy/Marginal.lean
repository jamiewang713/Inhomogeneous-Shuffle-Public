import RiffleLowerV2.Occupancy.MarginalNumerical
import RiffleLowerV2.Occupancy.CentralModel
import RiffleLowerV2.Occupancy.RegimeAlgebra

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Occupancy
open TimeProfile

/-- Uniform actual-model marginal estimate, proved before all conditional and
pair estimates. The numerical constant is universal; the threshold depends on c,C. -/
theorem uniform_marginal (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ k K : ℕ,
      (K : ℝ) ≤ C*logScale N → ∀ (cuts : Cuts k N K) (w : Word k K),
      (∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) →
      |probability (fixedCountPMF cuts) (collisionEvent w) -
        poissonCollision ((N : ℝ)*wordMass cuts w)| ≤
      8*tau N*poissonCollision ((N : ℝ)*wordMass cuts w) := by
  obtain ⟨D,hD,N1,hF⟩ := original_one_factorial_inputs c C hc hC
  obtain ⟨A,hA,N2,hCentral⟩ := central_marginal_absolute c C hc hC
  obtain ⟨N3,hBudget⟩ := eventual_marginal_budgets D C A
  refine ⟨max 2 (max N1 (max N2 N3)), le_max_left _ _, ?_⟩
  intro N hN k K hK cuts w hw
  have hN1 : N1 ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hN2 : N2 ≤ N := (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))).trans hN
  have hN3 : N3 ≤ N := (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))).trans hN
  obtain ⟨hNN,hL,ht1,hRare,hAbs,hTail,hOrder⟩ := hBudget N hN3
  have hNp : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  have ht : 0 < tau N := tau_pos hNp
  have hμ := wordMean_pos cuts w hc hNp hw
  let μ : ℝ := (N : ℝ)*wordMass cuts w
  let p : ℝ := probability (fixedCountPMF cuts) (collisionEvent w)
  change 0 < μ at hμ
  change |p-poissonCollision μ| ≤ 8*tau N*poissonCollision μ
  have hf0 := (poissonCollision_pos hμ).le
  by_cases hμt : μ ≤ tau N
  · let η : ℝ := 9*D*(C*logScale N+1)/N
    have hη : 0 ≤ η := by dsimp [η]; positivity
    have h2 := hF N hN1 k K hK cuts w hw 2 (by norm_num; linarith)
    have h3 := hF N hN1 k K hK cuts w hw 3 (by norm_num; exact hOrder)
    have h2' : |expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) 2)-μ^2| ≤ η*μ^2 := by
      apply h2.trans
      dsimp [η, μ]
      have hk : (K : ℝ)+1 ≤ C*logScale N+1 := by linarith
      have hm : 0 ≤ ((N : ℝ)*wordMass cuts w)^2 := sq_nonneg _
      have hcoef : D*(K+1)*(2 : ℝ)^2/N ≤ 9*D*(C*logScale N+1)/N := by
        apply div_le_div_of_nonneg_right _ hNr.le
        have hh := mul_le_mul_of_nonneg_left hk hD.le
        have hn : 0 ≤ D*((K : ℝ)+1) := by positivity
        norm_num
        nlinarith
      exact mul_le_mul_of_nonneg_right hcoef hm
    have h3' : |expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) 3)-μ^3| ≤ η*μ^3 := by
      apply h3.trans
      have hk : (K : ℝ)+1 ≤ C*logScale N+1 := by linarith
      have hm : 0 ≤ μ^3 := pow_nonneg hμ.le _
      apply mul_le_mul_of_nonneg_right _ hm
      dsimp [η]
      apply div_le_div_of_nonneg_right _ hNr.le
      have hh := mul_le_mul_of_nonneg_left hk hD.le
      norm_num
      nlinarith
    have hs := Factorial.rareSandwich (Sample cuts) (fixedCountPMF cuts) (wordCount w)
    exact rare_marginal_relative hμ hμt ht1 hη hRare h2' h3' hs.1 hs.2
  · have htm : tau N < μ := lt_of_not_ge hμt
    by_cases hμB : μ ≤ centralBound N
    · have hB : 0 ≤ centralBound N := by dsimp [centralBound]; linarith
      have ha := hCentral N hN2 k K hK cuts w hw (by change μ ≤ _; linarith)
      have hb := benchmark_lower_at_tau ht.le (by linarith) htm
      have hb' := mul_le_mul_of_nonneg_left hb ht.le
      have hh : |p-poissonCollision μ| ≤ tau N*poissonCollision μ := by
        change |p-poissonCollision μ| ≤ A*(N : ℝ)^(-7/10 : ℝ) at ha
        nlinarith [ha.trans hAbs]
      nlinarith [mul_nonneg ht.le hf0]
    · have hBm : centralBound N ≤ μ := (lt_of_not_ge hμB).le
      have hB : 0 ≤ centralBound N := by dsimp [centralBound]; linarith
      have hp1 : p ≤ 1 := probability_le_one _ _
      have hf1 := (Factorial.poissonCollision_bounds μ hμ.le).2
      have hpTail : 1-p ≤ 2*Real.exp (-μ/2) := by
        have hh := fullWord_empty_singleton_tail cuts hNp w
        have heq : probability (fixedCountPMF cuts) (fun ω => wordCount w ω < 2) = 1-p := by
          rw [← probability_not (fixedCountPMF cuts) (collisionEvent w)]
          apply probability_congr
          intro ω
          exact Nat.not_le.symm
        rw [heq] at hh
        exact hh
      have hpTail' : 1-p ≤ 2*Real.exp (-centralBound N/2) := by
        apply hpTail.trans
        gcongr
      have hfmono := poissonCollision_mono hB hμ.le hBm
      have hfTail : 1-poissonCollision μ ≤ (1+centralBound N)*Real.exp (-centralBound N) := by
        dsimp [poissonCollision] at hfmono ⊢
        linarith
      have hfhalf : 1/2 ≤ poissonCollision μ := by
        have hexp : 0 ≤ 2*Real.exp (-centralBound N/2) := by positivity
        linarith
      have hh : |p-poissonCollision μ| ≤ tau N/2 := by
        apply abs_le.mpr
        constructor <;> linarith
      have hb := mul_le_mul_of_nonneg_left hfhalf ht.le
      nlinarith [mul_nonneg ht.le hf0]

end RiffleLowerV2.Occupancy
