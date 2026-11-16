import RiffleUpperV2.Conditional.FineMoments
import RiffleUpperV2.Conditional.RegimePowers
import RiffleUpperV2.Reservoir.ExtraCopies
import RiffleUpperV2.Reservoir.BackwardCounts

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Conditional
open Exploration Reservoir TimeProfile
attribute [local instance 2000] wordDecEq

theorem fullWordMean_le_maximalMean {k n L : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    (s : Word k L) :
    (n : ℝ)*RiffleLowerV2.wordMass cuts s ≤ RiffleLowerV2.maximalMean cuts hn := by
  unfold RiffleLowerV2.wordMass RiffleLowerV2.prefixMass RiffleLowerV2.fullPrefix
    RiffleLowerV2.maximalMean
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Finset.prod_le_prod
  · intro j _; positivity
  · intro j _
    exact prob_le_pileMax (cuts.profile hn j) (s.get j)

/-- The actual maximum full-word mean and the source alpha budget control the
one exposed run, including zero-mass words. -/
theorem currentWordPower {k n L : ℕ} (hn : 2 ≤ n) (cuts : Cuts k n (L+1))
    (s : Word k (L+1)) {η α : ℝ} (hη : 0 < η) (hα1 : α ≤ 1)
    (hα : α ≤ η/(40*(1+η)))
    (hmargin : empiricalBeta n 0 cuts (by omega) (L+1) ≤ -η) :
    (n : ℝ)*(RiffleLowerV2.wordMass cuts s)^(1-α) ≤ (n : ℝ)^(-3*η/5) := by
  have hmean := (fullWordMean_le_maximalMean cuts (by omega) s).trans
    (Margins.maximalMean_le_of_terminalMargin hn 0 cuts (by omega) (by simpa using hmargin))
  have hl : 0 ≤ RiffleLowerV2.wordMass cuts s := by
    unfold RiffleLowerV2.wordMass RiffleLowerV2.prefixMass
    positivity
  have hh := tinyCount_power (by exact_mod_cast (show 0 < n by omega)) hl hα1 hmean
  apply hh.trans
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ n by omega)) (currentExponent_budget hη hα)

/-- Both genuine natural-history directions share one current-run constant.
The hasDirection premise is used only on the caller's nonzero-current-run branch. -/
theorem currentRunBound (k D : ℕ) (hk : 0 < k) (hD : 1 ≤ D)
    (g τ T η : ℝ) (hg : 0 < g) (hg1 : g < 1) (hτ : 0 < τ)
    (hτg : τ < g) (hT : 0 < T) (hη : 0 < η)
    (hαhalf : Real.log (1/g)/Real.log (1/τ) < 1/2)
    (hα : Real.log (1/g)/Real.log (1/τ) ≤ η/(40*(1+η))) :
    ∃ Ccur : ℝ, 0 < Ccur ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ n : ℕ, N0 ≤ n →
      ∀ L : ℕ, ((L+1 : ℕ) : ℝ) ≤ T*Real.log (n : ℝ) →
      ∀ cuts : Cuts k n (L+1), ∀ hn : 0 < n,
      GoodColumn (cuts.profile hn 0) g →
      empiricalBeta n 0 cuts hn (L+1) ≤ -η →
      ∀ ξ ε : ℝ, 0 ≤ ε → ∀ (p : Fin k) (d : Direction), ∀ ω : Sample cuts,
      ∀ j : Fin (pileSize cuts p), positiveHistory cuts p d (j.val+1) ω →
      historyGood cuts D g ξ ε p d (j.val+1) ω →
      hasDirection cuts D g d (revealWords cuts p d ω j) →
      conditionalExpect (fixedCountPMF cuts) (currentExcess cuts p d j ω)
        (historyFiber cuts p d (j.val+1) ω) ≤ Ccur*(n : ℝ)^(-3*η/5)+n*ε := by
  obtain ⟨Cf,hCf,Nf,hNf,hf⟩ := Reservoir.extraCurrentCopies k D hk hD g τ T hg hg1 hτ hτg hT hαhalf
  obtain ⟨Cb,hCb,Nb,hNb,hb⟩ := Reservoir.Backward.extraCurrentCopies k D hk hD g τ T hg hg1 hτ hτg hT hαhalf
  refine ⟨max Cf Cb,lt_of_lt_of_le hCf (le_max_left _ _),max 2 (max Nf Nb),le_max_left _ _,?_⟩
  intro n hn L hL cuts hn0 hgood hmargin ξ ε hε p d ω j hpos hhistory hdir
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hrate := currentWordPower hn2 cuts (revealWords cuts p d ω j) hη
    (by linarith) hα hmargin
  cases d with
  | forward =>
    have hh := hf n ((le_max_left Nf Nb).trans ((le_max_right _ _).trans hn))
      L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir
    change conditionalExpect _ (currentExcess cuts p .forward j ω) _ ≤ _ at hh
    apply hh.trans
    have h1 := mul_le_mul_of_nonneg_left hrate hCf.le
    have h2 := mul_le_mul_of_nonneg_right (le_max_left Cf Cb)
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-3*η/5))
    simpa only [revealWords,pileWords,mul_assoc,add_comm] using
      add_le_add_right (h1.trans h2) ((n : ℝ)*ε)
  | backward =>
    have hh := hb n ((le_max_right Nf Nb).trans ((le_max_right _ _).trans hn))
      L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir
    change conditionalExpect _ (currentExcess cuts p .backward j ω) _ ≤ _ at hh
    apply hh.trans
    have h1 := mul_le_mul_of_nonneg_left hrate hCb.le
    have h2 := mul_le_mul_of_nonneg_right (le_max_right Cf Cb)
      (Real.rpow_nonneg (Nat.cast_nonneg n) (-3*η/5))
    simpa only [revealWords,backwardWords,mul_assoc,add_comm] using
      add_le_add_right (h1.trans h2) ((n : ℝ)*ε)

end RiffleUpperV2.Conditional
