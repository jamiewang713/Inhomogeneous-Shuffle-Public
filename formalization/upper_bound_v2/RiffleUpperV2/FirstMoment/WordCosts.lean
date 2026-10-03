import RiffleUpperV2.FirstMoment.Entropy
import RiffleUpperV2.FirstMoment.Exponents

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.FirstMoment
open TimeProfile

/-- Exact logarithmic product cost, with zero selected probabilities excluded. -/
theorem selectedCost_log_product {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (p : J → Simplex k) (I : Finset J) (w : J → Fin k)
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w j)) :
    selectedCost N p I w = -Real.log (∏ j ∈ I, prob (p j) (w j))/logScale N := by
  unfold selectedCost
  rw [Real.log_prod (fun j hj => (hlegal j hj).ne')]
  simp [digitCost, one_div, Real.log_inv, Finset.sum_neg_distrib]

/-- The selected good and exceptional costs give the literal mean-exponent split. -/
theorem exactWordCostSplit {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (p : J → Simplex k) (I : Finset J) (w : J → Fin k) (chi mu : ℝ)
    (hmu : 0 < mu) (hlegal : ∀ j ∈ I, 0 < prob (p j) (w j)) :
    Real.log (mu*(∏ j ∈ I, prob (p j) (w j)))/logScale N =
      Real.log mu/logScale N-goodCost N p I chi w-exceptionalCost N p I chi w := by
  have hp : 0 < ∏ j ∈ I, prob (p j) (w j) := Finset.prod_pos hlegal
  rw [Real.log_mul hmu.ne' hp.ne']
  have hs := selectedCost_split N p I chi w
  rw [selectedCost_log_product p I w hlegal] at hs
  rw [neg_div] at hs
  rw [add_div]
  linarith

/-- Concrete expected occupancy of the full selected word. -/
def fullWordMean {k n L : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    (w : Fin L → Fin k) : ℝ := (n : ℝ)*(∏ j, prob (cuts.profile hn j) (w j))

theorem fullWordMean_le_maximalMean {k n L : ℕ} (cuts : Cuts k n L) (hn : 0 < n)
    (w : Fin L → Fin k) : fullWordMean cuts hn w ≤ RiffleLowerV2.maximalMean cuts hn := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.prod_le_prod (fun j _ => prob_nonneg _ _) (fun j _ => prob_le_pileMax _ _)

/-- Literal terminal-word exponent at original scale N, including n<N. -/
theorem empiricalTerminalExponent {k n L N : ℕ} (hN : 2 ≤ N) (a : ℕ)
    (cuts : Cuts k n L) (hn : 0 < n) (w : Fin L → Fin k)
    (hlegal : ∀ j, 0 < prob (cuts.profile hn j) (w j)) {eta : ℝ}
    (hterminal : empiricalBeta N a cuts hn (a+L) ≤ -eta) :
    Real.log (fullWordMean cuts hn w)/logScale N ≤ -eta := by
  have hp : 0 < fullWordMean cuts hn w :=
    mul_pos (by exact_mod_cast hn) (Finset.prod_pos (fun j _ => hlegal j))
  have hb := (fullWordMean_le_maximalMean cuts hn w).trans
    (Margins.maximalMean_le_of_terminalMargin hN a cuts hn hterminal)
  have hh := Real.log_le_log hp hb
  rw [Real.log_rpow (by exact_mod_cast (by omega : 0 < N))] at hh
  apply (div_le_iff₀ (logScale_pos hN)).mpr
  simpa [logScale, mul_comm] using hh

/-- Refining a cost class by routing or boundary data can only improve its entropy. -/
theorem refinedClassEntropy {J : Type*} [Fintype J] [DecidableEq J] {k N : ℕ}
    (hk : 2 ≤ k) (hN : 2 ≤ N) (p : J → Simplex k) (I : Finset J)
    (chi width theta alpha : ℝ) (hwidth : 0 < width)
    (htheta : theta ∈ Set.Icc (3 : ℝ) 4) (w0 : J → Fin k)
    (hlegal : ∀ j ∈ I, 0 < prob (p j) (w0 j))
    (hbudget : ((exceptionalPositions p I chi w0).card : ℝ) ≤ alpha*logScale N)
    (W : Finset (J → Fin k)) (hW : W.Nonempty)
    (hsub : W ⊆ costClass N p I chi width w0) :
    Real.log (W.card : ℝ)/logScale N ≤
      theta*goodCost N p I chi w0-(∑ j ∈ I, psi (p j) theta)/logScale N+
        (4*width+4*Real.log (k : ℝ)*alpha) := by
  have hc : (W.card : ℝ) ≤ (costClass N p I chi width w0).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  have hwpos : 0 < (W.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hW
  exact (div_le_div_of_nonneg_right (Real.log_le_log hwpos hc) (logScale_pos hN).le).trans
    (classEntropy_of_exceptionalBudget hk hN p I chi width theta alpha hwidth htheta w0 hlegal hbudget)

/-- Empty descriptor fibers can be omitted before taking logarithms. -/
theorem sum_emptyClass {A : Type*} (f : A → ℝ) : ∑ x ∈ (∅ : Finset A), f x = 0 := by simp

end RiffleUpperV2.FirstMoment
