import RiffleUpperV2.Shared.Model

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2

abbrev conditionalExpect := @RiffleLowerV2.conditionalExpect
abbrev conditionalProbability := @RiffleLowerV2.conditionalProbability

/-- Independent fixed-count samples, each with the exact original uniform law. -/
def independentPairLaw {k n L : ℕ} (cuts : Cuts k n L) : PMF (Sample cuts × Sample cuts) :=
  PMF.uniformOfFintype _

theorem independentPair_expect {k n L : ℕ} (cuts : Cuts k n L)
    (f : Sample cuts → Sample cuts → ℝ) :
    expect (independentPairLaw cuts) (fun ω => f ω.1 ω.2) =
      expect (fixedCountPMF cuts) (fun ω => expect (fixedCountPMF cuts) (f ω)) := by
  simp only [independentPairLaw, RiffleLowerV2.Model.expect_uniform,
    RiffleLowerV2.fixed_expect_eq_average, Fintype.card_prod, Nat.cast_mul,
    Fintype.sum_prod_type]
  rw [← Finset.sum_div]
  ring

/-- Every positive finite event has a witness; impossible histories are excluded. -/
theorem probability_pos_exists {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (A : Ω → Prop) (h : 0 < probability P A) : ∃ ω, A ω := by
  classical
  by_contra hn
  push Not at hn
  have hz : probability P A = 0 := by
    simp [RiffleLowerV2.probability, RiffleLowerV2.expect, hn]
  linarith

/-- Quantifying over observed matrix representatives covers every positive history. -/
theorem positive_history_has_representative {Ω H : Type*} [Fintype Ω]
    (P : PMF Ω) (history : Ω → H) (h : H)
    (hh : 0 < probability P (fun ω => history ω = h)) : ∃ ω, history ω = h :=
  probability_pos_exists P _ hh

end RiffleUpperV2
