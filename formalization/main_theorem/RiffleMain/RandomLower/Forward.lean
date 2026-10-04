import RiffleMain.RandomLower.Main

noncomputable section
set_option autoImplicit false
open scoped Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.Targets
namespace RiffleMain.RandomLower

/-- The chronological physical law, averaged over the whole random count array. -/
def randomForwardLaw {k N K : ℕ} (Q : PMF (Cuts k N K)) : PMF (Permutation N) :=
  Q.bind physicalForwardLaw

/-- Inversion commutes with averaging over arbitrarily dependent column counts. -/
theorem randomInverseLaw_eq_map {k N K : ℕ} (Q : PMF (Cuts k N K)) :
    RiffleUpperV2.randomInverseLaw Q = (randomForwardLaw Q).map Equiv.symm := by
  rw [randomForwardLaw, PMF.map_bind]
  unfold RiffleUpperV2.randomInverseLaw
  apply congrArg (fun laws => Q.bind laws)
  funext cuts
  exact physicalInverseLaw_eq_map cuts

theorem tv_randomInverse_eq_forward {k N K : ℕ} (Q : PMF (Cuts k N K)) :
    tv (RiffleUpperV2.randomInverseLaw Q) (uniformPermutation N) =
      tv (randomForwardLaw Q) (uniformPermutation N) := by
  rw [randomInverseLaw_eq_map, Model.inversionTV]

/-- Uniform random lower bound for the chronological forward shuffle in the paper. -/
theorem randomEmpiricalLower_forward (k : ℕ) (hk : 2 ≤ k) (T etaLargest etaCold : ℝ)
    (hT : 0 < T) (hl : 0 < etaLargest) (hc : 0 < etaCold)
    (chi gamma rho ε : ℝ) (hε : 0 < ε) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N ≥ N0, ∀ (hN : 2 ≤ N)
      (Q : PMF (HorizonCuts k N T)),
      probability Q (fun cuts =>
        EmpiricalAlternative T cuts (deckPos hN) etaLargest etaCold chi gamma rho) - ε ≤
        tv (randomForwardLaw Q) (uniformPermutation N) := by
  simpa only [tv_randomInverse_eq_forward] using
    randomEmpiricalLower k hk T etaLargest etaCold hT hl hc chi gamma rho ε hε

theorem randomEmpiricalLower_forward_tendsto (k : ℕ) (hk : 2 ≤ k)
    (T etaLargest etaCold : ℝ) (hT : 0 < T) (hl : 0 < etaLargest) (hc : 0 < etaCold)
    (chi gamma rho : ℝ) (Q : ∀ N : ℕ, PMF (HorizonCuts k N T))
    (hgood : Tendsto (fun N => probability (Q N)
      (Admissible T etaLargest etaCold chi gamma rho N)) atTop (𝓝 1)) :
    Tendsto (fun N => tv (randomForwardLaw (Q N)) (uniformPermutation N)) atTop (𝓝 1) := by
  simpa only [tv_randomInverse_eq_forward] using
    randomEmpiricalLower_tendsto k hk T etaLargest etaCold hT hl hc chi gamma rho Q hgood

end RiffleMain.RandomLower
