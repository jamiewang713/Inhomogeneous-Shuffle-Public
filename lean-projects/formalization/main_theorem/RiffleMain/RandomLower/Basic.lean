import RiffleUpperV2.Shared.Random
import RiffleLowerV2.Ascent.Mixture
import RiffleLowerV2.Ascent.FiniteProbability

noncomputable section
set_option autoImplicit false
open scoped BigOperators Topology
open RiffleLowerV2 TimeProfile Filter
open RiffleLowerV2.Targets
namespace RiffleMain.RandomLower

/-- A formulation defined for every deck size, including the irrelevant initial sizes. -/
def Admissible {k : ℕ} (T etaLargest etaCold chi gamma rho : ℝ) (N : ℕ)
    (cuts : HorizonCuts k N T) : Prop :=
  ∃ hN : 2 ≤ N,
    EmpiricalAlternative T cuts (deckPos hN) etaLargest etaCold chi gamma rho

theorem admissible_iff {k N : ℕ} (T etaLargest etaCold chi gamma rho : ℝ)
    (hN : 2 ≤ N) (cuts : HorizonCuts k N T) :
    Admissible T etaLargest etaCold chi gamma rho N cuts ↔
      EmpiricalAlternative T cuts (deckPos hN) etaLargest etaCold chi gamma rho := by
  constructor
  · rintro ⟨hN', h⟩
    exact h
  · intro h
    exact ⟨hN, h⟩

/-- There are at most `(N+1)^(k*K)` arrays of integer pile counts. -/
theorem card_cuts_le (k N K : ℕ) :
    Fintype.card (Cuts k N K) ≤ (N+1)^(k*K) := by
  have h := Fintype.card_le_of_injective
    (@RiffleUpperV2.countEncoding k N K) RiffleUpperV2.countEncoding_injective
  simpa [Fintype.card_fun, ← pow_mul, Nat.mul_comm] using h

theorem probability_bind {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (Q : PMF Ω) (laws : Ω → PMF Γ) (A : Γ → Prop) :
    probability (Q.bind laws) A = expect Q (fun x => probability (laws x) A) := by
  classical
  exact Model.expect_bind Q laws (fun x => if A x then 1 else 0)

/-- A common event is averaged over the whole environment, with no independence assumption. -/
theorem mixture_event_lower {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (Q : PMF Ω) (laws : Ω → PMF Γ) (good : Ω → Prop) (A : Γ → Prop)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ x, good x → 1-ε ≤ probability (laws x) A) :
    probability Q good-ε ≤ probability (Q.bind laws) A := by
  classical
  rw [probability_bind]
  have hpoint (x : Ω) : (if good x then (1 : ℝ) else 0)-ε ≤
      probability (laws x) A := by
    by_cases hx : good x
    · simpa only [if_pos hx] using hgood x hx
    · simp only [if_neg hx, zero_sub]
      exact (neg_nonpos.mpr hε).trans (Ascent.probability_nonneg _ _)
  have h := Ascent.expect_mono Q hpoint
  rwa [Ascent.expect_sub, Ascent.expect_const] at h

theorem mixture_tv_lower {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (Q : PMF Ω) (laws : Ω → PMF Γ) (U : PMF Γ)
    (good : Ω → Prop) (A : Γ → Prop) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ x, good x → 1-ε ≤ probability (laws x) A)
    (hnull : probability U A ≤ δ) :
    probability Q good-ε-δ ≤ tv (Q.bind laws) U := by
  have hs := mixture_event_lower Q laws good A hε hgood
  have ht := Ascent.probability_sub_le_tv (Q.bind laws) U A
  linarith

/-- Uniform bounds for individual tests survive a union over a finite index type. -/
theorem probability_exists_le_card_mul {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : PMF Ω) (A : I → Ω → Prop) {b : ℝ}
    (h : ∀ i, probability P (A i) ≤ b) :
    probability P (fun x => ∃ i, A i x) ≤ (Fintype.card I : ℝ)*b := by
  have hu := Ascent.probability_iUnion_le P A
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => h i)
  exact hu.trans (by simpa using hs)

end RiffleMain.RandomLower
