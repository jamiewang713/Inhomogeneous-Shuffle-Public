import RiffleLowerV2.Factorial.Main
import RiffleLowerV2.Thinning.Main

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Occupancy
open TimeProfile

/-- Selected piles give positive full-word means, including the empty word. -/
theorem wordMean_pos {N k K : ℕ} (cuts : Cuts k N K) (w : Word k K)
    {c : ℝ} (hc : 0 < c) (hN : 0 < N)
    (hpiles : ∀ j, c * N ≤ (cuts.count j (w.get j) : ℝ)) :
    0 < (N : ℝ) * wordMass cuts w := by
  rw [Factorial.wordMean_eq_numericalMean]
  apply Factorial.numericalMean_pos (by exact_mod_cast hN)
  intro j
  exact lt_of_lt_of_le (mul_pos hc (by exact_mod_cast hN)) (hpiles j)

/-- Concrete one-word factorial estimates, with the original exact order cost. -/
theorem original_one_factorial_inputs (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ,
      ∀ N ≥ N0, ∀ k K : ℕ, (K : ℝ) ≤ C * logScale N →
      ∀ (cuts : Cuts k N K) (w : Word k K),
        (∀ j, c * N ≤ (cuts.count j (w.get j) : ℝ)) →
      ∀ r : ℕ, (r : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) →
        |expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) r) -
          ((N : ℝ) * wordMass cuts w)^r| ≤
        D * (K+1) * (r : ℝ)^2 / N * ((N : ℝ) * wordMass cuts w)^r := by
  obtain ⟨D, hD, N0, hF⟩ := Factorial.relativeJointFactorial c C hc hC
  refine ⟨D, hD, N0, ?_⟩
  intro N hN k K hK cuts w hpiles r hr
  have hinj : Function.Injective (fun _ : Fin 1 => w) := by
    intro i j _
    exact Subsingleton.elim i j
  have h := hF N hN k K 1 hK cuts (fun _ : Fin 1 => w) (fun _ => r)
    hinj (fun _ => hpiles) (by simpa only [Fin.sum_univ_one] using hr)
  have heq : (factorialProduct (fun _ : Fin 1 => w) (fun _ => r) : Sample cuts → ℝ) =
      (fun ω => falling (wordCount w ω) r) := by
    funext ω
    simp [factorialProduct]
  rw [heq] at h
  simpa only [Fin.prod_univ_one, Fin.sum_univ_one] using h

/-- Concrete two-word factorial estimates; distinctness supplies disjoint requests. -/
theorem original_two_factorial_inputs (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ,
      ∀ N ≥ N0, ∀ k K : ℕ, (K : ℝ) ≤ C * logScale N →
      ∀ (cuts : Cuts k N K) (w v : Word k K), w ≠ v →
        (∀ j, c * N ≤ (cuts.count j (w.get j) : ℝ)) →
        (∀ j, c * N ≤ (cuts.count j (v.get j) : ℝ)) →
      ∀ r s : ℕ, ((r+s : ℕ) : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) →
        |expect (fixedCountPMF cuts)
            (fun ω => falling (wordCount w ω) r * falling (wordCount v ω) s) -
          ((N : ℝ) * wordMass cuts w)^r * ((N : ℝ) * wordMass cuts v)^s| ≤
        D * (K+1) * ((r+s : ℕ) : ℝ)^2 / N *
          (((N : ℝ) * wordMass cuts w)^r * ((N : ℝ) * wordMass cuts v)^s) := by
  obtain ⟨D, hD, N0, hF⟩ := Factorial.relativeJointFactorial c C hc hC
  refine ⟨D, hD, N0, ?_⟩
  intro N hN k K hK cuts w v hwv hw hv r s hrs
  let words : Fin 2 → Word k K := ![w, v]
  let orders : Fin 2 → ℕ := ![r, s]
  have hinj : Function.Injective words := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [words]
  have hpiles (i : Fin 2) (j : Fin K) : c * N ≤ (cuts.count j ((words i).get j) : ℝ) := by
    fin_cases i
    · exact hw j
    · exact hv j
  have h := hF N hN k K 2 hK cuts words orders hinj hpiles
    (by simpa [orders, Fin.sum_univ_two] using hrs)
  have heq : (factorialProduct words orders : Sample cuts → ℝ) =
      (fun ω => falling (wordCount w ω) r * falling (wordCount v ω) s) := by
    funext ω
    simp [factorialProduct, words, orders, Fin.prod_univ_two]
  rw [heq] at h
  simpa [words, orders, Fin.prod_univ_two, Fin.sum_univ_two] using h

/-- The full-word empty/singleton tail is the concrete LB02 prefix theorem. -/
theorem fullWord_empty_singleton_tail {N k K : ℕ} (cuts : Cuts k N K)
    (hN : 0 < N) (w : Word k K) :
    probability (fixedCountPMF cuts) (fun ω => wordCount w ω < 2) ≤
      2 * Real.exp (-((N : ℝ) * wordMass cuts w) / 2) :=
  (Thinning.prefixTails cuts hN (fullPrefix w)).2.2

end RiffleLowerV2.Occupancy
