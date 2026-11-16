import RiffleLowerV2.Occupancy.ModelInputs

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Occupancy
open TimeProfile

/-- Full-prefix prescriptions count exactly the prescribed copies of the word. -/
theorem prescribedPrefixCount_fullPrefix {N k K b : ℕ}
    (p : RowPrescription N k K b) (w : Word k K) :
    Thinning.prescribedPrefixCount p (fullPrefix w) =
      (Finset.univ.filter fun q => p.word q = w).card := by
  unfold Thinning.prescribedPrefixCount fullPrefix
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_last]
  rw [List.take_of_length_le (by simp)]
  exact List.Vector.toList_injective.eq_iff

/-- The conditional statistic removes every prescribed occurrence of the word. -/
theorem residualPrefixCount_fullPrefix {N k K b : ℕ} {cuts : Cuts k N K}
    (p : RowPrescription N k K b) (w : Word k K) (ω : Sample cuts) :
    Thinning.residualPrefixCount p (fullPrefix w) ω =
      wordCount w ω - (Finset.univ.filter fun q => p.word q = w).card := by
  rw [Thinning.residualPrefixCount, prescribedPrefixCount_fullPrefix]
  rfl

/-- The residual prefix mean specializes to the frozen numerical word mean. -/
theorem residualPrefixMean_fullPrefix {N k K b : ℕ} (cuts : Cuts k N K)
    (p : RowPrescription N k K b) (w : Word k K) :
    Thinning.residualPrefixMean cuts p (fullPrefix w) =
      Targets.residualWordMean cuts p w := rfl

/-- A positive residual population and unexhausted selected piles give a positive mean. -/
theorem residualWordMean_pos {N k K b : ℕ} (cuts : Cuts k N K)
    (p : RowPrescription N k K b) (w : Word k K) {c : ℝ}
    (hb : b < N) (hbc : (b : ℝ) < c * N)
    (hpiles : ∀ j, c * N ≤ (cuts.count j (w.get j) : ℝ)) :
    0 < Targets.residualWordMean cuts p w := by
  have hpop : (0 : ℝ) < (N-b : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hb
  apply mul_pos hpop
  apply Finset.prod_pos
  intro j _
  apply div_pos ?_ hpop
  have hu : (usedCount p j (w.get j) : ℝ) ≤ b := by
    exact_mod_cast Factorial.usedCount_le p j (w.get j)
  have hh : usedCount p j (w.get j) < cuts.count j (w.get j) := by
    exact_mod_cast (lt_of_le_of_lt hu (hbc.trans_le (hpiles j)))
  exact_mod_cast Nat.sub_pos_of_lt hh

/-- The conditional probability is the conditional expectation of its indicator. -/
theorem conditionalProbability_eq_expect_indicator {Ω : Type*} [Fintype Ω]
    (P : PMF Ω) (A B : Ω → Prop) :
    conditionalProbability P A B = conditionalExpect P (fun ω => if A ω then 1 else 0) B := by
  unfold conditionalProbability conditionalExpect probability
  congr 1
  congr 1
  funext ω
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb]

/-- A single residual fixed-column law transports all deleted full-word tests.
The residual counts, expectation bridge, event bridge and mean identity share
the same residual cuts witness. -/
theorem exists_residual_word_law {N k K b : ℕ} (cuts : Cuts k N K)
    (p : RowPrescription N k K b) (hb : b < N) (hinj : Function.Injective p.row)
    (hprob : 0 < probability (fixedCountPMF cuts) (prescriptionEvent p)) :
    ∃ residual : Cuts k (N-b) K,
      (∀ j a, residual.count j a = cuts.count j a - usedCount p j a) ∧
      (∀ (w : Word k K) (F : ℕ → ℝ),
        conditionalExpect (fixedCountPMF cuts)
          (fun ω => F (wordCount w ω - (Finset.univ.filter fun q => p.word q = w).card))
          (prescriptionEvent p) = expect (fixedCountPMF residual) (fun η => F (wordCount w η))) ∧
      (∀ (w : Word k K) (A : ℕ → Prop),
        conditionalProbability (fixedCountPMF cuts)
          (fun ω => A (wordCount w ω - (Finset.univ.filter fun q => p.word q = w).card))
          (prescriptionEvent p) = probability (fixedCountPMF residual) (fun η => A (wordCount w η))) ∧
      (∀ w : Word k K, (N-b : ℕ) * wordMass residual w = Targets.residualWordMean cuts p w) := by
  obtain ⟨residual, hres, ht⟩ := Thinning.residualPrefixExpect cuts p hb hinj hprob
  obtain ⟨e, he, hc⟩ := Thinning.existsComplementEnumeration p hinj
  have hexpect (w : Word k K) (F : ℕ → ℝ) :
      conditionalExpect (fixedCountPMF cuts)
        (fun ω => F (wordCount w ω - (Finset.univ.filter fun q => p.word q = w).card))
        (prescriptionEvent p) = expect (fixedCountPMF residual) (fun η => F (wordCount w η)) := by
    simpa only [residualPrefixCount_fullPrefix, wordCount] using ht e he hc (fullPrefix w) F
  refine ⟨residual, hres, hexpect, ?_, ?_⟩
  · intro w A
    rw [conditionalProbability_eq_expect_indicator]
    exact hexpect w (fun n => if A n then 1 else 0)
  · intro w
    exact Thinning.residualPrefixMean_eq cuts p residual hres (fullPrefix w)

/-- Concrete conditional one-word factorial estimates retain the ambient-N cutoff. -/
theorem conditional_one_factorial_inputs (c C : ℝ) (hc : 0 < c) (hC : 0 < C) (b0 : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ, b0 < N0 ∧ 2 ≤ N0 ∧
      ∀ N ≥ N0, ∀ k K b : ℕ, b ≤ b0 → (K : ℝ) ≤ C * logScale N →
      ∀ (cuts : Cuts k N K) (p : RowPrescription N k K b), Function.Injective p.row →
        0 < probability (fixedCountPMF cuts) (prescriptionEvent p) →
      ∀ w : Word k K, (∀ j, c * N ≤ (cuts.count j (w.get j) : ℝ)) →
      ∀ r : ℕ, (r : ℝ) ≤ (N : ℝ)^(1/5 : ℝ) →
        |conditionalExpect (fixedCountPMF cuts)
            (fun ω => falling (wordCount w ω - (Finset.univ.filter fun q => p.word q = w).card) r)
            (prescriptionEvent p) - (Targets.residualWordMean cuts p w)^r| ≤
          D * (K+1) * (r : ℝ)^2 / N * (Targets.residualWordMean cuts p w)^r := by
  obtain ⟨D, hD, N0, hb0, hN02, hF⟩ := Factorial.residualRelativeFactorial c C hc hC b0
  refine ⟨D, hD, N0, hb0, hN02, ?_⟩
  intro N hN k K b hb hK cuts p hinj hp w hpiles r hr
  have hwinj : Function.Injective (fun _ : Fin 1 => w) := by
    intro i j _
    exact Subsingleton.elim i j
  have h := hF N hN k K b 1 hb hK cuts p hinj hp (fun _ : Fin 1 => w)
    (fun _ => r) hwinj (fun _ => hpiles) (by simpa only [Fin.sum_univ_one] using hr)
  simpa only [Fin.prod_univ_one, Fin.sum_univ_one] using h

/-- LB02 gives the conditional empty/singleton tail at the exact residual mean. -/
theorem conditional_fullWord_empty_singleton_tail {N k K b : ℕ} (cuts : Cuts k N K)
    (p : RowPrescription N k K b) (hb : b < N) (hinj : Function.Injective p.row)
    (hprob : 0 < probability (fixedCountPMF cuts) (prescriptionEvent p)) (w : Word k K) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => wordCount w ω - (Finset.univ.filter fun q => p.word q = w).card < 2)
      (prescriptionEvent p) ≤ 2 * Real.exp (-Targets.residualWordMean cuts p w / 2) := by
  simpa only [residualPrefixCount_fullPrefix, residualPrefixMean_fullPrefix] using
    (Thinning.residualPrefixTails cuts p hb hinj hprob (fullPrefix w)).2.2

end RiffleLowerV2.Occupancy
