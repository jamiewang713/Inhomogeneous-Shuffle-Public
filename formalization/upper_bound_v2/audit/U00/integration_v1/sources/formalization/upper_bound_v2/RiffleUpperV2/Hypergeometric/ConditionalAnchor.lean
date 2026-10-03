import RiffleUpperV2.Hypergeometric.CylinderMean

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Hypergeometric
open TimeProfile RiffleLowerV2 RiffleLowerV2.Thinning

/-- Conditioning a uniform finite product on its first coordinate leaves the second uniform. -/
theorem uniform_product_conditional_expect {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    [Nonempty Ω] [Nonempty Γ] (c : Ω) (f : Γ → ℝ) :
    conditionalExpect (PMF.uniformOfFintype (Ω × Γ)) (fun ω => f ω.2)
      (fun ω => ω.1 = c) = expect (PMF.uniformOfFintype Γ) f := by
  simp only [conditionalExpect, probability, uniform_expect, Fintype.card_prod,
    Nat.cast_mul, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hΓ : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  rw [Finset.sum_comm]
  simp [hΓ]

/-- Exact conditional transport for an exposed first column of a uniform product. -/
theorem uniform_head_conditional_expect {d : ℕ} (Ω : Fin (d+1) → Type*)
    [∀ j, Fintype (Ω j)] [∀ j, Nonempty (Ω j)]
    (c : Ω 0) (f : (∀ j : Fin d, Ω j.succ) → ℝ) :
    conditionalExpect (PMF.uniformOfFintype (∀ j, Ω j))
      (fun ω => f (fun j => ω j.succ)) (fun ω => ω 0 = c) =
      expect (PMF.uniformOfFintype (∀ j : Fin d, Ω j.succ)) f := by
  have hn := uniform_expect_equiv (Fin.consEquiv Ω)
    (fun ω => if ω 0 = c then f (fun j => ω j.succ) else 0)
  have hd := uniform_expect_equiv (Fin.consEquiv Ω)
    (fun ω => if ω 0 = c then (1 : ℝ) else 0)
  unfold conditionalExpect probability
  rw [← hn, ← hd]
  exact uniform_product_conditional_expect c f

/-- The future columns retain the full current population n. -/
def tailCuts {k n d : ℕ} (cuts : Cuts k n (d+1)) : Cuts k n d where
  count j a := cuts.count j.succ a
  sum_count j := cuts.sum_count j.succ

def tailSample {k n d : ℕ} {cuts : Cuts k n (d+1)} (ω : Sample cuts) :
    Sample (tailCuts cuts) := fun j => ω j.succ

def anchorRows {k n d : ℕ} {cuts : Cuts k n (d+1)}
    (c : ColumnAssignments cuts 0) (a : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun i => c.val i = a

/-- There is no assumption of independent rows: this is conditional column independence. -/
theorem firstColumnConditionalExpect {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (f : Sample (tailCuts cuts) → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => f (tailSample ω))
      (fun ω => ω 0 = c) = expect (fixedCountPMF (tailCuts cuts)) f :=
  uniform_head_conditional_expect (ColumnAssignments cuts) c f

theorem firstColumnConditionalProbability {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (E : Sample (tailCuts cuts) → Prop) :
    conditionalProbability (fixedCountPMF cuts) (fun ω => E (tailSample ω))
      (fun ω => ω 0 = c) = probability (fixedCountPMF (tailCuts cuts)) E := by
  have h := firstColumnConditionalExpect cuts c (fun ω => if E ω then (1 : ℝ) else 0)
  unfold probability
  convert h using 1
  unfold conditionalProbability conditionalExpect probability
  congr 1
  apply congrArg (expect (fixedCountPMF cuts))
  funext ω
  by_cases he : E (tailSample ω) <;> by_cases hc : ω 0 = c <;> simp [he, hc]

theorem firstColumnCylinderTransform {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (a : Fin k) (D : Fin d → Finset (Fin k))
    (s : ℝ) (hs : 0 < s) :
    conditionalExpect (fixedCountPMF cuts)
      (fun ω => s ^ cylinderCount (tailCuts cuts) (anchorRows c a) D (tailSample ω))
      (fun ω => ω 0 = c) ≤
      (1 - cylinderMass (tailCuts cuts) D + cylinderMass (tailCuts cuts) D * s) ^
        (anchorRows c a).card ∧
    (1 - cylinderMass (tailCuts cuts) D + cylinderMass (tailCuts cuts) D * s) ^
        (anchorRows c a).card ≤
      Real.exp (cylinderMean (tailCuts cuts) (anchorRows c a) D * (s-1)) := by
  rw [firstColumnConditionalExpect cuts c (fun ω =>
    s ^ cylinderCount (tailCuts cuts) (anchorRows c a) D ω)]
  exact anchorCylinderTransform (tailCuts cuts) (anchorRows c a) D s hs

theorem firstColumnCylinderTail {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (a : Fin k) (D : Fin d → Finset (Fin k))
    {t : ℝ} (ht : 0 < t) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => t ≤ |(cylinderCount (tailCuts cuts) (anchorRows c a) D (tailSample ω) : ℝ) -
        cylinderMean (tailCuts cuts) (anchorRows c a) D|) (fun ω => ω 0 = c) ≤
      2 * Real.exp (-t^2 / (4 * (cylinderMean (tailCuts cuts) (anchorRows c a) D + t))) := by
  rw [firstColumnConditionalProbability cuts c (fun ω =>
    t ≤ |(cylinderCount (tailCuts cuts) (anchorRows c a) D ω : ℝ) -
      cylinderMean (tailCuts cuts) (anchorRows c a) D|)]
  exact (anchorCylinderTail (tailCuts cuts) (anchorRows c a) D ht).1

theorem firstColumnCylinderHalfMean {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (a : Fin k) (D : Fin d → Finset (Fin k)) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => (cylinderCount (tailCuts cuts) (anchorRows c a) D (tailSample ω) : ℝ) ≤
        cylinderMean (tailCuts cuts) (anchorRows c a) D / 2) (fun ω => ω 0 = c) ≤
      Real.exp (-chernoffConstant * cylinderMean (tailCuts cuts) (anchorRows c a) D) := by
  rw [firstColumnConditionalProbability cuts c (fun ω =>
    (cylinderCount (tailCuts cuts) (anchorRows c a) D ω : ℝ) ≤
      cylinderMean (tailCuts cuts) (anchorRows c a) D / 2)]
  exact (anchorCylinderTail (tailCuts cuts) (anchorRows c a) D (t := 1) (by norm_num)).2

/-- Every value of the assignment subtype has positive first-column probability. -/
theorem firstColumnProbability_pos {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) :
    0 < probability (fixedCountPMF cuts) (fun ω => ω 0 = c) := by
  have h := firstColumnConditionalExpect cuts c (fun _ => (1 : ℝ))
  rw [show expect (fixedCountPMF (tailCuts cuts)) (fun _ => (1 : ℝ)) = 1 from
    uniform_expect_const 1] at h
  by_contra hp
  have hz : probability (fixedCountPMF cuts) (fun ω => ω 0 = c) = 0 :=
    le_antisymm (le_of_not_gt hp) (probability_nonneg _ _)
  simp [conditionalExpect, hz] at h

theorem firstColumnCylinderMean {k n d : ℕ} (cuts : Cuts k n (d+1))
    (c : ColumnAssignments cuts 0) (a : Fin k) (D : Fin d → Finset (Fin k)) :
    conditionalExpect (fixedCountPMF cuts)
      (fun ω => (cylinderCount (tailCuts cuts) (anchorRows c a) D (tailSample ω) : ℝ))
      (fun ω => ω 0 = c) = cylinderMean (tailCuts cuts) (anchorRows c a) D := by
  rw [firstColumnConditionalExpect cuts c (fun ω =>
    (cylinderCount (tailCuts cuts) (anchorRows c a) D ω : ℝ))]
  exact (cylinderMean_eq_expect (tailCuts cuts) (anchorRows c a) D).symm

end RiffleUpperV2.Hypergeometric
