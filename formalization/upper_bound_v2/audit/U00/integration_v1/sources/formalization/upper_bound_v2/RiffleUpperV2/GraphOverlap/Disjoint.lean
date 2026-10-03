import RiffleUpperV2.GraphOverlap.RunProduct

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.GraphOverlap

theorem boundedComponents_population {N : ℕ} (G : PathEdges N) : BoundedComponents G N := by
  intro c
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem edgeDisjointOverlap {N : ℕ} (G H : PathEdges N) (hd : Disjoint G H) :
    overlap G H ≤ 1 := by
  have h := boundedComponentOverlap_strong G H (boundedComponents_population H)
  simpa only [Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty, pow_zero] using h

theorem edgeDisjointFactorial {N : ℕ} (G H : PathEdges N) (hd : Disjoint G H) :
    componentFactorial G * componentFactorial H ≤ componentFactorial (G ∪ H) := by
  have h := boundedComponentFactorial G H (boundedComponents_population H)
  simpa only [Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty, pow_zero, mul_one] using h

/-- The source's elementary monochromatic-run factorial inequality. -/
theorem runFactorial_aux (a b : ℕ) :
    (a+1).factorial * (b+1).factorial ≤ (a+b+1).factorial := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hs : a+1+b+1 = (a+b+1)+1 := by omega
    rw [hs, Nat.factorial_succ (a+1), Nat.factorial_succ (a+b+1)]
    calc
      (a+1+1) * (a+1).factorial * (b+1).factorial =
          (a+1+1) * ((a+1).factorial * (b+1).factorial) := by ring
      _ ≤ (a+b+1+1) * (a+b+1).factorial := Nat.mul_le_mul (by omega) ih

theorem runFactorial (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a.factorial * b.factorial ≤ (a+b-1).factorial := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  have he : (a+1)+(b+1)-1 = a+b+1 := by omega
  simpa only [Nat.succ_eq_add_one, he] using runFactorial_aux a b

end RiffleUpperV2.GraphOverlap
