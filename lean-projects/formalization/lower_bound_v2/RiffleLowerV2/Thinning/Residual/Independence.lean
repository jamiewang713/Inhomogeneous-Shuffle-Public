import RiffleLowerV2.Thinning.Residual

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Thinning
open TimeProfile

/-- Finite product factorization, adapted from the elementary proof of
`RiffleLower.uniform_pi_expect_prod` in the historical FixedColumns source.
The probability law here is the current canonical PMF. -/
theorem uniform_pi_expect_prod {I : Type*} [Fintype I] [DecidableEq I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] (f : ∀ i, Ω i → ℝ) :
    expect (PMF.uniformOfFintype (∀ i, Ω i)) (fun ω => ∏ i, f i (ω i)) =
      ∏ i, expect (PMF.uniformOfFintype (Ω i)) (f i) := by
  classical
  simp_rw [uniform_expect]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib]
  simp [Fintype.card_pi, Nat.cast_prod]

set_option maxHeartbeats 1000000 in
/-- Every admissible deterministic prescription leaves independent residual
columns, with their exact reduced counts, under any complement enumeration. -/
theorem residualColumnIndependence {k N K b : ℕ} (cuts : Cuts k N K)
    (r : RowPrescription N k K b) (_hb : b < N) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (prescriptionEvent r)) :
    ∃ residual : Cuts k (N-b) K,
      (∀ j a, residual.count j a = cuts.count j a - usedCount r j a) ∧
      ∀ e : Fin (N-b) → Fin N, Function.Injective e →
        (∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i) →
        ∀ f : Fin K → (Fin (N-b) → Fin k) → ℝ,
          conditionalExpect (fixedCountPMF cuts)
            (fun ω => ∏ j, f j (fun q => sampleEntry ω (e q) j)) (prescriptionEvent r) =
          ∏ j, expect (columnPMF residual j) (fun c => f j c.val) := by
  classical
  obtain ⟨residual, hres, htransport⟩ := residualConditionalExpect cuts r hr hp
  refine ⟨residual, hres, ?_⟩
  intro e he hc f
  calc
    _ = expect (fixedCountPMF residual)
        (fun η => ∏ j, f j (fun q => sampleEntry η q j)) :=
      htransport e he hc (fun rows => ∏ j, f j (fun q => rows q j))
    _ = _ := by
      change expect (PMF.uniformOfFintype (∀ j : Fin K, ColumnAssignments residual j))
        (fun η => ∏ j, f j (η j).val) =
        ∏ j, expect (PMF.uniformOfFintype (ColumnAssignments residual j)) (fun c => f j c.val)
      exact uniform_pi_expect_prod (I := Fin K) (Ω := ColumnAssignments residual)
        (fun j (c : ColumnAssignments residual j) => f j c.val)

end RiffleLowerV2.Thinning
