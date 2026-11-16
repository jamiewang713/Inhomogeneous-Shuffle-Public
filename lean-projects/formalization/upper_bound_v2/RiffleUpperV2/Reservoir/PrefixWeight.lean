import RiffleUpperV2.Reservoir.Cancellation
import RiffleLowerV2.Thinning.Residual

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile RiffleLowerV2.Thinning
attribute [local instance 2000] wordDecEq

theorem commonDigit_probability {k n L m : ℕ} (cuts : Cuts k n L) (j : Fin L)
    (e : Fin m ↪ Fin n) (a : Fin k) :
    probability (columnPMF cuts j) (fun c => ∀ q, c.val (e q) = a) =
      RiffleLowerV2.falling (cuts.count j a) m / RiffleLowerV2.falling n m := by
  have h := RiffleLowerV2.Factorial.column_request_probability cuts j (fun _ : Fin m => a) e
  have hprod : (∏ d : Fin k, RiffleLowerV2.falling (cuts.count j d)
      (Nat.card {q : Fin m // a = d})) = RiffleLowerV2.falling (cuts.count j a) m := by
    rw [Finset.prod_eq_single a]
    · simp
    · intro d _ hd
      simp [Ne.symm hd, RiffleLowerV2.falling]
    · simp
  rw [hprod, Fintype.card_fin] at h
  convert h using 1
  unfold probability RiffleLowerV2.probability
  congr 1
  funext c
  split_ifs <;> rfl

def commonDigits {k n L m : ℕ} {cuts : Cuts k n L} (e : Fin m ↪ Fin n)
    (J : Finset (Fin L)) (a : Fin L → Fin k) (ω : Sample cuts) : Prop :=
  ∀ j ∈ J, ∀ q, sampleEntry ω (e q) j = a j

/-- The unused columns sum out exactly. Only columns in J occur in this
ordered common-digit probability, and every factor has the correct population. -/
theorem commonDigits_probability {k n L m : ℕ} (cuts : Cuts k n L)
    (e : Fin m ↪ Fin n) (J : Finset (Fin L)) (a : Fin L → Fin k) :
    probability (fixedCountPMF cuts) (commonDigits e J a) =
      ∏ j ∈ J, RiffleLowerV2.falling (cuts.count j (a j)) m / RiffleLowerV2.falling n m := by
  let f : ∀ j, ColumnAssignments cuts j → ℝ := fun j c =>
    if j ∈ J then (if ∀ q, c.val (e q) = a j then 1 else 0) else 1
  have hi (ω : Sample cuts) : (if commonDigits e J a ω then (1 : ℝ) else 0) =
      ∏ j, f j (ω j) := by
    by_cases h : commonDigits e J a ω
    · simp only [h, if_true]
      symm
      apply Finset.prod_eq_one
      intro j _
      by_cases hj : j ∈ J
      · have hh : ∀ q, (ω j).val (e q) = a j := h j hj
        simp [f, hj, hh]
      · simp [f, hj]
    · simp only [h, if_false]
      unfold commonDigits at h
      push Not at h
      obtain ⟨j, hj, q, hq⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp only [f, hj, if_true]
      exact if_neg (fun hh => hq (hh q))
  calc
    _ = expect (fixedCountPMF cuts) (fun ω : Sample cuts => ∏ j, f j (ω j)) := by
      unfold probability RiffleLowerV2.probability
      apply congrArg (expect (fixedCountPMF cuts))
      funext ω
      convert hi ω using 1 <;> split_ifs <;> rfl
    _ = ∏ j, expect (columnPMF cuts j) (f j) :=
      RiffleLowerV2.Factorial.request_column_product cuts f
    _ = _ := by
      calc
        _ = ∏ j ∈ J, expect (columnPMF cuts j) (f j) := by
          symm
          apply Finset.prod_subset (Finset.subset_univ J)
          intro j _ hj
          simp only [f, hj, if_false]
          exact RiffleLowerV2.Model.expect_const _ _
        _ = _ := by
          apply Finset.prod_congr rfl
          intro j hj
          simp only [f, hj, if_true]
          convert commonDigit_probability cuts j e (a j) using 1
          unfold probability RiffleLowerV2.probability
          congr 1
          funext c
          split_ifs <;> rfl

/-- Exact residual prefix weight after full values on b distinct labels are
exposed. The complement enumeration and marked embedding are concrete; the
remaining fixed-count law is derived, never assumed. -/
theorem residual_commonDigits_probability {k n L b m : ℕ} (cuts : Cuts k n L)
    (r : RiffleLowerV2.RowPrescription n k L b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r))
    (e : Fin (n-b) → Fin n) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (f : Fin m ↪ Fin (n-b)) (J : Finset (Fin L)) (a : Fin L → Fin k) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => ∀ j ∈ J, ∀ q, sampleEntry ω (e (f q)) j = a j)
      (RiffleLowerV2.prescriptionEvent r) =
      ∏ j ∈ J, RiffleLowerV2.falling (cuts.count j (a j) - RiffleLowerV2.usedCount r j (a j)) m /
        RiffleLowerV2.falling (n-b) m := by
  obtain ⟨residual, hres, ht⟩ := residualConditionalProbability cuts r hr hp
  have h := ht e he hc (fun rows => ∀ j ∈ J, ∀ q, rows (f q) j = a j)
  change conditionalProbability (fixedCountPMF cuts) _ _ =
    probability (fixedCountPMF residual) (commonDigits f J a) at h
  rw [h, commonDigits_probability]
  simp only [hres]

end RiffleUpperV2.Reservoir
