import RiffleUpperV2.Reservoir.PrefixWeight

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile RiffleLowerV2.Thinning

theorem commonDigits_insert_zero {k n L m : ℕ} (cuts : Cuts k n (L+1))
    (e : Fin m ↪ Fin n) (J : Finset (Fin (L+1))) (hJ : (0 : Fin (L+1)) ∉ J)
    (a : Fin (L+1) → Fin k) (p : Fin k) (ω : Sample cuts) :
    commonDigits e (insert 0 J) (Function.update a 0 p) ω ↔
      (∀ q, sampleEntry ω (e q) 0 = p) ∧ commonDigits e J a ω := by
  unfold commonDigits
  simp only [Finset.mem_insert, forall_eq_or_imp, Function.update_self]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply imp_congr_right
  intro hj
  have hj0 : j ≠ 0 := by intro hh; exact hJ (hh ▸ hj)
  rw [Function.update_of_ne hj0]

theorem commonDigits_firstColumn_joint {k n L m : ℕ} (cuts : Cuts k n (L+1))
    (e : Fin m ↪ Fin n) (J : Finset (Fin (L+1))) (hJ : (0 : Fin (L+1)) ∉ J)
    (a : Fin (L+1) → Fin k) (p : Fin k) :
    probability (fixedCountPMF cuts) (fun ω =>
      (∀ q, sampleEntry ω (e q) 0 = p) ∧ commonDigits e J a ω) =
    (RiffleLowerV2.falling (cuts.count 0 p) m / RiffleLowerV2.falling n m) *
      ∏ j ∈ J, RiffleLowerV2.falling (cuts.count j (a j)) m / RiffleLowerV2.falling n m := by
  have he : (fun ω : Sample cuts => (∀ q, sampleEntry ω (e q) 0 = p) ∧ commonDigits e J a ω) =
      commonDigits e (insert 0 J) (Function.update a 0 p) := by
    funext ω
    exact propext (commonDigits_insert_zero cuts e J hJ a p ω).symm
  rw [he, commonDigits_probability, Finset.prod_insert hJ, Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (by intro h; exact hJ (h ▸ hj))]

theorem commonDigits_firstColumn_probability {k n L m : ℕ} (cuts : Cuts k n (L+1))
    (e : Fin m ↪ Fin n) (p : Fin k) :
    probability (fixedCountPMF cuts) (fun ω => ∀ q, sampleEntry ω (e q) 0 = p) =
      RiffleLowerV2.falling (cuts.count 0 p) m / RiffleLowerV2.falling n m := by
  have h := commonDigits_probability cuts e {0} (fun _ => p)
  have he : commonDigits (cuts := cuts) e {0} (fun _ => p) =
      (fun ω => ∀ q, sampleEntry ω (e q) 0 = p) := by
    funext ω
    simp [commonDigits]
  rw [he] at h
  simpa only [Finset.prod_singleton] using h

/-- The first-column marked-pile condition leaves every later-column prefix
weight unchanged. Its positivity is discharged by the available first digit count. -/
theorem commonDigits_given_firstColumn {k n L m : ℕ} (cuts : Cuts k n (L+1))
    (e : Fin m ↪ Fin n) (J : Finset (Fin (L+1))) (hJ : (0 : Fin (L+1)) ∉ J)
    (a : Fin (L+1) → Fin k) (p : Fin k) (hp : m ≤ cuts.count 0 p) :
    conditionalProbability (fixedCountPMF cuts) (commonDigits e J a)
      (fun ω => ∀ q, sampleEntry ω (e q) 0 = p) =
      ∏ j ∈ J, RiffleLowerV2.falling (cuts.count j (a j)) m / RiffleLowerV2.falling n m := by
  have hne : RiffleLowerV2.falling (cuts.count 0 p) m / RiffleLowerV2.falling n m ≠ 0 := by
    apply ne_of_gt
    apply div_pos <;> unfold RiffleLowerV2.falling
    · exact_mod_cast Nat.descFactorial_pos.mpr hp
    · exact_mod_cast Nat.descFactorial_pos.mpr (by simpa using Fintype.card_le_of_embedding e)
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  have he : (fun ω : Sample cuts => commonDigits e J a ω ∧ ∀ q, sampleEntry ω (e q) 0 = p) =
      (fun ω => (∀ q, sampleEntry ω (e q) 0 = p) ∧ commonDigits e J a ω) := by
    funext ω
    exact propext and_comm
  rw [he]
  calc
    _ = ((RiffleLowerV2.falling (cuts.count 0 p) m / RiffleLowerV2.falling n m) *
          ∏ j ∈ J, RiffleLowerV2.falling (cuts.count j (a j)) m / RiffleLowerV2.falling n m) /
          (RiffleLowerV2.falling (cuts.count 0 p) m / RiffleLowerV2.falling n m) :=
      congrArg₂ (fun x y : ℝ => x/y) (commonDigits_firstColumn_joint cuts e J hJ a p)
        (commonDigits_firstColumn_probability cuts e p)
    _ = _ := mul_div_cancel_left₀ _ hne

theorem conditionalProbability_refine {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (A B C : Ω → Prop) (hB : probability P B ≠ 0) :
    conditionalProbability P A (fun ω => B ω ∧ C ω) =
      conditionalProbability P (fun ω => A ω ∧ C ω) B / conditionalProbability P C B := by
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  have hnum : (fun ω => A ω ∧ B ω ∧ C ω) = (fun ω => (A ω ∧ C ω) ∧ B ω) := by
    funext ω
    apply propext
    tauto
  have hden : (fun ω => B ω ∧ C ω) = (fun ω => C ω ∧ B ω) := by
    funext ω
    exact propext and_comm
  rw [hnum, hden, div_div_div_cancel_right₀ hB]

/-- Exact source prefix weight after exposing the other pile rows and fixing
the marked first digits. The residual count and c+m population are explicit;
neither column independence nor a conditional law is assumed. -/
theorem residual_prefixWeight_given_pile {k n L b m : ℕ} (cuts : Cuts k n (L+1))
    (r : RiffleLowerV2.RowPrescription n k (L+1) b) (hr : Function.Injective r.row)
    (hp : 0 < probability (fixedCountPMF cuts) (RiffleLowerV2.prescriptionEvent r))
    (e : Fin (n-b) → Fin n) (he : Function.Injective e)
    (hc : ∀ i, (∃ q, e q = i) ↔ ¬∃ q, r.row q = i)
    (f : Fin m ↪ Fin (n-b)) (J : Finset (Fin (L+1))) (hJ : (0 : Fin (L+1)) ∉ J)
    (a : Fin (L+1) → Fin k) (p : Fin k)
    (hcount : m ≤ cuts.count 0 p - RiffleLowerV2.usedCount r 0 p) :
    conditionalProbability (fixedCountPMF cuts)
      (fun ω => ∀ j ∈ J, ∀ q, sampleEntry ω (e (f q)) j = a j)
      (fun ω => RiffleLowerV2.prescriptionEvent r ω ∧
        ∀ q, sampleEntry ω (e (f q)) 0 = p) =
    ∏ j ∈ J, RiffleLowerV2.falling (cuts.count j (a j) - RiffleLowerV2.usedCount r j (a j)) m /
      RiffleLowerV2.falling (n-b) m := by
  obtain ⟨residual, hres, ht⟩ := residualConditionalProbability cuts r hr hp
  rw [conditionalProbability_refine _ _ _ _ (ne_of_gt hp)]
  have hnum := ht e he hc (fun rows =>
    (∀ j ∈ J, ∀ q, rows (f q) j = a j) ∧ ∀ q, rows (f q) 0 = p)
  have hden := ht e he hc (fun rows => ∀ q, rows (f q) 0 = p)
  calc
    _ = conditionalProbability (fixedCountPMF residual) (commonDigits f J a)
          (fun ω => ∀ q, sampleEntry ω (f q) 0 = p) :=
      congrArg₂ (fun x y : ℝ => x/y) hnum hden
    _ = _ := by
      have hh := commonDigits_given_firstColumn residual f J hJ a p (by rwa [hres])
      simpa only [hres] using hh

end RiffleUpperV2.Reservoir
