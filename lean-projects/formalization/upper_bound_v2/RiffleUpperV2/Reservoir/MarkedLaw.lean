import RiffleUpperV2.Reservoir.History
import RiffleLowerV2.Factorial.Exact
import RiffleUpperV2.Shared.Conditioning

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile

attribute [local instance 2000] wordDecEq

def tupleWords {k n L m : ℕ} {cuts : Cuts k n L} (e : Fin m ↪ Fin n)
    (ω : Sample cuts) : Fin m → Word k L := fun q => rowWord ω (e q)

/-- Completion-count weight, with every unlisted label summed out. Impossible
digit allocations have zero falling factorial, including zero-size piles. -/
def tupleWeight {k n L m : ℕ} (cuts : Cuts k n L) (w : Fin m → Word k L) : ℝ :=
  ∏ j : Fin L, (∏ a : Fin k, RiffleLowerV2.falling (cuts.count j a)
    (Finset.univ.filter fun q => (w q).get j = a).card) / RiffleLowerV2.falling n m

theorem tupleWeight_zero_of_overflow {k n L m : ℕ} (cuts : Cuts k n L)
    (w : Fin m → Word k L) (j : Fin L) (a : Fin k)
    (h : cuts.count j a < (Finset.univ.filter fun q => (w q).get j = a).card) :
    tupleWeight cuts w = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply (div_eq_zero_iff).mpr
  left
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp only [RiffleLowerV2.falling, Nat.descFactorial_of_lt h, Nat.cast_zero]

theorem tupleWords_probability {k n L m : ℕ} (cuts : Cuts k n L)
    (e : Fin m ↪ Fin n) (w : Fin m → Word k L) :
    probability (fixedCountPMF cuts) (fun ω => tupleWords e ω = w) = tupleWeight cuts w := by
  let f : ∀ j, ColumnAssignments cuts j → ℝ := fun j c =>
    if ∀ q : Fin m, c.val (e q) = (w q).get j then 1 else 0
  have he (ω : Sample cuts) : tupleWords e ω = w ↔
      ∀ j q, (ω j).val (e q) = (w q).get j := by
    constructor
    · intro h j q
      have hh := congrArg (fun z : Fin m → Word k L => (z q).get j) h
      simpa only [tupleWords, RiffleLowerV2.rowWord_get, sampleEntry] using hh
    · intro h
      funext q
      apply List.Vector.ext
      intro j
      simpa only [tupleWords, RiffleLowerV2.rowWord_get, sampleEntry] using h j q
  have hi (ω : Sample cuts) : (if tupleWords e ω = w then (1 : ℝ) else 0) =
      ∏ j, f j (ω j) := by
    by_cases h : ∀ j q, (ω j).val (e q) = (w q).get j
    · simp [he, h, f]
    · rw [if_neg (fun hh => h ((he ω).mp hh))]
      push Not at h
      obtain ⟨j, q, hq⟩ := h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (fun hh => hq (hh q)))
  calc
    _ = expect (fixedCountPMF cuts) (fun ω : Sample cuts => ∏ j, f j (ω j)) := by
      unfold probability RiffleLowerV2.probability
      apply congrArg (expect (fixedCountPMF cuts))
      funext ω
      convert hi ω using 1
      by_cases hh : tupleWords e ω = w <;> simp [hh]
    _ = ∏ j, expect (columnPMF cuts j) (f j) :=
      RiffleLowerV2.Factorial.request_column_product cuts f
    _ = tupleWeight cuts w := by
      unfold tupleWeight
      apply Finset.prod_congr rfl
      intro j _
      change expect (columnPMF cuts j)
        (fun c => if ∀ q, c.val (e q) = (w q).get j then 1 else 0) = _
      have hc := RiffleLowerV2.Factorial.column_request_probability cuts j (fun q => (w q).get j) e
      simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fin] at hc
      convert hc using 1
      congr 1
      funext c
      split_ifs <;> rfl

private theorem finite_expect_partition {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (P : PMF Ω) (f : Ω → Γ) (F : Γ → ℝ) :
    expect P (fun ω => F (f ω)) =
      ∑ w : Γ, probability P (fun ω => f ω = w) * F w := by
  classical
  simp only [RiffleLowerV2.probability, RiffleLowerV2.expect, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

theorem tupleWords_expect {k n L m : ℕ} (cuts : Cuts k n L)
    (e : Fin m ↪ Fin n) (F : (Fin m → Word k L) → ℝ) :
    expect (fixedCountPMF cuts) (fun ω => F (tupleWords e ω)) =
      ∑ w : Fin m → Word k L, tupleWeight cuts w * F w := by
  rw [finite_expect_partition]
  simp_rw [tupleWords_probability]

theorem tupleWords_event {k n L m : ℕ} (cuts : Cuts k n L)
    (e : Fin m ↪ Fin n) (B : (Fin m → Word k L) → Prop) :
    probability (fixedCountPMF cuts) (fun ω => B (tupleWords e ω)) =
      ∑ w : Fin m → Word k L, if B w then tupleWeight cuts w else 0 := by
  have h := tupleWords_expect cuts e (fun w => if B w then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  convert h using 1
  unfold probability RiffleLowerV2.probability
  congr 1

/-- A realized event has a positive normalizing weight. This is qualitative
positivity only; it supplies no uniform reserve lower bound. -/
theorem tupleWords_event_positive {k n L m : ℕ} (cuts : Cuts k n L)
    (e : Fin m ↪ Fin n) (B : (Fin m → Word k L) → Prop) (ω : Sample cuts)
    (hω : B (tupleWords e ω)) :
    0 < ∑ w : Fin m → Word k L, if B w then tupleWeight cuts w else 0 := by
  rw [← tupleWords_event cuts e B]
  unfold probability RiffleLowerV2.probability RiffleLowerV2.expect
  apply Finset.sum_pos'
  · intro v _
    positivity
  · refine ⟨ω, Finset.mem_univ _, ?_⟩
    simp only [hω, if_true, mul_one]
    change 0 < ((PMF.uniformOfFintype (Sample cuts)) ω).toReal
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- If precisely the prescribed pile-size many distinct labels start with p,
they are the entire p-pile, so no unlisted row can affect its history. -/
theorem tuplePile_exhausts {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω : Sample cuts)
    (he : ∀ q, (tupleWords e ω q).get 0 = p) :
    ∀ r : Fin n, (rowWord ω r).get 0 = p ↔ ∃ q, e q = r := by
  classical
  let P := Finset.univ.filter (fun r : Fin n => (rowWord ω r).get 0 = p)
  have hP : P.card = pileSize cuts p := (ω 0).property p
  have hs : Finset.univ.map e ⊆ P := by
    intro r hr
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he q⟩
  have hEq : Finset.univ.map e = P :=
    Finset.eq_of_subset_of_card_le hs (by simp [hP])
  intro r
  have hh := Finset.ext_iff.mp hEq r
  simpa [P] using hh.symm

theorem tuplePile_wordCount {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω : Sample cuts)
    (he : ∀ q, (tupleWords e ω q).get 0 = p)
    (u : Word k (L+1)) (hu : u.get 0 = p) :
    wordCount ω u = tupleCount (tupleWords e ω) u := by
  classical
  symm
  apply Finset.card_bij (fun q _ => e q)
  · intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
  · intro q _ r _ hqr; exact e.injective hqr
  · intro r hr
    have hru := (Finset.mem_filter.mp hr).2
    obtain ⟨q, hq⟩ := (tuplePile_exhausts cuts p e ω he r).mp (by rw [hru]; exact hu)
    refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hq⟩
    change rowWord ω (e q) = u
    rwa [hq]

def tupleHistoryConstraint {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (w : Fin (pileSize cuts p) → Word k (L+1)) : Prop :=
  (∀ q, (w q).get 0 = p) ∧
  (∀ u : Word k (L+1), u.get 0 = p → u < pileWords cuts p ω j →
    tupleCount w u = observedCount (pileWords cuts p ω) (j.val+1) u) ∧
  observedCount (pileWords cuts p ω) (j.val+1) (pileWords cuts p ω j) ≤
    tupleCount w (pileWords cuts p ω j)

theorem tupleHistoryConstraint_iff {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω v : Sample cuts)
    (j : Fin (pileSize cuts p)) :
    tupleHistoryConstraint cuts p ω j (tupleWords e v) ↔
      (∀ q, (tupleWords e v q).get 0 = p) ∧
        historyFiber cuts p .forward (j.val+1) ω v := by
  rw [historyAtom]
  unfold tupleHistoryConstraint
  apply and_congr_right
  intro he
  apply and_congr
  · apply forall_congr'
    intro u
    apply imp_congr_right
    intro hu
    rw [tuplePile_wordCount cuts p e v he u hu]
  · rw [tuplePile_wordCount cuts p e v he _ (pileWords_first cuts p ω j)]

/-- Exact finite conditional law after fixing the labeled pile, the unmarked
pile rows A, and the natural sorted history. The weights retain the full-pile
completion factors; the outside reservoir has been summed out exactly.
No residual-law hypothesis is supplied by the caller. -/
theorem exactMarkedRowLaw {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω : Sample cuts)
    (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1))
    (F : (Fin (pileSize cuts p) → Word k (L+1)) → ℝ) :
    conditionalExpect (fixedCountPMF cuts) (fun v => F (tupleWords e v))
      (fun v => (∀ q, (tupleWords e v q).get 0 = p) ∧
        historyFiber cuts p .forward (j.val+1) ω v ∧
        ∀ q ∈ A, tupleWords e v q = a q) =
    (∑ w : Fin (pileSize cuts p) → Word k (L+1),
      if tupleHistoryConstraint cuts p ω j w ∧ (∀ q ∈ A, w q = a q)
      then tupleWeight cuts w * F w else 0) /
    (∑ w : Fin (pileSize cuts p) → Word k (L+1),
      if tupleHistoryConstraint cuts p ω j w ∧ (∀ q ∈ A, w q = a q)
      then tupleWeight cuts w else 0) := by
  let B := fun w : Fin (pileSize cuts p) → Word k (L+1) =>
    tupleHistoryConstraint cuts p ω j w ∧ (∀ q ∈ A, w q = a q)
  have hb (v : Sample cuts) : B (tupleWords e v) ↔
      (∀ q, (tupleWords e v q).get 0 = p) ∧
        historyFiber cuts p .forward (j.val+1) ω v ∧
        ∀ q ∈ A, tupleWords e v q = a q := by
    simp only [B, tupleHistoryConstraint_iff, and_assoc]
  have hevent : (fun v : Sample cuts => (∀ q, (tupleWords e v q).get 0 = p) ∧
      historyFiber cuts p .forward (j.val+1) ω v ∧ ∀ q ∈ A, tupleWords e v q = a q) =
      fun v => B (tupleWords e v) := funext (fun v => propext (hb v).symm)
  rw [hevent]
  unfold conditionalExpect RiffleLowerV2.conditionalExpect RiffleLowerV2.probability
  apply congrArg₂ (fun x y : ℝ => x / y)
  · trans ∑ w : Fin (pileSize cuts p) → Word k (L+1),
        tupleWeight cuts w * (if B w then F w else 0)
    · convert tupleWords_expect cuts e (fun w => if B w then F w else 0) using 1
      congr 1
      funext v
      by_cases h : B (tupleWords e v) <;> simp [h]
    · simp only [B, mul_ite, mul_zero]
  · trans ∑ w : Fin (pileSize cuts p) → Word k (L+1),
        tupleWeight cuts w * (if B w then 1 else 0)
    · convert tupleWords_expect cuts e (fun w => if B w then 1 else 0) using 1
      congr 1
      funext v
      by_cases h : B (tupleWords e v) <;> simp [h]
    · simp only [B, mul_ite, mul_zero, mul_one]

end RiffleUpperV2.Reservoir
