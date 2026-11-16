import RiffleLowerV2.Occupancy.ConditionalInputs

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace RiffleLowerV2.Occupancy
open TimeProfile

/-- An ordered tuple of distinct labels is prescribed one common full word. -/
def sameWordPrescription {N k K b : ℕ} (w : Word k K) (e : Fin b ↪ Fin N) :
    RowPrescription N k K b := ⟨e, fun _ => w⟩

theorem sameWordPrescription_row_injective {N k K b : ℕ} (w : Word k K)
    (e : Fin b ↪ Fin N) : Function.Injective (sameWordPrescription w e).row := e.injective

/-- The probability of any prescribed labelled tuple is an explicit positive product. -/
theorem sameWord_forcing_probability {N k K b : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (e : Fin b ↪ Fin N) :
    probability (fixedCountPMF cuts) (prescriptionEvent (sameWordPrescription w e)) =
      ∏ j, falling (cuts.count j (w.get j)) b / falling N b := by
  let e' : (Σ _ : Fin 1, Fin b) ↪ Fin N :=
    ⟨fun x => e x.2, by
      rintro ⟨i, x⟩ ⟨j, y⟩ h
      have hxy : x = y := e.injective h
      subst y
      have hij : i = j := Subsingleton.elim _ _
      subst j
      rfl⟩
  have h := Factorial.request_probability cuts (fun _ : Fin 1 => w) (fun _ => b) e'
  have hprod (j : Fin K) :
      (∏ a, falling (cuts.count j a) (requestedCount (fun _ : Fin 1 => w) (fun _ => b) j a)) =
        falling (cuts.count j (w.get j)) b := by
    rw [Finset.prod_eq_single (w.get j)]
    · simp [requestedCount]
    · intro a _ ha
      simp [requestedCount, Ne.symm ha, falling]
    · simp
  simp_rw [hprod] at h
  simp only [Fin.sum_univ_one] at h
  rw [← h]
  unfold probability
  congr 1
  funext ω
  have hevent : prescriptionEvent (sameWordPrescription w e) ω ↔
      ∀ x : Σ _ : Fin 1, Fin b, rowWord ω (e' x) = w := by
    constructor
    · intro hp x
      exact hp x.2
    · intro hp q
      exact hp ⟨0, q⟩
  simp only [hevent]

/-- Pile feasibility proves positivity, uniformly over the prescribed labels. -/
theorem sameWord_forcing_pos {N k K b : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (e : Fin b ↪ Fin N) (hb : b ≤ N)
    (hpiles : ∀ j, b ≤ cuts.count j (w.get j)) :
    0 < probability (fixedCountPMF cuts) (prescriptionEvent (sameWordPrescription w e)) := by
  rw [sameWord_forcing_probability]
  apply Finset.prod_pos
  intro j _
  apply div_pos
  · unfold falling
    exact_mod_cast Nat.descFactorial_pos.mpr (hpiles j)
  · unfold falling
    exact_mod_cast Nat.descFactorial_pos.mpr hb

private def forcingEmbeddingsEquiv {N k K b : ℕ} {cuts : Cuts k N K}
    (w : Word k K) (ω : Sample cuts) :
    (Fin b ↪ {i : Fin N // rowWord ω i = w}) ≃
      {e : Fin b ↪ Fin N // prescriptionEvent (sameWordPrescription w e) ω} where
  toFun e := ⟨⟨fun q => (e q).val, fun x y h => e.injective (Subtype.ext h)⟩,
    fun q => (e q).property⟩
  invFun e := ⟨fun q => ⟨e.val q, e.property q⟩,
    fun x y h => e.val.injective (congrArg Subtype.val h)⟩
  left_inv e := by ext q; rfl
  right_inv e := by apply Subtype.ext; ext q; rfl

/-- A falling factorial counts all ordered distinct tuples carrying the word. -/
theorem falling_eq_forcing_sum {N k K b : ℕ} {cuts : Cuts k N K}
    (w : Word k K) (ω : Sample cuts) :
    falling (wordCount w ω) b =
      ∑ e : Fin b ↪ Fin N, if prescriptionEvent (sameWordPrescription w e) ω then 1 else 0 := by
  have h := Fintype.card_congr (forcingEmbeddingsEquiv (b := b) w ω)
  rw [Fintype.card_embedding_eq, Fintype.card_fin, ← Factorial.wordCount_eq_card] at h
  have hc := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [falling, Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hc

/-- Averaging the tuple expansion gives the sum of its positive forcing probabilities. -/
theorem falling_expect_eq_forcing_sum {N k K b : ℕ} (cuts : Cuts k N K)
    (w : Word k K) :
    expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) b) =
      ∑ e : Fin b ↪ Fin N, probability (fixedCountPMF cuts) (prescriptionEvent (sameWordPrescription w e)) := by
  simp_rw [falling_eq_forcing_sum]
  exact Factorial.expect_sum _ Finset.univ _

/-- The weighted tuple expansion keeps the arbitrary event inside each joint probability. -/
theorem falling_weighted_event_eq_forcing_sum {N k K b : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (A : Sample cuts → Prop) :
    expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) b * (if A ω then 1 else 0)) =
      ∑ e : Fin b ↪ Fin N, probability (fixedCountPMF cuts)
        (fun ω => A ω ∧ prescriptionEvent (sameWordPrescription w e) ω) := by
  have hpoint (ω : Sample cuts) :
      falling (wordCount w ω) b * (if A ω then 1 else 0) =
      ∑ e : Fin b ↪ Fin N, if A ω ∧ prescriptionEvent (sameWordPrescription w e) ω then 1 else 0 := by
    rw [falling_eq_forcing_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    by_cases ha : A ω <;> by_cases he : prescriptionEvent (sameWordPrescription w e) ω <;>
      simp [ha, he]
  simp_rw [hpoint]
  rw [Factorial.expect_sum]
  apply Finset.sum_congr rfl
  intro e _
  unfold probability
  congr 1
  funext ω
  by_cases h : A ω ∧ prescriptionEvent (sameWordPrescription w e) ω <;> simp [h]

/-- A uniform conditional relative estimate passes through the exact factorial sum. -/
theorem forcing_weighted_relative_error {N k K b : ℕ} (cuts : Cuts k N K)
    (w : Word k K) (A : Sample cuts → Prop) (δ : ℝ)
    (hpos : ∀ e : Fin b ↪ Fin N,
      0 < probability (fixedCountPMF cuts) (prescriptionEvent (sameWordPrescription w e)))
    (hcond : ∀ e : Fin b ↪ Fin N,
      |conditionalProbability (fixedCountPMF cuts) A (prescriptionEvent (sameWordPrescription w e)) -
        probability (fixedCountPMF cuts) A| ≤ δ * probability (fixedCountPMF cuts) A) :
    |expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) b * (if A ω then 1 else 0)) -
      expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) b) * probability (fixedCountPMF cuts) A| ≤
      δ * expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) b) * probability (fixedCountPMF cuts) A := by
  let P := fixedCountPMF cuts
  let p := probability P A
  let E : (Fin b ↪ Fin N) → Sample cuts → Prop :=
    fun e => prescriptionEvent (sameWordPrescription w e)
  let q := fun e : Fin b ↪ Fin N => probability P (E e)
  have hterm (e : Fin b ↪ Fin N) :
      |probability P (fun ω => A ω ∧ E e ω) - q e * p| ≤ q e * (δ * p) := by
    have he : 0 < q e := hpos e
    have hjoint : probability P (fun ω => A ω ∧ E e ω) =
        q e * conditionalProbability P A (E e) := by
      unfold conditionalProbability
      change _ = q e * (_ / q e)
      field_simp [he.ne']
    rw [hjoint, ← mul_sub, abs_mul, abs_of_pos he]
    exact mul_le_mul_of_nonneg_left (hcond e) he.le
  rw [falling_weighted_event_eq_forcing_sum, falling_expect_eq_forcing_sum]
  change |(∑ e, probability P (fun ω => A ω ∧ E e ω)) - (∑ e, q e) * p| ≤
    δ * (∑ e, q e) * p
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ e, |probability P (fun ω => A ω ∧ E e ω) - q e * p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, q e * (δ * p) := Finset.sum_le_sum fun e _ => hterm e
    _ = δ * (∑ e, q e) * p := by rw [← Finset.sum_mul]; ring

/-- A distinct tested word is not counted among the same-word prescriptions. -/
theorem sameWord_prescribed_other_count {N k K b : ℕ} (w v : Word k K)
    (e : Fin b ↪ Fin N) (hwv : w ≠ v) :
    (Finset.univ.filter fun q => (sameWordPrescription w e).word q = v).card = 0 := by
  simp [sameWordPrescription, hwv]

end RiffleLowerV2.Occupancy
