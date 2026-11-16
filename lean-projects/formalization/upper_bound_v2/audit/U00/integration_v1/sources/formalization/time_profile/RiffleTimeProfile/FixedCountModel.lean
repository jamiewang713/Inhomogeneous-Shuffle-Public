import RiffleTimeProfile.Ambient
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-! P01: the exact uniform sample space of matrices with fixed column counts. -/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace TimeProfile

def ColumnAssignments {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :=
  {a : Fin N → Fin k // ∀ l : Fin k,
    (Finset.univ.filter (fun i => a i = l)).card = cuts.count j l}

instance {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
    Fintype (ColumnAssignments cuts j) := by
  classical
  unfold ColumnAssignments
  infer_instance

theorem columnAssignments_nonempty {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
    Nonempty (ColumnAssignments cuts j) := by
  classical
  have hcard : Fintype.card (Σ l : Fin k, Fin (cuts.count j l)) = N := by
    simpa using cuts.sum_count j
  let e : (Σ l : Fin k, Fin (cuts.count j l)) ≃ Fin N := Fintype.equivFinOfCardEq hcard
  let a : Fin N → Fin k := fun i => (e.symm i).1
  refine ⟨⟨a, ?_⟩⟩
  intro l
  have hfiber : Finset.univ.filter (fun i => a i = l) =
      Finset.univ.image (fun q : Fin (cuts.count j l) => e ⟨l, q⟩) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      rcases hsplit : e.symm i with ⟨m, q⟩
      have hm : m = l := by simpa only [a, hsplit] using hi
      subst m
      refine ⟨q, ?_⟩
      have heq := congrArg e hsplit
      simpa only [Equiv.apply_symm_apply] using heq.symm
    · rintro ⟨q, rfl⟩
      simp [a]
  have hinj : Function.Injective (fun q : Fin (cuts.count j l) => e ⟨l, q⟩) := by
    intro q q' hq
    have hp := e.injective hq
    exact eq_of_heq (Sigma.mk.inj_iff.mp hp).2
  rw [hfiber, Finset.card_image_of_injective _ hinj]
  simp

instance {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
    Nonempty (ColumnAssignments cuts j) := columnAssignments_nonempty cuts j

instance {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
    MeasurableSpace (ColumnAssignments cuts j) := ⊤

instance {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
    MeasurableSingletonClass (ColumnAssignments cuts j) := ⟨fun _ => trivial⟩

def ShuffleSample {k N K : ℕ} (cuts : Cuts k N K) :=
  (j : Fin K) → ColumnAssignments cuts j

instance {k N K : ℕ} (cuts : Cuts k N K) : Fintype (ShuffleSample cuts) := by
  unfold ShuffleSample
  infer_instance

instance {k N K : ℕ} (cuts : Cuts k N K) : Nonempty (ShuffleSample cuts) :=
  ⟨fun j => Classical.choice (columnAssignments_nonempty cuts j)⟩

instance {k N K : ℕ} (cuts : Cuts k N K) : MeasurableSpace (ShuffleSample cuts) := ⊤

instance {k N K : ℕ} (cuts : Cuts k N K) : MeasurableSingletonClass (ShuffleSample cuts) :=
  ⟨fun _ => trivial⟩

def columnPMF {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) : PMF (ColumnAssignments cuts j) :=
  PMF.uniformOfFintype (ColumnAssignments cuts j)

def columnMeasure {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) : Measure (ColumnAssignments cuts j) :=
  (columnPMF cuts j).toMeasure

def fixedCountPMF {k N K : ℕ} (cuts : Cuts k N K) : PMF (ShuffleSample cuts) :=
  PMF.uniformOfFintype (ShuffleSample cuts)

def fixedCountMeasure {k N K : ℕ} (cuts : Cuts k N K) : Measure (ShuffleSample cuts) :=
  (fixedCountPMF cuts).toMeasure

instance {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K) :
    IsProbabilityMeasure (columnMeasure cuts j) := by
  unfold columnMeasure
  infer_instance

instance {k N K : ℕ} (cuts : Cuts k N K) : IsProbabilityMeasure (fixedCountMeasure cuts) := by
  unfold fixedCountMeasure
  infer_instance

def sampleEntry {k N K : ℕ} {cuts : Cuts k N K}
    (sample : ShuffleSample cuts) (row : Fin N) (col : Fin K) : Fin k :=
  (sample col).val row

def sampleRow {k N K : ℕ} {cuts : Cuts k N K}
    (sample : ShuffleSample cuts) (row : Fin N) : Fin K → Fin k :=
  fun col => sampleEntry sample row col

def rowsSatisfying {k N K : ℕ} (rows : Fin N → Fin K → Fin k)
    (B : (Fin K → Fin k) → Prop) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => B (rows i))

def rowCount {k N K : ℕ} (rows : Fin N → Fin K → Fin k)
    (B : (Fin K → Fin k) → Prop) : ℕ :=
  (rowsSatisfying rows B).card

def boxRows {k N K : ℕ} {cuts : Cuts k N K}
    (A : Fin K → Finset (Fin k)) (sample : ShuffleSample cuts) : Finset (Fin N) :=
  rowsSatisfying (sampleRow sample) (fun row => ∀ j, row j ∈ A j)

def prefixRows {k N K : ℕ} {cuts : Cuts k N K}
    (x : Fin K → Fin k) (M : ℕ) (sample : ShuffleSample cuts) : Finset (Fin N) :=
  rowsSatisfying (sampleRow sample) (fun row => ∀ j, j.val < M → row j = x j)

def leftSideRows {k N K : ℕ} {cuts : Cuts k N K}
    (x : Fin K → Fin k) (j : Fin K) (sample : ShuffleSample cuts) : Finset (Fin N) :=
  rowsSatisfying (sampleRow sample)
    (fun row => (∀ h, h.val < j.val → row h = x h) ∧ row j < x j)

def rightSideRows {k N K : ℕ} {cuts : Cuts k N K}
    (x : Fin K → Fin k) (j : Fin K) (sample : ShuffleSample cuts) : Finset (Fin N) :=
  rowsSatisfying (sampleRow sample)
    (fun row => (∀ h, h.val < j.val → row h = x h) ∧ x j < row j)

theorem columnAssignments_count {k N K : ℕ} {cuts : Cuts k N K} {j : Fin K}
    (a : ColumnAssignments cuts j) (l : Fin k) :
    (Finset.univ.filter (fun i => a.val i = l)).card = cuts.count j l :=
  a.property l

theorem sample_column_counts {k N K : ℕ} {cuts : Cuts k N K}
    (sample : ShuffleSample cuts) (j : Fin K) (l : Fin k) :
    (Finset.univ.filter (fun i => sampleEntry sample i j = l)).card = cuts.count j l :=
  (sample j).property l

theorem sample_entry_count_pos {k N K : ℕ} {cuts : Cuts k N K}
    (sample : ShuffleSample cuts) (row : Fin N) (j : Fin K) :
    0 < cuts.count j (sampleEntry sample row j) := by
  rw [← sample_column_counts sample j (sampleEntry sample row j)]
  apply Finset.card_pos.mpr
  exact ⟨row, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem sample_row_legal {k N K : ℕ} {cuts : Cuts k N K} (hN : 0 < N)
    (sample : ShuffleSample cuts) (row : Fin N) :
    LegalPrefix (cuts.profile hN) (sampleRow sample row) K := by
  intro j _
  exact (cuts.profile_pos_iff hN j _).mpr (sample_entry_count_pos sample row j)

theorem uniform_integrable {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    Integrable f (PMF.uniformOfFintype A).toMeasure :=
  Integrable.of_finite

theorem uniform_integral_eq_average {A : Type*} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    ∫ a, f a ∂(PMF.uniformOfFintype A).toMeasure =
      (∑ a, f a) / (Fintype.card A : ℝ) := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, ← Finset.mul_sum]
  ring

theorem column_integrable {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (f : ColumnAssignments cuts j → ℝ) : Integrable f (columnMeasure cuts j) :=
  uniform_integrable f

theorem fixedCount_integrable {k N K : ℕ} (cuts : Cuts k N K)
    (f : ShuffleSample cuts → ℝ) : Integrable f (fixedCountMeasure cuts) :=
  uniform_integrable f

theorem column_integral_eq_average {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (f : ColumnAssignments cuts j → ℝ) :
    ∫ a, f a ∂columnMeasure cuts j =
      (∑ a, f a) / (Fintype.card (ColumnAssignments cuts j) : ℝ) :=
  uniform_integral_eq_average f

theorem fixedCount_integral_eq_average {k N K : ℕ} (cuts : Cuts k N K)
    (f : ShuffleSample cuts → ℝ) :
    ∫ sample, f sample ∂fixedCountMeasure cuts =
      (∑ sample, f sample) / (Fintype.card (ShuffleSample cuts) : ℝ) :=
  uniform_integral_eq_average f

end TimeProfile
