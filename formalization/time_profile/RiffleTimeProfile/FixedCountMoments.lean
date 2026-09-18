import RiffleTimeProfile.FixedCountModel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TimeProfile

private theorem average_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ j, Fintype (α j)] (f : ∀ j, α j → ℝ) :
    (∑ s : ∀ j, α j, ∏ j, f j (s j)) / (Fintype.card (∀ j, α j) : ℝ) =
      ∏ j, ((∑ a : α j, f j a) / (Fintype.card (α j) : ℝ)) := by
  rw [← Fintype.prod_sum, Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

private theorem average_sum {α β : Type*} [Fintype α] [Fintype β] (f : β → α → ℝ) :
    (∑ a, ∑ b, f b a) / (Fintype.card α : ℝ) =
      ∑ b, (∑ a, f b a) / (Fintype.card α : ℝ) := by
  rw [Finset.sum_comm, Finset.sum_div]

private theorem average_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) :
    (∑ a, f (e a)) / (Fintype.card α : ℝ) = (∑ b, f b) / (Fintype.card β : ℝ) := by
  rw [Fintype.card_congr e]
  congr 1
  exact Equiv.sum_comp e f

private theorem average_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    (∑ _a : α, c) / (Fintype.card α : ℝ) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ c hc

private theorem card_filter_perm {α β : Type*} [Fintype α] [DecidableEq β]
    (sigma : Equiv.Perm α) (a : α → β) (l : β) :
    (Finset.univ.filter (fun i => a (sigma i) = l)).card =
      (Finset.univ.filter (fun i => a i = l)).card := by
  classical
  apply Finset.card_bij (fun i _ => sigma i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
  · intro i _ j _ hij
    exact sigma.injective hij
  · intro i hi
    refine ⟨sigma.symm i, ?_, sigma.apply_symm_apply i⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, sigma.apply_symm_apply] using hi

private theorem sum_by_digit {k N : ℕ} (a : Fin N → Fin k) (g : Fin k → ℝ) :
    (∑ i, g (a i)) =
      ∑ l, ((Finset.univ.filter (fun i => a i = l)).card : ℝ) * g l := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul] using
    (Finset.sum_fiberwise' Finset.univ a g).symm

/-- Relabelling rows permutes the exact fixed-count assignment space. -/
def columnReindex {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (sigma : Equiv.Perm (Fin N)) : ColumnAssignments cuts j ≃ ColumnAssignments cuts j where
  toFun a := ⟨fun i => a.val (sigma i), by
    intro l
    exact (card_filter_perm sigma a.val l).trans (a.property l)⟩
  invFun a := ⟨fun i => a.val (sigma.symm i), by
    intro l
    exact (card_filter_perm sigma.symm a.val l).trans (a.property l)⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    exact congrArg a.val (sigma.apply_symm_apply i)
  right_inv a := by
    apply Subtype.ext
    funext i
    exact congrArg a.val (sigma.symm_apply_apply i)

@[simp] theorem columnReindex_entry {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (sigma : Equiv.Perm (Fin N)) (a : ColumnAssignments cuts j) (i : Fin N) :
    (columnReindex cuts j sigma a).val i = a.val (sigma i) := rfl

theorem uniform_integral_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (e : α ≃ β) (f : β → ℝ) :
    (∫ a, f (e a) ∂(PMF.uniformOfFintype α).toMeasure) =
      ∫ b, f b ∂(PMF.uniformOfFintype β).toMeasure := by
  rw [uniform_integral_eq_average, uniform_integral_eq_average]
  exact average_equiv e f

theorem column_integral_reindex {k N K : ℕ} (cuts : Cuts k N K) (j : Fin K)
    (sigma : Equiv.Perm (Fin N)) (f : ColumnAssignments cuts j → ℝ) :
    (∫ a, f (columnReindex cuts j sigma a) ∂columnMeasure cuts j) =
      ∫ a, f a ∂columnMeasure cuts j :=
  uniform_integral_equiv (columnReindex cuts j sigma) f

theorem column_sum_eval {k N K : ℕ} {cuts : Cuts k N K} {j : Fin K}
    (a : ColumnAssignments cuts j) (g : Fin k → ℝ) :
    (∑ i, g (a.val i)) = ∑ l, (cuts.count j l : ℝ) * g l := by
  rw [sum_by_digit]
  simp_rw [columnAssignments_count]

/-- A fixed labelled row has the prescribed marginal, proved from row symmetry. -/
theorem column_marginal {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (j : Fin K) (i : Fin N) (g : Fin k → ℝ) :
    (∫ a, g (a.val i) ∂columnMeasure cuts j) =
      ∑ l, prob (cuts.profile hN j) l * g l := by
  have hequal (q : Fin N) :
      (∫ a, g (a.val q) ∂columnMeasure cuts j) =
        ∫ a, g (a.val i) ∂columnMeasure cuts j := by
    have h := column_integral_reindex cuts j (Equiv.swap i q) (fun a => g (a.val i))
    simpa only [columnReindex_entry, Equiv.swap_apply_left] using h
  have hweighted : (∫ a, g (a.val i) ∂columnMeasure cuts j) * (N : ℝ) =
      ∑ l, (cuts.count j l : ℝ) * g l := by
    calc
      _ = ∑ q : Fin N, ∫ a, g (a.val q) ∂columnMeasure cuts j := by
        simp_rw [hequal]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ = ∫ a, ∑ q : Fin N, g (a.val q) ∂columnMeasure cuts j := by
        simp_rw [column_integral_eq_average]
        exact (average_sum (fun q (a : ColumnAssignments cuts j) => g (a.val q))).symm
      _ = ∑ l, (cuts.count j l : ℝ) * g l := by
        simp_rw [column_sum_eval]
        rw [column_integral_eq_average]
        exact average_const _
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    _ = (∑ l, (cuts.count j l : ℝ) * g l) / (N : ℝ) := (eq_div_iff hNreal).mpr hweighted
    _ = ∑ l, prob (cuts.profile hN j) l * g l := by
      simp only [Cuts.profile_prob, div_mul_eq_mul_div, Finset.sum_div]

/-- The uniform fixed-count matrix law factors across its column coordinates. -/
theorem column_product_factorization {k N K : ℕ} (cuts : Cuts k N K)
    (F : ∀ j : Fin K, ColumnAssignments cuts j → ℝ) :
    (∫ sample, ∏ j, F j (sample j) ∂fixedCountMeasure cuts) =
      ∏ j, ∫ a, F j a ∂columnMeasure cuts j := by
  rw [fixedCount_integral_eq_average]
  simp_rw [column_integral_eq_average]
  exact average_prod_pi F

/-- The labelled-row marginal is unchanged on the full product sample space. -/
theorem sample_marginal {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (j : Fin K) (i : Fin N) (g : Fin k → ℝ) :
    (∫ sample, g (sampleEntry sample i j) ∂fixedCountMeasure cuts) =
      ∑ l, prob (cuts.profile hN j) l * g l := by
  have h := column_product_factorization cuts
    (fun h a => if h = j then g (a.val i) else 1)
  have hcolumn (h : Fin K) :
      (∫ a, (if h = j then g (a.val i) else 1) ∂columnMeasure cuts h) =
        if h = j then (∫ a, g (a.val i) ∂columnMeasure cuts h) else 1 := by
    by_cases hh : h = j
    · simp only [hh, if_true]
    · simp [hh]
  simp_rw [hcolumn] at h
  simp only [Fintype.prod_ite_eq'] at h
  exact h.trans (column_marginal cuts hN j i g)

theorem column_digit_probability {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (j : Fin K) (i : Fin N) (l : Fin k) :
    (columnMeasure cuts j).real {a | a.val i = l} = prob (cuts.profile hN j) l := by
  classical
  have h := column_marginal cuts hN j i (fun q => if q = l then (1 : ℝ) else 0)
  have hs : MeasurableSet {a : ColumnAssignments cuts j | a.val i = l} :=
    (Set.toFinite _).measurableSet
  have hind := integral_indicator_one (μ := columnMeasure cuts j) hs
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] at hind
  rw [hind] at h
  simpa only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] using h

theorem sample_digit_probability {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (j : Fin K) (i : Fin N) (l : Fin k) :
    (fixedCountMeasure cuts).real {sample | sampleEntry sample i j = l} =
      prob (cuts.profile hN j) l := by
  classical
  have h := sample_marginal cuts hN j i (fun q => if q = l then (1 : ℝ) else 0)
  have hs : MeasurableSet {sample : ShuffleSample cuts | sampleEntry sample i j = l} :=
    (Set.toFinite _).measurableSet
  have hind := integral_indicator_one (μ := fixedCountMeasure cuts) hs
  simp only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply] at hind
  rw [hind] at h
  simpa only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] using h

/-- The exact expected number of labelled rows in an arbitrary digit box. -/
theorem expected_box_count {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (A : Fin K → Finset (Fin k)) :
    (∫ sample : ShuffleSample cuts, ((boxRows A sample).card : ℝ) ∂fixedCountMeasure cuts) =
      (N : ℝ) * ∏ j, ∑ l ∈ A j, prob (cuts.profile hN j) l := by
  have hcount (sample : ShuffleSample cuts) :
      ((boxRows A sample).card : ℝ) =
        ∑ i : Fin N, ∏ j : Fin K, (if sampleEntry sample i j ∈ A j then (1 : ℝ) else 0) := by
    have hbox : boxRows A sample = Finset.univ.filter
        (fun i : Fin N => ∀ j : Fin K, sampleEntry sample i j ∈ A j) :=
      Finset.filter_congr_decidable Finset.univ
        (fun i : Fin N => ∀ j : Fin K, sampleEntry sample i j ∈ A j)
        (fun i => Classical.propDecidable _)
    rw [hbox]
    calc
      _ = ∑ i : Fin N, (if ∀ j : Fin K, sampleEntry sample i j ∈ A j then (1 : ℝ) else 0) :=
        Finset.natCast_card_filter (R := ℝ)
          (fun i : Fin N => ∀ j : Fin K, sampleEntry sample i j ∈ A j) Finset.univ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Fintype.prod_boole]
        by_cases hi : ∀ j : Fin K, sampleEntry sample i j ∈ A j
        · simp only [if_pos hi]
        · simp only [if_neg hi]
  have hrow (i : Fin N) :
      (∫ sample, ∏ j : Fin K, (if sampleEntry sample i j ∈ A j then (1 : ℝ) else 0)
        ∂fixedCountMeasure cuts) = ∏ j, ∑ l ∈ A j, prob (cuts.profile hN j) l := by
    change (∫ sample, ∏ j : Fin K, (if (sample j).val i ∈ A j then (1 : ℝ) else 0)
        ∂fixedCountMeasure cuts) = _
    apply (column_product_factorization cuts (fun j (a : ColumnAssignments cuts j) =>
      if a.val i ∈ A j then (1 : ℝ) else 0)).trans
    apply Finset.prod_congr rfl
    intro j _
    have h := column_marginal cuts hN j i (fun l => if l ∈ A j then (1 : ℝ) else 0)
    simpa only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using h
  calc
    _ = ∫ sample, ∑ i : Fin N, ∏ j : Fin K,
        (if sampleEntry sample i j ∈ A j then (1 : ℝ) else 0) ∂fixedCountMeasure cuts := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hcount
    _ = ∑ i : Fin N, ∫ sample, ∏ j : Fin K,
        (if sampleEntry sample i j ∈ A j then (1 : ℝ) else 0) ∂fixedCountMeasure cuts := by
      apply integral_finsetSum
      intro i _
      exact fixedCount_integrable cuts _
    _ = ∑ _i : Fin N, ∏ j, ∑ l ∈ A j, prob (cuts.profile hN j) l := by simp_rw [hrow]
    _ = (N : ℝ) * ∏ j, ∑ l ∈ A j, prob (cuts.profile hN j) l := by simp

end TimeProfile
