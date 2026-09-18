import Shuffle.FixedColumns
import RiffleProfiles.ModelWordMass

/-!
Frozen T07–T08: uniform fixed-column row marginals and the exact expected
row count under the existing independent-column matrix law.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace RiffleProfiles

attribute [local instance] Classical.propDecidable

private theorem digitCount_permute {N k : ℕ} (f : Fin N → Fin k)
    (e : Equiv.Perm (Fin N)) (a : Fin k) :
    Shuffle.digitCount (fun r => f (e r)) a = Shuffle.digitCount f a := by
  unfold Shuffle.digitCount
  exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))

/-- The row permutation acts on the same fixed histogram. -/
def permuteFixedColumn {N k : ℕ} (h : Shuffle.Histogram (Fin N) k)
    (e : Equiv.Perm (Fin N)) : Shuffle.FixedColumn h ≃ Shuffle.FixedColumn h where
  toFun f := ⟨fun r => f.val (e r), fun a => (digitCount_permute f.val e a).trans (f.property a)⟩
  invFun f := ⟨fun r => f.val (e.symm r),
    fun a => (digitCount_permute f.val e.symm a).trans (f.property a)⟩
  left_inv f := by
    apply Subtype.ext
    funext r
    exact congrArg f.val (e.apply_symm_apply r)
  right_inv f := by
    apply Subtype.ext
    funext r
    exact congrArg f.val (e.symm_apply_apply r)

/-- T07: invariance of every column event under a row permutation. -/
theorem columnLaw_permute_prob {N k : ℕ} (h : Shuffle.Histogram (Fin N) k)
    (e : Equiv.Perm (Fin N)) (E : Shuffle.FixedColumn h → Prop) :
    (Shuffle.columnLaw h).prob (fun f => E (permuteFixedColumn h e f)) =
      (Shuffle.columnLaw h).prob E := by
  classical
  rw [Shuffle.columnLaw, Shuffle.FiniteLaw.uniform_prob, Shuffle.FiniteLaw.uniform_prob]
  have hcard : Fintype.card {f : Shuffle.FixedColumn h // E (permuteFixedColumn h e f)} =
      Fintype.card {f : Shuffle.FixedColumn h // E f} :=
    Fintype.card_congr ((permuteFixedColumn h e).subtypeEquiv (fun _ => Iff.rfl))
  rw [hcard]

/-- Any two labelled rows have the same one-digit marginal. -/
theorem columnLaw_row_marginals_eq {N k : ℕ} (h : Shuffle.Histogram (Fin N) k)
    (r s : Fin N) (a : Fin k) :
    (Shuffle.columnLaw h).prob (fun f => f.val r = a) =
      (Shuffle.columnLaw h).prob (fun f => f.val s = a) := by
  have he := columnLaw_permute_prob h (Equiv.swap r s) (fun f => f.val r = a)
  simpa [permuteFixedColumn] using he.symm

/-- The row indicators sum to the prescribed count in every outcome. -/
theorem fixedColumn_sum_indicator {N k : ℕ} (h : Shuffle.Histogram (Fin N) k)
    (f : Shuffle.FixedColumn h) (a : Fin k) :
    (∑ r : Fin N, if f.val r = a then (1 : ℝ) else 0) = (h.count a : ℝ) := by
  classical
  calc
    (∑ r : Fin N, if f.val r = a then (1 : ℝ) else 0) =
        ((Finset.univ.filter (fun r => f.val r = a)).card : ℝ) := by simp
    _ = (Shuffle.digitCount f.val a : ℝ) := by
      rw [Shuffle.digitCount, Fintype.card_subtype]
    _ = _ := by rw [f.property]

/-- T07: every row of a uniform fixed-count column has its empirical marginal. -/
theorem columnLaw_row_marginal {N k : ℕ} (h : Shuffle.Histogram (Fin N) k)
    (hN : 0 < N) (r : Fin N) (a : Fin k) :
    (Shuffle.columnLaw h).prob (fun f => f.val r = a) = (h.count a : ℝ) / (N : ℝ) := by
  classical
  have hsum : (∑ s : Fin N, (Shuffle.columnLaw h).prob (fun f => f.val s = a)) =
      (h.count a : ℝ) := by
    unfold Shuffle.FiniteLaw.prob
    rw [Finset.sum_comm]
    calc
      _ = ∑ f : Shuffle.FixedColumn h, (Shuffle.columnLaw h).mass f *
            (∑ s : Fin N, if f.val s = a then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro f _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        split_ifs <;> simp
      _ = ∑ f : Shuffle.FixedColumn h, (Shuffle.columnLaw h).mass f * (h.count a : ℝ) := by
        simp_rw [fixedColumn_sum_indicator h]
      _ = (h.count a : ℝ) := by
        rw [← Finset.sum_mul, Shuffle.FiniteLaw.mass_sum, one_mul]
  have hconstant : (∑ s : Fin N, (Shuffle.columnLaw h).prob (fun f => f.val s = a)) =
      (N : ℝ) * (Shuffle.columnLaw h).prob (fun f => f.val r = a) := by
    calc
      _ = ∑ _s : Fin N, (Shuffle.columnLaw h).prob (fun f => f.val r = a) := by
        apply Finset.sum_congr rfl
        intro s _
        exact columnLaw_row_marginals_eq h s r a
      _ = _ := by simp
  apply (eq_div_iff (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne')).2
  simpa only [mul_comm] using hconstant.symm.trans hsum

/-- The existing model's counts give each actual fixed-column histogram. -/
def modelHistogram (D : Riffle.Model) (j : Fin D.K) : Shuffle.Histogram (Fin D.N) D.k where
  count a := D.n j.val a.val
  total := by
    simpa only [Fin.sum_univ_eq_sum_range, Fintype.card_fin] using D.sum_counts j.val j.isLt

/-- Match the dependent finite product used by the existing matrix law. -/
instance (priority := 2000) modelMatrixFintype (D : Riffle.Model) :
    Fintype (∀ j : Fin D.K, Shuffle.FixedColumn (modelHistogram D j)) := by
  letI : DecidableEq (Fin D.K) := fun a b => Classical.propDecidable (a = b)
  exact Pi.instFintype

/-- A labelled row of the dependent matrix is the existing finite full-word type. -/
def modelRowWord (D : Riffle.Model)
    (matrix : ∀ j : Fin D.K, Shuffle.FixedColumn (modelHistogram D j))
    (r : Fin D.N) : Riffle.FullIndex D := fun j => (matrix j).val r

/-- T08: the full-word marginal is the product of the actual column proportions. -/
theorem model_rowWord_probability (D : Riffle.Model) (r : Fin D.N)
    (ω : Riffle.FullIndex D) :
    (Shuffle.fixedMatrixLaw (modelHistogram D)).prob
      (fun matrix => modelRowWord D matrix r = ω) = wordWeight (modelDigitProb D) ω := by
  have hrectangle :
      (fun matrix : ∀ j : Fin D.K, Shuffle.FixedColumn (modelHistogram D j) =>
        modelRowWord D matrix r = ω) =
      (fun matrix => ∀ j : Fin D.K, (matrix j).val r = ω j) := by
    funext matrix
    exact propext ⟨congrFun, funext⟩
  rw [hrectangle, Shuffle.fixedMatrixLaw]
  rw [Shuffle.FiniteLaw.product_prob_rectangle
    (fun j : Fin D.K => Shuffle.columnLaw (modelHistogram D j))
    (fun j f => f.val r = ω j)]
  unfold wordWeight
  apply Finset.prod_congr rfl
  intro j _
  rw [columnLaw_row_marginal (modelHistogram D j)
    (lt_trans Nat.zero_lt_one D.one_lt_N) r (ω j)]
  simp [modelHistogram, modelDigitProb, Riffle.prob]

private theorem model_rowWord_event_probability (D : Riffle.Model)
    (r : Fin D.N) (E : Set Riffle.Word) :
    (Shuffle.fixedMatrixLaw (modelHistogram D)).prob
      (fun matrix => Riffle.fullList (modelRowWord D matrix r) ∈ E) =
      ∑ ω : Riffle.FullIndex D,
        if Riffle.fullList ω ∈ E then wordWeight (modelDigitProb D) ω else 0 := by
  classical
  rw [← Shuffle.FiniteLaw.map_prob (Shuffle.fixedMatrixLaw (modelHistogram D))
    (fun matrix => modelRowWord D matrix r) (fun ω => Riffle.fullList ω ∈ E)]
  unfold Shuffle.FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro ω _
  have hm :
      ((Shuffle.fixedMatrixLaw (modelHistogram D)).map
        (fun matrix => modelRowWord D matrix r)).mass ω = wordWeight (modelDigitProb D) ω :=
    model_rowWord_probability D r ω
  rw [hm]

/-- T08: the actual expected number of labelled rows equals the model functional. -/
theorem model_expected_row_count (D : Riffle.Model) (E : Set Riffle.Word) :
    (Shuffle.fixedMatrixLaw (modelHistogram D)).expect
      (fun matrix => ((Finset.univ.filter (fun r : Fin D.N =>
        Riffle.fullList (modelRowWord D matrix r) ∈ E)).card : ℝ)) =
      (Riffle.expectedCount D E : ℝ) := by
  classical
  rw [model_expectedCount_eq_wordMass]
  calc
    _ = ∑ r : Fin D.N, (Shuffle.fixedMatrixLaw (modelHistogram D)).prob
        (fun matrix => Riffle.fullList (modelRowWord D matrix r) ∈ E) := by
      unfold Shuffle.FiniteLaw.expect Shuffle.FiniteLaw.prob
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro matrix _
      calc
        _ = (Shuffle.fixedMatrixLaw (modelHistogram D)).mass matrix *
            (∑ r : Fin D.N,
              if Riffle.fullList (modelRowWord D matrix r) ∈ E then (1 : ℝ) else 0) := by
          congr 1
          simp
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          split_ifs <;> simp
    _ = (D.N : ℝ) * ∑ ω : Riffle.FullIndex D,
        if Riffle.fullList ω ∈ E then wordWeight (modelDigitProb D) ω else 0 := by
      simp_rw [model_rowWord_event_probability D]
      simp

end RiffleProfiles
