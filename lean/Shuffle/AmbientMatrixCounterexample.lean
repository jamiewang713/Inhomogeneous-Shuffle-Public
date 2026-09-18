import Shuffle.AmbientCounterexample
import Shuffle.FixedColumns
import Shuffle.ConditionalHypergeometric

/-! Concrete D6 realizations of the two frozen X1 experiments. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Shuffle.X1Matrix

def middleSize (L : ℕ) (singleton : Bool) : ℕ := if singleton then 1 else L

abbrev Rows (L : ℕ) (singleton : Bool) := Fin (2 * L + middleSize L singleton)

def histogram (L : ℕ) (singleton : Bool) : Histogram (Rows L singleton) 3 where
  count a := if a = 1 then middleSize L singleton else L
  total := by
    simp [Fin.sum_univ_succ, Rows]
    omega

abbrev Experiment (L : ℕ) (singleton : Bool) (d : ℕ) :=
  Fin (d + 2) → FixedColumn (histogram L singleton)

def law (L : ℕ) (singleton : Bool) (d : ℕ) : FiniteLaw (Experiment L singleton d) := by
  convert fixedMatrixLaw (fun _ : Fin (d + 2) => histogram L singleton) using 1

variable {L d : ℕ} {singleton : Bool}

def firstColumn (ω : Experiment L singleton d) : Rows L singleton → Fin 3 :=
  (ω 0).val

def middleRows (ω : Experiment L singleton d) : Finset (Rows L singleton) :=
  Finset.univ.filter fun v => firstColumn ω v = 1

def residualRows (ω : Experiment L singleton d) : Finset (Rows L singleton) :=
  Finset.univ \ middleRows ω

def markedRows (ω : Experiment L singleton d) : Finset (Rows L singleton) :=
  Finset.univ.filter fun v => firstColumn ω v = 0

def sampleRows (ω : Experiment L singleton d) : Finset (Rows L singleton) :=
  residualRows ω

def leftCount (ω : Experiment L singleton d) : ℕ :=
  (Finset.univ.filter fun v => firstColumn ω v < 1).card

def throughCount (ω : Experiment L singleton d) : ℕ :=
  (Finset.univ.filter fun v => firstColumn ω v ≤ 1).card

def residualCount (ω : Experiment L singleton d) : ℕ :=
  (markedRows ω ∩ sampleRows ω).card

private theorem digit_card (ω : Experiment L singleton d) (a : Fin 3) :
    (Finset.univ.filter fun v => firstColumn ω v = a).card =
      (histogram L singleton).count a := by
  have h := (ω 0).property a
  simpa only [digitCount, Fintype.card_subtype, firstColumn] using h

private theorem middle_card (ω : Experiment L singleton d) :
    (middleRows ω).card = middleSize L singleton := by
  simpa [middleRows, histogram] using digit_card ω 1

private theorem marked_card (ω : Experiment L singleton d) :
    (markedRows ω).card = L := by
  simpa [markedRows, histogram] using digit_card ω 0

private theorem residual_card (ω : Experiment L singleton d) :
    (residualRows ω).card = 2 * L := by
  rw [residualRows, Finset.card_sdiff (Finset.subset_univ _), Finset.card_univ]
  rw [middle_card]
  simp only [Rows, Fintype.card_fin]
  omega

private theorem marked_subset (ω : Experiment L singleton d) :
    markedRows ω ⊆ residualRows ω := by
  intro v hv
  obtain ⟨_, hv⟩ := Finset.mem_filter.mp hv
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hm
  have hm' := (Finset.mem_filter.mp hm).2
  rw [hv] at hm'
  norm_num at hm'

private theorem endpoints (ω : Experiment L singleton d) :
    leftCount ω = L ∧ throughCount ω = L + middleSize L singleton := by
  apply fixed_column_middle_endpoints (firstColumn ω) L (middleSize L singleton)
  · exact marked_card ω
  · exact middle_card ω

/-- R1: these are the actual labelled-row counts of every legal matrix. -/
theorem counts (_hL : 1 ≤ L) (ω : Experiment L singleton d) :
    (middleRows ω).card = middleSize L singleton ∧
    (residualRows ω).card = 2 * L ∧
    (markedRows ω).card = L ∧
    (residualRows ω \ markedRows ω).card = L ∧
    leftCount ω = L ∧ throughCount ω = L + middleSize L singleton := by
  refine ⟨middle_card ω, residual_card ω, marked_card ω, ?_, endpoints ω⟩
  rw [Finset.card_sdiff (marked_subset ω), residual_card, marked_card]
  omega

/-- The sample is the entire residual population; its intersection count is
the source's first-column equal-index count. -/
theorem residual_intersection (_hL : 1 ≤ L) (ω : Experiment L singleton d) :
    markedRows ω ⊆ residualRows ω ∧ sampleRows ω = residualRows ω ∧
      residualCount ω = leftCount ω := by
  refine ⟨marked_subset ω, rfl, ?_⟩
  rw [residualCount, sampleRows, Finset.inter_eq_left.mpr (marked_subset ω),
    marked_card, (endpoints ω).1]

private theorem constant_conditional_point {Ω : Type*} [Fintype Ω]
    (p : FiniteLaw Ω) (f : Ω → ℕ) (c : ℕ) (hf : ∀ ω, f ω = c)
    (E : Ω → Prop) (hE : 0 < p.prob E) (q : ℕ) :
    p.conditionalProb E (fun ω => f ω = q) = if c = q then 1 else 0 := by
  by_cases hq : c = q
  · simp [FiniteLaw.conditionalProb, hf, hq, ne_of_gt hE]
  · simp [FiniteLaw.conditionalProb, hf, hq]

/-- R2: every positive event preserves the exact exhausted count law.
This does not assert uniformity of the remaining assignments under that event. -/
theorem conditional_left_law (_hL : 1 ≤ L) (E : Experiment L singleton d → Prop)
    (hE : 0 < (law L singleton d).prob E) :
    (law L singleton d).HasConditionalHypergeometric E leftCount (exhaustedParams L) := by
  intro q
  rw [constant_conditional_point (law L singleton d) leftCount L
    (fun ω => (endpoints ω).1) E hE q]
  rw [(exhaustedParams L).pointMass_full_draw rfl]
  rfl

theorem conditional_residual_law (hL : 1 ≤ L) (E : Experiment L singleton d → Prop)
    (hE : 0 < (law L singleton d).prob E) :
    (law L singleton d).HasConditionalHypergeometric E residualCount (exhaustedParams L) := by
  have hf : (residualCount : Experiment L singleton d → ℕ) = leftCount := by
    funext ω
    exact (residual_intersection hL ω).2.2
  rw [hf]
  exact conditional_left_law hL E hE

theorem conditional_left_mean (hL : 1 ≤ L) (E : Experiment L singleton d → Prop)
    (hE : 0 < (law L singleton d).prob E) :
    (law L singleton d).conditionalExpect E (fun ω => (leftCount ω : ℝ)) = (L : ℝ) := by
  rw [(law L singleton d).conditional_hypergeom_expect E hE leftCount
    (exhaustedParams L) (conditional_left_law hL E hE)]
  rw [← (exhaustedParams L).expect_val, exhausted_expectation]

theorem conditional_left_variance (hL : 1 ≤ L) (E : Experiment L singleton d → Prop)
    (hE : 0 < (law L singleton d).prob E) :
    ((law L singleton d).condition E hE).variance (fun ω => (leftCount ω : ℝ)) = 0 := by
  rw [(law L singleton d).conditional_hypergeom_variance E hE leftCount
    (exhaustedParams L) (conditional_left_law hL E hE)]
  rw [← (exhaustedParams L).variance_val, exhausted_variance]

theorem conditional_unit_atoms (hL : 1 ≤ L) (E : Experiment L singleton d → Prop)
    (hE : 0 < (law L singleton d).prob E) :
    (law L singleton d).conditionalProb E (fun ω => leftCount ω = L) = 1 ∧
    (law L singleton d).conditionalProb E
      (fun ω => throughCount ω = L + middleSize L singleton) = 1 := by
  constructor
  · exact (conditional_left_law hL E hE L).trans (exhausted_point_mass L)
  · simpa using constant_conditional_point (law L singleton d) throughCount
      (L + middleSize L singleton) (fun ω => (endpoints ω).2) E hE
      (L + middleSize L singleton)

/-- R3: keeping any event cannot create randomness in a fixed endpoint. -/
theorem conditional_restricted_counts (_hL : 1 ≤ L)
    (E S : Experiment L singleton d → Prop)
    (_hE : 0 < (law L singleton d).prob E) :
    (law L singleton d).conditionalProb E (fun ω => leftCount ω = L ∧ S ω) =
        (law L singleton d).conditionalProb E S ∧
    (law L singleton d).conditionalProb E
        (fun ω => throughCount ω = L + middleSize L singleton ∧ S ω) =
        (law L singleton d).conditionalProb E S := by
  have hleft : (fun ω : Experiment L singleton d => leftCount ω = L ∧ S ω) = S := by
    funext ω
    simp [(endpoints ω).1]
  have hright : (fun ω : Experiment L singleton d =>
      throughCount ω = L + middleSize L singleton ∧ S ω) = S := by
    funext ω
    simp [(endpoints ω).2]
  exact ⟨congrArg ((law L singleton d).conditionalProb E) hleft,
    congrArg ((law L singleton d).conditionalProb E) hright⟩

/-- A uniform conditional endpoint bound would force the retained event
itself to have small probability. Null reveal atoms contribute zero. -/
theorem retained_bound_forces_small_probability {Γ : Type*} [Fintype Γ]
    (hL : 1 ≤ L) (Z : Experiment L singleton d → Γ)
    (S : Experiment L singleton d → Prop) (b : ℝ)
    (hb : ∀ z, 0 < (law L singleton d).prob (fun ω => Z ω = z) →
      (law L singleton d).conditionalProb (fun ω => Z ω = z)
          (fun ω => leftCount ω = L ∧ S ω) +
      (law L singleton d).conditionalProb (fun ω => Z ω = z)
          (fun ω => throughCount ω = L + middleSize L singleton ∧ S ω) ≤ b) :
    2 * (law L singleton d).prob S ≤ b := by
  have hbound : ∀ z, 0 < (law L singleton d).prob (fun ω => Z ω = z) →
      (law L singleton d).conditionalProb (fun ω => Z ω = z) S ≤ b / 2 := by
    intro z hz
    have h := hb z hz
    obtain ⟨hl, hr⟩ := conditional_restricted_counts hL (fun ω => Z ω = z) S hz
    rw [hl, hr] at h
    linarith
  have h := (law L singleton d).total_probability_bound Z S (fun _ => b / 2) hbound
  rw [← Finset.sum_mul, (law L singleton d).sum_atom_prob Z, one_mul] at h
  linarith

/-- R4 uses the actual finite-set-valued first-column middle-row reveal. -/
theorem middle_reveal_residual_law (hL : 1 ≤ L) (R : Finset (Rows L singleton))
    (hR : 0 < (law L singleton d).prob (fun ω => middleRows ω = R)) :
    (law L singleton d).HasConditionalHypergeometric
      (fun ω => middleRows ω = R) residualCount (exhaustedParams L) :=
  conditional_residual_law hL _ hR

theorem actual_sample_exhausts (hL : 1 ≤ L) (ω : Experiment L singleton d) :
    0 < (markedRows ω).card ∧ 0 < (residualRows ω \ markedRows ω).card ∧
    1 - ((sampleRows ω).card : ℝ) / (residualRows ω).card = 0 := by
  obtain ⟨_, hr, hm, hu, _, _⟩ := counts hL ω
  refine ⟨by omega, by omega, ?_⟩
  have hpos : (0 : ℝ) < (residualRows ω).card := by
    rw [hr]
    exact_mod_cast (show 0 < 2 * L by omega)
  simp only [sampleRows, div_self (ne_of_gt hpos), sub_self]

end Shuffle.X1Matrix
