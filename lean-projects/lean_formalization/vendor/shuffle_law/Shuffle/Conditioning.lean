import Shuffle.FiniteLaw

open scoped BigOperators

namespace Shuffle
namespace FiniteLaw

variable {Ω Γ Δ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ]

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The literal conditional probability quotient. A null denominator is not
asserted to define a probability law. -/
def conditionalProb (p : FiniteLaw Ω) (E B : Ω → Prop) : ℝ :=
  p.prob (fun ω => B ω ∧ E ω) / p.prob E

/-- The literal conditional expectation quotient, used in finite tower sums. -/
def conditionalExpect (p : FiniteLaw Ω) (E : Ω → Prop) (f : Ω → ℝ) : ℝ := by
  classical
  exact (∑ ω, if E ω then p.mass ω * f ω else 0) / p.prob E

/-- Conditioning is a finite law only on a strictly positive event. -/
def condition (p : FiniteLaw Ω) (E : Ω → Prop) (hE : 0 < p.prob E) :
    FiniteLaw Ω := by
  classical
  refine ⟨(fun ω => (if E ω then p.mass ω else 0) / p.prob E), ?_, ?_⟩
  · intro ω
    apply div_nonneg _ (le_of_lt hE)
    split_ifs
    · exact p.mass_nonneg ω
    · exact le_rfl
  · rw [← Finset.sum_div]
    exact div_self (ne_of_gt hE)

@[simp] theorem condition_mass (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (ω : Ω) :
    (p.condition E hE).mass ω = (if E ω then p.mass ω else 0) / p.prob E := by
  classical
  rfl

theorem condition_prob (p : FiniteLaw Ω) (E B : Ω → Prop)
    (hE : 0 < p.prob E) :
    (p.condition E hE).prob B = p.conditionalProb E B := by
  classical
  unfold conditionalProb
  unfold prob
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω <;> by_cases hb : B ω <;> simp [condition_mass, he, hb, prob]

theorem condition_expect (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (f : Ω → ℝ) :
    (p.condition E hE).expect f = p.conditionalExpect E f := by
  classical
  unfold expect conditionalExpect
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : E ω <;> simp [condition_mass, he, div_mul_eq_mul_div]

/-- Every point in a null event has zero mass. This justifies omitting null
reveal atoms without inventing conditional laws on them. -/
theorem mass_eq_zero_of_prob_eq_zero (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : p.prob E = 0) {ω : Ω} (hω : E ω) : p.mass ω = 0 := by
  classical
  have hle : p.mass ω ≤ p.prob E := by
    unfold prob
    simpa only [if_pos hω] using
      (Finset.single_le_sum
        (f := fun a => if E a then p.mass a else 0)
        (fun a (_ : a ∈ Finset.univ) => by
          by_cases ha : E a
          · simp only [if_pos ha]
            exact p.mass_nonneg a
          · simp only [if_neg ha, le_refl])
        (Finset.mem_univ ω))
  exact le_antisymm (hE ▸ hle) (p.mass_nonneg ω)

theorem prob_inter_eq_zero_of_prob_eq_zero (p : FiniteLaw Ω)
    (E B : Ω → Prop) (hE : p.prob E = 0) :
    p.prob (fun ω => B ω ∧ E ω) = 0 := by
  classical
  unfold prob
  apply Finset.sum_eq_zero
  intro ω _
  by_cases h : B ω ∧ E ω
  · simp only [if_pos h]
    exact p.mass_eq_zero_of_prob_eq_zero E hE h.2
  · simp only [if_neg h]

theorem weighted_conditionalProb (p : FiniteLaw Ω) (E B : Ω → Prop) :
    p.prob E * p.conditionalProb E B = p.prob (fun ω => B ω ∧ E ω) := by
  unfold conditionalProb
  by_cases hE : p.prob E = 0
  · rw [hE, p.prob_inter_eq_zero_of_prob_eq_zero E B hE]
    simp
  · exact mul_div_cancel₀ _ hE

theorem weighted_conditionalExpect (p : FiniteLaw Ω) (E : Ω → Prop)
    (f : Ω → ℝ) :
    p.prob E * p.conditionalExpect E f =
      ∑ ω, if E ω then p.mass ω * f ω else 0 := by
  classical
  unfold conditionalExpect
  by_cases hE : p.prob E = 0
  · rw [hE]
    simp only [zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro ω _
    by_cases he : E ω
    · simp [he, p.mass_eq_zero_of_prob_eq_zero E hE he]
    · simp [he]
  · exact mul_div_cancel₀ _ hE

/-- F4: total probability, with null-atom terms equal to zero. -/
theorem total_probability (p : FiniteLaw Ω) (Z : Ω → Γ) (B : Ω → Prop) :
    p.prob B =
      ∑ z, p.prob (fun ω => Z ω = z) *
        p.conditionalProb (fun ω => Z ω = z) B := by
  classical
  simp_rw [weighted_conditionalProb]
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hb : B ω <;> simp [hb]

/-- F4: total expectation, including arbitrary real-valued functions. -/
theorem total_expectation (p : FiniteLaw Ω) (Z : Ω → Γ) (f : Ω → ℝ) :
    p.expect f =
      ∑ z, p.prob (fun ω => Z ω = z) *
        p.conditionalExpect (fun ω => Z ω = z) f := by
  classical
  simp_rw [weighted_conditionalExpect]
  unfold expect
  rw [Finset.sum_comm]
  simp

theorem conditionalProb_nonneg (p : FiniteLaw Ω) (E B : Ω → Prop) :
    0 ≤ p.conditionalProb E B := by
  exact div_nonneg (p.prob_nonneg _) (p.prob_nonneg _)

theorem conditionalProb_mono_on (p : FiniteLaw Ω) (E B D : Ω → Prop)
    (h : ∀ ω, E ω → B ω → D ω) :
    p.conditionalProb E B ≤ p.conditionalProb E D := by
  unfold conditionalProb
  apply div_le_div_of_nonneg_right _ (p.prob_nonneg _)
  exact p.prob_mono (fun ω hω => ⟨h ω hω.2 hω.1, hω.2⟩)

theorem total_probability_bound (p : FiniteLaw Ω) (Z : Ω → Γ)
    (B : Ω → Prop) (b : Γ → ℝ)
    (hb : ∀ z, 0 < p.prob (fun ω => Z ω = z) →
      p.conditionalProb (fun ω => Z ω = z) B ≤ b z) :
    p.prob B ≤ ∑ z, p.prob (fun ω => Z ω = z) * b z := by
  rw [p.total_probability Z B]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : 0 < p.prob (fun ω => Z ω = z)
  · exact mul_le_mul_of_nonneg_left (hb z hz) (p.prob_nonneg _)
  · have hzero : p.prob (fun ω => Z ω = z) = 0 :=
      le_antisymm (le_of_not_gt hz) (p.prob_nonneg _)
    simp [hzero]

/-- F4: the weights on a positive coarse atom are conditional weights. -/
theorem coarse_total_probability (p : FiniteLaw Ω) (Z : Ω → Γ)
    (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ ω, U ω = g (Z ω))
    (u : Δ) (_hu : 0 < p.prob (fun ω => U ω = u)) (B : Ω → Prop) :
    p.conditionalProb (fun ω => U ω = u) B =
      ∑ z, p.conditionalProb (fun ω => U ω = u) (fun ω => Z ω = z) *
        p.conditionalProb (fun ω => Z ω = z) B := by
  classical
  unfold conditionalProb
  rw [p.total_probability Z (fun ω => B ω ∧ U ω = u), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro z _
  unfold conditionalProb
  by_cases hzu : g z = u
  · have hsub : ∀ ω, Z ω = z → U ω = u := by
      intro ω hω
      rw [hU ω, hω, hzu]
    have h1 : (fun ω => (B ω ∧ U ω = u) ∧ Z ω = z) =
        (fun ω => B ω ∧ Z ω = z) := by
      funext ω
      apply propext
      constructor
      · intro h
        exact ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.1, hsub ω h.2⟩, h.2⟩
    have h2 : (fun ω => Z ω = z ∧ U ω = u) = (fun ω => Z ω = z) := by
      funext ω
      apply propext
      exact ⟨And.left, fun h => ⟨h, hsub ω h⟩⟩
    rw [h1, h2]
    ring
  · have hempty : ∀ ω, ¬(Z ω = z ∧ U ω = u) := by
      intro ω h
      apply hzu
      simpa only [hU ω, h.1] using h.2
    have h1 : (fun ω => (B ω ∧ U ω = u) ∧ Z ω = z) = (fun _ => False) := by
      funext ω
      apply propext
      exact ⟨fun h => hempty ω ⟨h.2, h.1.2⟩, False.elim⟩
    have h2 : (fun ω => Z ω = z ∧ U ω = u) = (fun _ => False) := by
      funext ω
      exact propext ⟨hempty ω, False.elim⟩
    rw [h1, h2, p.prob_false]
    simp

theorem coarse_total_probability_bound (p : FiniteLaw Ω) (Z : Ω → Γ)
    (U : Ω → Δ) (g : Γ → Δ) (hU : ∀ ω, U ω = g (Z ω))
    (u : Δ) (hu : 0 < p.prob (fun ω => U ω = u))
    (B : Ω → Prop) (b : Γ → ℝ)
    (hb : ∀ z, 0 < p.prob (fun ω => Z ω = z) →
      p.conditionalProb (fun ω => Z ω = z) B ≤ b z) :
    p.conditionalProb (fun ω => U ω = u) B ≤
      ∑ z, p.conditionalProb (fun ω => U ω = u) (fun ω => Z ω = z) * b z := by
  rw [p.coarse_total_probability Z U g hU u hu B]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : 0 < p.prob (fun ω => Z ω = z)
  · exact mul_le_mul_of_nonneg_left (hb z hz) (p.conditionalProb_nonneg _ _)
  · have hzero : p.prob (fun ω => Z ω = z) = 0 :=
      le_antisymm (le_of_not_gt hz) (p.prob_nonneg _)
    have hinter : p.prob (fun ω => Z ω = z ∧ U ω = u) = 0 := by
      apply le_antisymm _ (p.prob_nonneg _)
      calc
        p.prob (fun ω => Z ω = z ∧ U ω = u) ≤ p.prob (fun ω => Z ω = z) :=
          p.prob_mono (fun _ h => h.1)
        _ = 0 := hzero
    simp only [conditionalProb, hinter, zero_div, zero_mul, le_refl]

theorem sum_atom_prob (p : FiniteLaw Ω) (Z : Ω → Γ) :
    ∑ z, p.prob (fun ω => Z ω = z) = 1 := by
  classical
  unfold prob
  rw [Finset.sum_comm]
  simpa using p.mass_sum

theorem sum_conditional_atom_prob (p : FiniteLaw Ω) (E : Ω → Prop)
    (hE : 0 < p.prob E) (Z : Ω → Γ) :
    ∑ z, p.conditionalProb E (fun ω => Z ω = z) = 1 := by
  simp_rw [← p.condition_prob E _ hE]
  exact (p.condition E hE).sum_atom_prob Z

/-- F5: an event may be contained in a good reveal set without itself being
measurable in the reveal. Conditional point-mass bounds still descend. -/
theorem shifted_anticoncentration_transfer (p : FiniteLaw Ω)
    (Z : Ω → Γ) (U : Ω → Δ) (g : Γ → Δ)
    (hU : ∀ ω, U ω = g (Z ω)) (A : Γ → ℤ) (Y : Ω → ℕ)
    (H : Γ → Prop) (S : Ω → Prop) (hS : ∀ ω, S ω → H (Z ω))
    (b : ℝ) (hb : 0 ≤ b)
    (hpoint : ∀ z, 0 < p.prob (fun ω => Z ω = z) → H z → ∀ q : ℕ,
      p.conditionalProb (fun ω => Z ω = z) (fun ω => Y ω = q) ≤ b)
    (u : Δ) (hu : 0 < p.prob (fun ω => U ω = u)) (j : ℤ) :
    p.conditionalProb (fun ω => U ω = u)
      (fun ω => A (Z ω) + (Y ω : ℤ) = j ∧ S ω) ≤ b := by
  classical
  have hfine : ∀ z, 0 < p.prob (fun ω => Z ω = z) →
      p.conditionalProb (fun ω => Z ω = z)
        (fun ω => A (Z ω) + (Y ω : ℤ) = j ∧ S ω) ≤ b := by
    intro z hz
    by_cases hzH : H z
    · by_cases hex : ∃ q : ℕ, A z + (q : ℤ) = j
      · obtain ⟨q, hq⟩ := hex
        apply le_trans (p.conditionalProb_mono_on _ _ (fun ω => Y ω = q) ?_)
          (hpoint z hz hzH q)
        intro ω hω hj
        apply Int.ofNat.inj
        have hleft : A z + (Y ω : ℤ) = j := by simpa only [hω] using hj.1
        exact add_left_cancel (hleft.trans hq.symm)
      · have hle : p.conditionalProb (fun ω => Z ω = z)
            (fun ω => A (Z ω) + (Y ω : ℤ) = j ∧ S ω) ≤
            p.conditionalProb (fun ω => Z ω = z) (fun _ => False) := by
          apply p.conditionalProb_mono_on
          intro ω hω hj
          apply hex
          exact ⟨Y ω, by simpa only [hω] using hj.1⟩
        exact le_trans hle (by simpa [conditionalProb, prob] using hb)
    · have hle : p.conditionalProb (fun ω => Z ω = z)
          (fun ω => A (Z ω) + (Y ω : ℤ) = j ∧ S ω) ≤
          p.conditionalProb (fun ω => Z ω = z) (fun _ => False) := by
        apply p.conditionalProb_mono_on
        intro ω hω hj
        exact hzH (hω ▸ hS ω hj.2)
      exact le_trans hle (by simpa [conditionalProb, prob] using hb)
  have hbound := p.coarse_total_probability_bound Z U g hU u hu
    (fun ω => A (Z ω) + (Y ω : ℤ) = j ∧ S ω) (fun _ => b) hfine
  rw [← Finset.sum_mul, p.sum_conditional_atom_prob _ hu Z, one_mul] at hbound
  exact hbound

/-- Literal finite pushforward, as specified by D2. -/
def map (p : FiniteLaw Ω) (f : Ω → Γ) : FiniteLaw Γ where
  mass z := p.prob (fun ω => f ω = z)
  mass_nonneg _ := p.prob_nonneg _
  mass_sum := p.sum_atom_prob f

@[simp] theorem map_prob (p : FiniteLaw Ω) (f : Ω → Γ) (B : Γ → Prop) :
    (p.map f).prob B = p.prob (fun ω => B (f ω)) := by
  classical
  unfold prob map
  simp only
  calc
    _ = ∑ z, ∑ ω, if f ω = z then (if B (f ω) then p.mass ω else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hb : B z
      · simp only [hb, if_true]
        apply Finset.sum_congr rfl
        intro ω _
        by_cases hz : f ω = z <;> simp [hz, hb]
      · simp only [hb, if_false]
        symm
        apply Finset.sum_eq_zero
        intro ω _
        by_cases hz : f ω = z <;> simp [hz, hb]
    _ = _ := by rw [Finset.sum_comm]; simp

@[simp] theorem map_expect (p : FiniteLaw Ω) (f : Ω → Γ) (h : Γ → ℝ) :
    (p.map f).expect h = p.expect (fun ω => h (f ω)) := by
  classical
  unfold expect map prob
  simp only
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

@[simp] theorem map_variance (p : FiniteLaw Ω) (f : Ω → Γ) (h : Γ → ℝ) :
    (p.map f).variance h = p.variance (fun ω => h (f ω)) := by
  simp only [variance, map_expect]

/-- Uniform law on a nonempty finite outcome type. -/
def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := 1 / (Fintype.card Ω : ℝ)
  mass_nonneg _ := div_nonneg zero_le_one (Nat.cast_nonneg _)
  mass_sum := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
    exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem uniform_prob [Nonempty Ω] (E : Ω → Prop) :
    (uniform Ω).prob E =
      (Fintype.card {ω : Ω // E ω} : ℝ) / (Fintype.card Ω : ℝ) := by
  classical
  unfold prob uniform
  simp only
  rw [Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

theorem uniform_prob_pos_iff [Nonempty Ω] (E : Ω → Prop) :
    0 < (uniform Ω).prob E ↔ ∃ ω, E ω := by
  classical
  rw [uniform_prob]
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  rw [div_pos_iff_of_pos_right hcard, Nat.cast_pos, Fintype.card_pos_iff]
  exact ⟨fun ⟨ω, hω⟩ => ⟨ω, hω⟩, fun ⟨ω, hω⟩ => ⟨⟨ω, hω⟩⟩⟩

/-- F3: the conditional uniform mass is exactly the reciprocal of the
nonempty fibre's size, and zero off that fibre. -/
theorem condition_uniform_mass [Nonempty Ω] (E : Ω → Prop)
    (hE : 0 < (uniform Ω).prob E) (ω : Ω) :
    ((uniform Ω).condition E hE).mass ω =
      if E ω then 1 / (Fintype.card {ω : Ω // E ω} : ℝ) else 0 := by
  classical
  rw [condition_mass, uniform_prob]
  by_cases hω : E ω
  · simp only [hω, if_true, uniform]
    exact div_div_div_cancel_right₀
      (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)) _ _
  · simp only [hω, if_false, zero_div]

theorem uniform_conditionalProb [Nonempty Ω] (E B : Ω → Prop) :
    (uniform Ω).conditionalProb E B =
      (Fintype.card {ω : Ω // B ω ∧ E ω} : ℝ) /
        (Fintype.card {ω : Ω // E ω} : ℝ) := by
  unfold conditionalProb
  rw [uniform_prob, uniform_prob]
  convert div_div_div_cancel_right₀ (c := (Fintype.card Ω : ℝ))
    (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0))
    (Fintype.card {ω : Ω // B ω ∧ E ω} : ℝ) (Fintype.card {ω : Ω // E ω} : ℝ)
    using 1 <;> congr 3
  exact congrArg (@Fintype.card {ω : Ω // B ω ∧ E ω}) (Subsingleton.elim _ _)

/-- Uniformity can be transported through a bijection from the conditioning
fibre. This is the generic finite interface used by residual sampling. -/
theorem uniform_conditional_point_of_fiber_equiv [Nonempty Ω]
    (E : Ω → Prop) (_hE : 0 < (uniform Ω).prob E) (f : Ω → Γ)
    (e : {ω : Ω // E ω} ≃ Γ)
    (hf : ∀ (ω : Ω) (h : E ω), f ω = e ⟨ω, h⟩) (z : Γ) :
    (uniform Ω).conditionalProb E (fun ω => f ω = z) =
      1 / (Fintype.card Γ : ℝ) := by
  classical
  have hsingle : Fintype.card {ω : Ω // f ω = z ∧ E ω} = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨(e.symm z).val, ?_⟩, ?_⟩
    · exact ⟨(hf _ (e.symm z).property).trans (e.apply_symm_apply z),
        (e.symm z).property⟩
    · intro ω
      apply Subtype.ext
      have heq : (⟨ω.val, ω.property.2⟩ : {ω : Ω // E ω}) = e.symm z := by
        apply e.injective
        rw [← hf ω.val ω.property.2, ω.property.1, e.apply_symm_apply]
      exact congrArg (fun x : {ω : Ω // E ω} => x.val) heq
  rw [uniform_conditionalProb, hsingle, Fintype.card_congr e]
  simp

/-- C4's finite exact-law interface transfers every event, without replacing
the equality of laws by a moment hypothesis. -/
theorem prob_eq_of_map_eq (p : FiniteLaw Ω) (X : Ω → Γ) (q : FiniteLaw Γ)
    (hlaw : p.map X = q) (B : Γ → Prop) :
    p.prob (fun ω => B (X ω)) = q.prob B := by
  rw [← map_prob, hlaw]

theorem expect_eq_of_map_eq (p : FiniteLaw Ω) (X : Ω → Γ) (q : FiniteLaw Γ)
    (hlaw : p.map X = q) (f : Γ → ℝ) :
    p.expect (fun ω => f (X ω)) = q.expect f := by
  rw [← map_expect, hlaw]

theorem variance_eq_of_map_eq (p : FiniteLaw Ω) (X : Ω → Γ) (q : FiniteLaw Γ)
    (hlaw : p.map X = q) (f : Γ → ℝ) :
    p.variance (fun ω => f (X ω)) = q.variance f := by
  rw [← map_variance, hlaw]

theorem conditional_prob_eq_of_map_eq (p : FiniteLaw Ω)
    (E : Ω → Prop) (hE : 0 < p.prob E) (X : Ω → Γ) (q : FiniteLaw Γ)
    (hlaw : (p.condition E hE).map X = q) (B : Γ → Prop) :
    p.conditionalProb E (fun ω => B (X ω)) = q.prob B := by
  rw [← condition_prob]
  exact (p.condition E hE).prob_eq_of_map_eq X q hlaw B

theorem conditional_expect_eq_of_map_eq (p : FiniteLaw Ω)
    (E : Ω → Prop) (hE : 0 < p.prob E) (X : Ω → Γ) (q : FiniteLaw Γ)
    (hlaw : (p.condition E hE).map X = q) (f : Γ → ℝ) :
    p.conditionalExpect E (fun ω => f (X ω)) = q.expect f := by
  rw [← condition_expect]
  exact (p.condition E hE).expect_eq_of_map_eq X q hlaw f

/-- Exact natural-valued count laws transfer arbitrary moments. Support is
deduced from the law equality; no pointwise bound on the count is assumed. -/
theorem expect_eq_of_count_law (p : FiniteLaw Ω) (Y : Ω → ℕ) (n : ℕ)
    (q : FiniteLaw (Fin (n + 1)))
    (hlaw : ∀ a : ℕ, p.prob (fun ω => Y ω = a) =
      q.prob (fun x => x.val = a)) (f : ℕ → ℝ) :
    p.expect (fun ω => f (Y ω)) = q.expect (fun x => f x.val) := by
  classical
  have hatom : ∀ a : Fin (n + 1), q.prob (fun x => x.val = a.val) = q.mass a := by
    intro a
    simp only [prob, ← Fin.ext_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  calc
    p.expect (fun ω => f (Y ω)) =
        ∑ a : Fin (n + 1), p.prob (fun ω => Y ω = a.val) * f a.val := by
      unfold expect prob
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hy : Y ω < n + 1
      · let a : Fin (n + 1) := ⟨Y ω, hy⟩
        have heq : ∀ x : Fin (n + 1), (Y ω = x.val) ↔ a = x := by
          intro x
          change a.val = x.val ↔ a = x
          exact Fin.ext_iff.symm
        simp_rw [heq]
        simp [a]
      · have hnull : p.prob (fun η => Y η = Y ω) = 0 := by
          rw [hlaw]
          unfold prob
          apply Finset.sum_eq_zero
          intro x _
          have hx : x.val ≠ Y ω := by have := x.isLt; omega
          simp [hx]
        have hmass : p.mass ω = 0 :=
          p.mass_eq_zero_of_prob_eq_zero (fun η => Y η = Y ω) hnull rfl
        simp [hmass]
    _ = ∑ a : Fin (n + 1), q.prob (fun x => x.val = a.val) * f a.val := by
      simp_rw [hlaw]
    _ = q.expect (fun x => f x.val) := by
      simp_rw [hatom]
      rfl

theorem prob_eq_of_count_law (p : FiniteLaw Ω) (Y : Ω → ℕ) (n : ℕ)
    (q : FiniteLaw (Fin (n + 1)))
    (hlaw : ∀ a : ℕ, p.prob (fun ω => Y ω = a) =
      q.prob (fun x => x.val = a)) (B : ℕ → Prop) :
    p.prob (fun ω => B (Y ω)) = q.prob (fun x => B x.val) := by
  classical
  have h := p.expect_eq_of_count_law Y n q hlaw (fun a => if B a then 1 else 0)
  simpa [expect, prob, mul_ite] using h

theorem variance_eq_of_count_law (p : FiniteLaw Ω) (Y : Ω → ℕ) (n : ℕ)
    (q : FiniteLaw (Fin (n + 1)))
    (hlaw : ∀ a : ℕ, p.prob (fun ω => Y ω = a) =
      q.prob (fun x => x.val = a)) (f : ℕ → ℝ) :
    p.variance (fun ω => f (Y ω)) = q.variance (fun x => f x.val) := by
  unfold variance
  rw [p.expect_eq_of_count_law Y n q hlaw f]
  exact p.expect_eq_of_count_law Y n q hlaw
    (fun a => (f a - q.expect (fun x => f x.val)) ^ 2)

/-- C4 for a natural-valued count on a positive atom. -/
theorem conditional_expect_eq_of_count_law (p : FiniteLaw Ω)
    (E : Ω → Prop) (hE : 0 < p.prob E) (Y : Ω → ℕ) (n : ℕ)
    (q : FiniteLaw (Fin (n + 1)))
    (hlaw : ∀ a : ℕ, p.conditionalProb E (fun ω => Y ω = a) =
      q.prob (fun x => x.val = a)) (f : ℕ → ℝ) :
    p.conditionalExpect E (fun ω => f (Y ω)) = q.expect (fun x => f x.val) := by
  rw [← condition_expect]
  apply (p.condition E hE).expect_eq_of_count_law Y n q
  intro a
  rw [condition_prob]
  exact hlaw a

theorem conditional_prob_eq_of_count_law (p : FiniteLaw Ω)
    (E : Ω → Prop) (hE : 0 < p.prob E) (Y : Ω → ℕ) (n : ℕ)
    (q : FiniteLaw (Fin (n + 1)))
    (hlaw : ∀ a : ℕ, p.conditionalProb E (fun ω => Y ω = a) =
      q.prob (fun x => x.val = a)) (B : ℕ → Prop) :
    p.conditionalProb E (fun ω => B (Y ω)) = q.prob (fun x => B x.val) := by
  rw [← condition_prob]
  apply (p.condition E hE).prob_eq_of_count_law Y n q
  intro a
  rw [condition_prob]
  exact hlaw a

theorem conditional_variance_eq_of_count_law (p : FiniteLaw Ω)
    (E : Ω → Prop) (hE : 0 < p.prob E) (Y : Ω → ℕ) (n : ℕ)
    (q : FiniteLaw (Fin (n + 1)))
    (hlaw : ∀ a : ℕ, p.conditionalProb E (fun ω => Y ω = a) =
      q.prob (fun x => x.val = a)) (f : ℕ → ℝ) :
    (p.condition E hE).variance (fun ω => f (Y ω)) =
      q.variance (fun x => f x.val) := by
  apply (p.condition E hE).variance_eq_of_count_law Y n q
  intro a
  rw [condition_prob]
  exact hlaw a

@[ext] theorem ext_mass (p q : FiniteLaw Ω) (h : ∀ ω, p.mass ω = q.mass ω) : p = q := by
  cases p
  cases q
  simp only at h
  congr
  exact funext h

/-- Independent finite coordinates, including an empty coordinate index. -/
def product {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, Fintype (X i)]
    (p : ∀ i, FiniteLaw (X i)) : FiniteLaw (∀ i, X i) := by
  classical
  refine ⟨(fun x => ∏ i, (p i).mass (x i)), ?_, ?_⟩
  · intro x
    exact Finset.prod_nonneg (fun i _ => (p i).mass_nonneg (x i))
  · rw [← Fintype.prod_sum]
    simp_rw [mass_sum]
    simp

theorem product_prob_rectangle {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteLaw (X i)) (E : ∀ i, X i → Prop) :
    (product p).prob (fun x => ∀ i, E i (x i)) = ∏ i, (p i).prob (E i) := by
  classical
  unfold prob product
  simp only
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact Fintype.prod_ite_zero.symm

theorem product_prob_rectangle_pos {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteLaw (X i)) (E : ∀ i, X i → Prop)
    (hE : ∀ i, 0 < (p i).prob (E i)) :
    0 < (product p).prob (fun x => ∀ i, E i (x i)) := by
  rw [product_prob_rectangle]
  exact Finset.prod_pos (fun i _ => hE i)

/-- C2's independence step: conditioning independent columns on separate
positive prescriptions preserves their product law. -/
theorem condition_product_rectangle {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (p : ∀ i, FiniteLaw (X i)) (E : ∀ i, X i → Prop)
    (hE : ∀ i, 0 < (p i).prob (E i)) :
    (product p).condition (fun x => ∀ i, E i (x i))
        (product_prob_rectangle_pos p E hE) =
      product (fun i => (p i).condition (E i) (hE i)) := by
  classical
  apply ext_mass
  intro x
  rw [condition_mass, product_prob_rectangle]
  simp only [product, condition_mass]
  rw [Finset.prod_div_distrib, Fintype.prod_ite_zero]

end
end FiniteLaw
end Shuffle
