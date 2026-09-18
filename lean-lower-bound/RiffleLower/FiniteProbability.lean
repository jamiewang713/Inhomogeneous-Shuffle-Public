import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace RiffleLower
attribute [local instance] Classical.propDecidable

structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

variable {α β E : Type*} [Fintype α] [Fintype β] [Fintype E]

def prob (P : FiniteLaw α) (A : Finset α) : ℝ := ∑ a ∈ A, P.mass a

def expect (P : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ a, P.mass a * f a

def variance (P : FiniteLaw α) (f : α → ℝ) : ℝ :=
  expect P (fun a => (f a - expect P f) ^ 2)

def uniformLaw (α : Type*) [Fintype α] [Nonempty α] : FiniteLaw α where
  mass := fun _ => (Fintype.card α : ℝ)⁻¹
  nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

def mapLaw (P : FiniteLaw α) (f : α → β) : FiniteLaw β where
  mass := fun b => ∑ a, if f a = b then P.mass a else 0
  nonneg := by
    intro b
    exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp [P.nonneg]
  total := by
    rw [Finset.sum_comm]
    simp [P.total]

def mixture (ρ : FiniteLaw E) (P : E → FiniteLaw α) : FiniteLaw α where
  mass := fun a => ∑ e, ρ.mass e * (P e).mass a
  nonneg := fun a => Finset.sum_nonneg fun e _ => mul_nonneg (ρ.nonneg e) ((P e).nonneg a)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp [FiniteLaw.total]

def tv (P Q : FiniteLaw α) : ℝ := (∑ a, |P.mass a - Q.mass a|) / 2

def unionEvents (A : E → Finset α) (G : Finset E) : Finset α := G.biUnion A

@[simp] theorem prob_empty (P : FiniteLaw α) : prob P ∅ = 0 := by simp [prob]
@[simp] theorem prob_univ (P : FiniteLaw α) : prob P Finset.univ = 1 := P.total

theorem prob_nonneg (P : FiniteLaw α) (A : Finset α) : 0 ≤ prob P A :=
  Finset.sum_nonneg fun a _ => P.nonneg a

theorem prob_mono (P : FiniteLaw α) {A B : Finset α} (h : A ⊆ B) : prob P A ≤ prob P B :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun a _ _ => P.nonneg a)

theorem prob_le_one (P : FiniteLaw α) (A : Finset α) : prob P A ≤ 1 := by
  simpa using prob_mono P (Finset.subset_univ A)

theorem prob_compl (P : FiniteLaw α) (A : Finset α) : prob P Aᶜ = 1 - prob P A := by
  have h := Finset.sum_add_sum_compl A P.mass
  change prob P A + prob P Aᶜ = ∑ a, P.mass a at h
  rw [P.total] at h
  linarith

theorem expect_mono (P : FiniteLaw α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect P f ≤ expect P g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

@[simp] theorem expect_const (P : FiniteLaw α) (c : ℝ) : expect P (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, P.total]

theorem expect_add (P : FiniteLaw α) (f g : α → ℝ) :
    expect P (fun a => f a + g a) = expect P f + expect P g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (P : FiniteLaw α) (f g : α → ℝ) :
    expect P (fun a => f a - g a) = expect P f - expect P g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (P : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    expect P (fun a => f a * c) = expect P f * c := by
  simp [expect, ← mul_assoc, Finset.sum_mul]

theorem expect_const_mul (P : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    expect P (fun a => c * f a) = c * expect P f := by
  simpa [mul_comm] using expect_mul_const P f c

theorem expect_sum (P : FiniteLaw α) {ι : Type*} (s : Finset ι) (f : ι → α → ℝ) :
    expect P (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect P (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_indicator (P : FiniteLaw α) (A : Finset α) :
    expect P (fun a => if a ∈ A then 1 else 0) = prob P A := by
  simp [expect, prob, Finset.sum_filter]

theorem prob_uniform [Nonempty α] (A : Finset α) :
    prob (uniformLaw α) A = (A.card : ℝ) / Fintype.card α := by
  simp [prob, uniformLaw, div_eq_mul_inv]

theorem expect_uniform [Nonempty α] (f : α → ℝ) :
    expect (uniformLaw α) f = (∑ a, f a) / Fintype.card α := by
  simp only [expect, uniformLaw, div_eq_mul_inv]
  rw [← Finset.mul_sum, mul_comm]

theorem prob_map (P : FiniteLaw α) (f : α → β) (A : Finset β) :
    prob (mapLaw P f) A = prob P (Finset.univ.filter fun a => f a ∈ A) := by
  simp only [prob, mapLaw]
  rw [Finset.sum_comm]
  simp [Finset.sum_filter]

theorem expect_map (P : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    expect (mapLaw P f) g = expect P (fun a => g (f a)) := by
  simp only [expect, mapLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

theorem prob_mixture (ρ : FiniteLaw E) (P : E → FiniteLaw α) (A : Finset α) :
    prob (mixture ρ P) A = ∑ e, ρ.mass e * prob (P e) A := by
  simp only [prob, mixture]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

theorem expect_mixture (ρ : FiniteLaw E) (P : E → FiniteLaw α) (f : α → ℝ) :
    expect (mixture ρ P) f = ∑ e, ρ.mass e * expect (P e) f := by
  simp only [expect, mixture, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum, mul_assoc]


theorem prob_unionEvents_le (P : FiniteLaw α) (A : E → Finset α) (G : Finset E) :
    prob P (unionEvents A G) ≤ ∑ e ∈ G, prob P (A e) := by
  calc
    prob P (unionEvents A G) = expect P (fun a => if a ∈ unionEvents A G then 1 else 0) :=
      (expect_indicator _ _).symm
    _ ≤ expect P (fun a => ∑ e ∈ G, if a ∈ A e then (1 : ℝ) else 0) := by
      apply expect_mono
      intro a
      by_cases ha : a ∈ unionEvents A G
      · obtain ⟨e, he, hae⟩ := Finset.mem_biUnion.mp ha
        simp only [if_pos ha]
        have h := Finset.single_le_sum (s := G) (f := fun e => if a ∈ A e then (1 : ℝ) else 0)
          (fun e _ => by dsimp only; split_ifs <;> norm_num) he
        simpa [hae] using h
      · simp only [if_neg ha]
        exact Finset.sum_nonneg fun e _ => by split_ifs <;> norm_num
    _ = ∑ e ∈ G, prob P (A e) := by rw [expect_sum]; simp_rw [expect_indicator]

theorem prob_unionEvents_le_card (P : FiniteLaw α) (A : E → Finset α) (G : Finset E)
    (δ : ℝ) (h : ∀ e ∈ G, prob P (A e) ≤ δ) :
    prob P (unionEvents A G) ≤ (G.card : ℝ) * δ := by
  calc
    _ ≤ ∑ e ∈ G, prob P (A e) := prob_unionEvents_le P A G
    _ ≤ ∑ _e ∈ G, δ := Finset.sum_le_sum h
    _ = _ := by simp

theorem tv_nonneg (P Q : FiniteLaw α) : 0 ≤ tv P Q := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => abs_nonneg _) (by norm_num)

theorem tv_le_one (P Q : FiniteLaw α) : tv P Q ≤ 1 := by
  have h : ∑ a, |P.mass a - Q.mass a| ≤ ∑ a, (P.mass a + Q.mass a) := by
    apply Finset.sum_le_sum
    intro a _
    exact abs_le.mpr ⟨by linarith [P.nonneg a], by linarith [Q.nonneg a]⟩
  simp only [Finset.sum_add_distrib, P.total, Q.total] at h
  dsimp [tv]
  linarith

theorem abs_prob_sub_le_tv (P Q : FiniteLaw α) (A : Finset α) :
    |prob P A - prob Q A| ≤ tv P Q := by
  have hA : |prob P A - prob Q A| ≤ ∑ a ∈ A, |P.mass a - Q.mass a| := by
    simpa [prob, Finset.sum_sub_distrib] using
      Finset.abs_sum_le_sum_abs (fun a => P.mass a - Q.mass a) A
  have hC : |prob P Aᶜ - prob Q Aᶜ| ≤ ∑ a ∈ Aᶜ, |P.mass a - Q.mass a| := by
    simpa [prob, Finset.sum_sub_distrib] using
      Finset.abs_sum_le_sum_abs (fun a => P.mass a - Q.mass a) Aᶜ
  have heq : |prob P Aᶜ - prob Q Aᶜ| = |prob P A - prob Q A| := by
    rw [prob_compl, prob_compl]
    have : 1 - prob P A - (1 - prob Q A) = -(prob P A - prob Q A) := by ring
    rw [this, abs_neg]
  rw [heq] at hC
  have hs := Finset.sum_add_sum_compl A (fun a => |P.mass a - Q.mass a|)
  dsimp [tv]
  linarith

theorem tv_test (P Q : FiniteLaw α) (A : Finset α) (ε δ : ℝ)
    (hP : 1 - ε ≤ prob P A) (hQ : prob Q A ≤ δ) :
    1 - ε - δ ≤ tv P Q := by
  have h := (le_abs_self (prob P A - prob Q A)).trans (abs_prob_sub_le_tv P Q A)
  linarith

theorem mixture_common_event (ρ : FiniteLaw E) (P : E → FiniteLaw α)
    (G : Finset E) (A : Finset α) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hG : 1 - ε ≤ prob ρ G)
    (hA : ∀ e ∈ G, 1 - δ ≤ prob (P e) A) :
    1 - ε - δ ≤ prob (mixture ρ P) A := by
  by_cases hlarge : 1 ≤ δ
  · linarith [prob_nonneg (mixture ρ P) A]
  have hsmall : 0 ≤ 1 - δ := by linarith
  have hlocal : (1 - δ) * prob ρ G ≤ ∑ e ∈ G, ρ.mass e * prob (P e) A := by
    rw [prob, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hA e he) (ρ.nonneg e)
  have hdiscard : (∑ e ∈ G, ρ.mass e * prob (P e) A) ≤ prob (mixture ρ P) A := by
    rw [prob_mixture]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
      (fun e _ _ => mul_nonneg (ρ.nonneg e) (prob_nonneg (P e) A))
  have hg := mul_le_mul_of_nonneg_left hG hsmall
  nlinarith [mul_nonneg hε hδ]

theorem mixture_union_test (ρ : FiniteLaw E) (P : E → FiniteLaw α) (Q : FiniteLaw α)
    (G : Finset E) (A : E → Finset α) (b : E → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hG : 1 - ε ≤ prob ρ G)
    (hP : ∀ e ∈ G, 1 - δ ≤ prob (P e) (A e))
    (hQ : ∀ e ∈ G, prob Q (A e) ≤ b e) :
    1 - ε - δ - (∑ e ∈ G, b e) ≤ tv (mixture ρ P) Q := by
  have hs : 1 - ε - δ ≤ prob (mixture ρ P) (unionEvents A G) := by
    apply mixture_common_event ρ P G (unionEvents A G) ε δ hε hδ hG
    intro e he
    apply (hP e he).trans
    apply prob_mono
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨e, he, ha⟩
  have hf : prob Q (unionEvents A G) ≤ ∑ e ∈ G, b e :=
    (prob_unionEvents_le Q A G).trans (Finset.sum_le_sum hQ)
  have ht := tv_test (mixture ρ P) Q (unionEvents A G) (ε + δ) (∑ e ∈ G, b e)
    (by linarith) hf
  linarith


theorem variance_eq (P : FiniteLaw α) (f : α → ℝ) :
    variance P f = expect P (fun a => f a ^ 2) - (expect P f) ^ 2 := by
  have hf : (fun a => (f a - expect P f) ^ 2) =
      (fun a => (f a ^ 2 - (2 * expect P f) * f a) + (expect P f) ^ 2) := by
    funext a
    ring
  rw [variance, hf, expect_add, expect_sub, expect_const_mul, expect_const]
  ring

theorem variance_nonneg (P : FiniteLaw α) (f : α → ℝ) : 0 ≤ variance P f := by
  exact Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _)

theorem chebyshev (P : FiniteLaw α) (f : α → ℝ) (t : ℝ) (ht : 0 < t) :
    prob P (Finset.univ.filter fun a => t ≤ |f a - expect P f|) ≤ variance P f / t ^ 2 := by
  let A := Finset.univ.filter fun a => t ≤ |f a - expect P f|
  have hpoint : ∀ a, t ^ 2 * (if a ∈ A then (1 : ℝ) else 0) ≤ (f a - expect P f) ^ 2 := by
    intro a
    by_cases ha : a ∈ A
    · rw [if_pos ha, mul_one]
      have hdev : t ≤ |f a - expect P f| := (Finset.mem_filter.mp ha).2
      have hsq := pow_le_pow_left₀ (le_of_lt ht) hdev 2
      simpa only [sq_abs] using hsq
    · rw [if_neg ha, mul_zero]
      exact sq_nonneg _
  have hb := expect_mono P hpoint
  rw [expect_const_mul, expect_indicator] at hb
  change t ^ 2 * prob P A ≤ variance P f at hb
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  simpa [A, mul_comm] using hb

theorem variance_le_mean_of_factorial (P : FiniteLaw α) (f : α → ℝ)
    (h : expect P (fun a => f a * (f a - 1)) ≤ (expect P f) ^ 2) :
    variance P f ≤ expect P f := by
  have hf : (fun a => f a * (f a - 1)) = (fun a => f a ^ 2 - f a) := by
    funext a
    ring
  rw [hf, expect_sub] at h
  rw [variance_eq]
  linarith

theorem lower_tail_from_variance (P : FiniteLaw α) (f : α → ℝ) (m : ℝ)
    (hm : m < expect P f) (hv : variance P f ≤ expect P f) :
    1 - expect P f / (expect P f - m) ^ 2 ≤
      prob P (Finset.univ.filter fun a => m ≤ f a) := by
  let A := Finset.univ.filter fun a => f a < m
  have hsub : A ⊆ Finset.univ.filter (fun a => expect P f - m ≤ |f a - expect P f|) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    have hx : f a < m := (Finset.mem_filter.mp ha).2
    have habs := neg_le_abs (f a - expect P f)
    linarith
  have ht : 0 < expect P f - m := sub_pos.mpr hm
  have hb := (prob_mono P hsub).trans (chebyshev P f (expect P f - m) ht)
  have hb' : prob P A ≤ expect P f / (expect P f - m) ^ 2 :=
    hb.trans (div_le_div_of_nonneg_right hv (sq_nonneg _))
  have hc : Finset.univ.filter (fun a => m ≤ f a) = Aᶜ := by
    ext a
    simp [A, not_lt]
  rw [hc, prob_compl]
  linarith

end RiffleLower
