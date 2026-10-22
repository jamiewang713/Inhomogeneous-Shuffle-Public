import RiffleLowerV2.Shared.Adapters
import Contracts.v1
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Elementary finite PMF identities on the frozen shared definitions.
The finite-sum arguments adapt the legacy RiffleLower/FiniteProbability.lean
proof patterns; the law and predicate-event definitions here are the shared PMFs. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Ascent

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expect_mono (P : PMF Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    expect P f ≤ expect P g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) ENNReal.toReal_nonneg

theorem expect_nonneg (P : PMF Ω) {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) :
    0 ≤ expect P f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg ENNReal.toReal_nonneg (h ω)

theorem expect_const (P : PMF Ω) (c : ℝ) : expect P (fun _ => c) = c := by
  have hsum : (∑ ω, (P ω).toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun ω _ => P.apply_ne_top ω)]
    have h := P.tsum_coe
    rw [tsum_fintype] at h
    rw [h]
    simp
  simp only [expect, ← Finset.sum_mul, hsum, one_mul]

theorem expect_const_mul (P : PMF Ω) (c : ℝ) (f : Ω → ℝ) :
    expect P (fun ω => c * f ω) = c * expect P f := by
  simp only [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem expect_add (P : PMF Ω) (f g : Ω → ℝ) :
    expect P (fun ω => f ω + g ω) = expect P f + expect P g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (P : PMF Ω) (f g : Ω → ℝ) :
    expect P (fun ω => f ω - g ω) = expect P f - expect P g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_sum (P : PMF Ω) {I : Type*} (s : Finset I) (f : I → Ω → ℝ) :
    expect P (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expect P (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem probability_mono (P : PMF Ω) {A B : Ω → Prop} (h : ∀ ω, A ω → B ω) :
    probability P A ≤ probability P B := by
  apply expect_mono
  intro ω
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp_all

theorem probability_nonneg (P : PMF Ω) (A : Ω → Prop) : 0 ≤ probability P A := by
  apply expect_nonneg
  intro ω
  split_ifs <;> norm_num

theorem probability_le_one (P : PMF Ω) (A : Ω → Prop) : probability P A ≤ 1 := by
  rw [← expect_const P 1]
  apply expect_mono
  intro ω
  split_ifs <;> norm_num

theorem probability_true (P : PMF Ω) : probability P (fun _ => True) = 1 := by
  simpa [probability] using expect_const P 1

theorem probability_false (P : PMF Ω) : probability P (fun _ => False) = 0 := by
  simp [probability, expect]

theorem probability_not (P : PMF Ω) (A : Ω → Prop) :
    probability P (fun ω => ¬ A ω) = 1 - probability P A := by
  calc
    _ = expect P (fun ω => 1 - (if A ω then 1 else 0)) := by
      unfold probability
      apply congrArg (expect P)
      funext ω
      by_cases ha : A ω <;> simp [ha]
    _ = 1 - probability P A := by
      rw [expect_sub, expect_const]
      rfl

theorem probability_union_le (P : PMF Ω) (A B : Ω → Prop) :
    probability P (fun ω => A ω ∨ B ω) ≤ probability P A + probability P B := by
  simp only [probability]
  rw [← expect_add]
  apply expect_mono
  intro ω
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb]

theorem probability_iUnion_le {I : Type*} [Fintype I] (P : PMF Ω) (A : I → Ω → Prop) :
    probability P (fun ω => ∃ i, A i ω) ≤ ∑ i, probability P (A i) := by
  simp only [probability, expect]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  by_cases ha : ∃ i, A i ω
  · obtain ⟨i, hi⟩ := ha
    simp only [show (∃ i, A i ω) from ⟨i, hi⟩, if_true]
    exact le_trans (by simp [hi])
      (Finset.single_le_sum (fun j _ => by positivity) (Finset.mem_univ i))
  · simp only [ha, if_false]
    exact Finset.sum_nonneg fun _ _ => by positivity

theorem markov (P : PMF Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω)
    {t : ℝ} (ht : 0 < t) : probability P (fun ω => t ≤ f ω) ≤ expect P f / t := by
  apply (le_div_iff₀ ht).2
  rw [mul_comm, probability, ← expect_const_mul]
  apply expect_mono
  intro ω
  by_cases h : t ≤ f ω <;> simp [h, hf ω]

theorem expect_uniform [Nonempty Ω] (f : Ω → ℝ) :
    expect (PMF.uniformOfFintype Ω) f = (∑ ω, f ω) / Fintype.card Ω := by
  simp only [expect, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ← Finset.mul_sum]
  ring

theorem uniform_expect_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ) (f : Γ → ℝ) :
    expect (PMF.uniformOfFintype Ω) (fun ω => f (e ω)) =
      expect (PMF.uniformOfFintype Γ) f := by
  rw [expect_uniform, expect_uniform, Fintype.card_congr e, Equiv.sum_comp]

/-- Indicator adapter allowing any decidable representation of the same event. -/
theorem expect_indicator (P : PMF Ω) (A : Ω → Prop) [DecidablePred A] :
    expect P (fun ω => if A ω then (1 : ℝ) else 0) = probability P A := by
  unfold probability
  apply congrArg (expect P)
  funext ω
  by_cases ha : A ω <;> simp [ha]

theorem uniform_probability_equiv [Nonempty Ω] [Nonempty Γ] (e : Ω ≃ Γ)
    (A : Γ → Prop) :
    probability (PMF.uniformOfFintype Ω) (fun ω => A (e ω)) =
      probability (PMF.uniformOfFintype Γ) A := by
  exact uniform_expect_equiv e (fun ω => if A ω then (1 : ℝ) else 0)

theorem uniform_probability [Nonempty Ω] (A : Ω → Prop) :
    probability (PMF.uniformOfFintype Ω) A =
      (Fintype.card {ω // A ω} : ℝ) / Fintype.card Ω := by
  rw [probability, expect_uniform]
  congr 1
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end RiffleLowerV2.Ascent
