import RiffleUpperV2.Shared.Conditioning
import RiffleLowerV2.Thinning.PMFTools

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exponential
open RiffleLowerV2.Thinning

/-- Finite history measurability: the observable is constant on every history fiber. -/
def HistoryMeasurable {Ω H A : Type*} (h : Ω → H) (f : Ω → A) : Prop :=
  ∀ ω v, h ω = h v → f ω = f v

/-- Later observed histories determine every earlier history. -/
def Refining {Ω H : Type*} (h : ℕ → Ω → H) (m : ℕ) : Prop :=
  ∀ i j, i ≤ j → j ≤ m → ∀ ω v, h j ω = h j v → h i ω = h i v

variable {Ω H : Type*} [Fintype Ω] [Fintype H]

/-- No integrability side condition is needed for a finite PMF. -/
theorem expect_sum (P : PMF Ω) {I : Type*} (s : Finset I) (f : I → Ω → ℝ) :
    expect P (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expect P (f i) := by
  simp only [RiffleLowerV2.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expect_fiber_partition (P : PMF Ω) (h : Ω → H) (f : Ω → ℝ) :
    expect P f = ∑ z, expect P (fun ω => if h ω = z then f ω else 0) := by
  simp only [RiffleLowerV2.expect]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum]

/-- A null event has zero weight at each of its points. -/
theorem mass_zero_of_probability_zero (P : PMF Ω) (A : Ω → Prop)
    (hA : probability P A = 0) {ω : Ω} (hω : A ω) : (P ω).toReal = 0 := by
  have hh : (P ω).toReal ≤ probability P A := by
    change _ ≤ ∑ v, (P v).toReal * (if A v then 1 else 0)
    simpa only [hω, if_true, mul_one] using
      (Finset.single_le_sum (f := fun v => (P v).toReal * (if A v then (1 : ℝ) else 0))
        (fun v (_ : v ∈ (Finset.univ : Finset Ω)) => by positivity) (Finset.mem_univ ω))
  exact le_antisymm (hA ▸ hh) ENNReal.toReal_nonneg

theorem masked_expect_zero (P : PMF Ω) (A : Ω → Prop)
    (hA : probability P A = 0) (f : Ω → ℝ) :
    expect P (fun ω => if A ω then f ω else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro ω _
  by_cases ha : A ω
  · simp [ha, mass_zero_of_probability_zero P A hA ha]
  · simp [ha]

/-- Converts the literal conditional-expectation quotient to an unnormalized inequality,
including null fibers. The bound may have either sign on positive events. -/
theorem masked_expect_le (P : PMF Ω) (A : Ω → Prop) (f : Ω → ℝ) (c : ℝ)
    (hc : conditionalExpect P f A ≤ c) :
    expect P (fun ω => if A ω then f ω else 0) ≤ c * probability P A := by
  by_cases hz : probability P A = 0
  · simp [masked_expect_zero P A hz f, hz]
  · have hp : 0 < probability P A := lt_of_le_of_ne (probability_nonneg _ _) (Ne.symm hz)
    exact (div_le_iff₀ hp).mp hc

/-- Weighted conditional bounds. Only the weight's current-history measurability is used. -/
theorem expect_mul_le_of_conditional (P : PMF Ω) (h : Ω → H)
    (f w : Ω → ℝ) (c : ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (had : HistoryMeasurable h w)
    (hc : ∀ ω, 0 < probability P (fun v => h v = h ω) →
      conditionalExpect P f (fun v => h v = h ω) ≤ c) :
    expect P (fun ω => w ω * f ω) ≤ c * expect P w := by
  rw [expect_fiber_partition P h (fun ω => w ω * f ω), expect_fiber_partition P h w,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : probability P (fun ω => h ω = z) = 0
  · simp [masked_expect_zero P _ hz, hz]
  · have hp : 0 < probability P (fun ω => h ω = z) :=
      lt_of_le_of_ne (probability_nonneg _ _) (Ne.symm hz)
    obtain ⟨a, ha⟩ := probability_pos_exists P _ hp
    have hc' : conditionalExpect P f (fun v => h v = z) ≤ c := by
      simpa only [ha] using hc a (by simpa only [ha] using hp)
    have hwz (v : Ω) (hv : h v = z) : w v = w a := had v a (hv.trans ha.symm)
    have hleft : expect P (fun ω => if h ω = z then w ω * f ω else 0) =
        w a * expect P (fun ω => if h ω = z then f ω else 0) := by
      rw [← expect_const_mul]
      congr 1
      funext v
      by_cases hv : h v = z <;> simp [hv, hwz v]
    have hright : expect P (fun ω => if h ω = z then w ω else 0) =
        w a * probability P (fun ω => h ω = z) := by
      change _ = w a * expect P (fun ω => if h ω = z then 1 else 0)
      rw [← expect_const_mul]
      congr 1
      funext v
      by_cases hv : h v = z <;> simp [hv, hwz v]
    rw [hleft, hright]
    calc
      _ ≤ w a * (c * probability P (fun ω => h ω = z)) :=
        mul_le_mul_of_nonneg_left (masked_expect_le P _ f c hc') (hw a)
      _ = _ := by ring

/-- A bound against all nonnegative history-measurable weights implies the quotient bound
on each positive fiber; null fibers have conditional expectation zero. -/
theorem conditional_le_of_weighted (P : PMF Ω) (h : Ω → H) (f : Ω → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ w : Ω → ℝ, (∀ ω, 0 ≤ w ω) → HistoryMeasurable h w →
      expect P (fun ω => w ω * f ω) ≤ c * expect P w) (a : Ω) :
    conditionalExpect P f (fun v => h v = h a) ≤ c := by
  by_cases hz : probability P (fun v => h v = h a) = 0
  · simp [RiffleLowerV2.conditionalExpect, hz, hc]
  · have hp : 0 < probability P (fun v => h v = h a) :=
      lt_of_le_of_ne (probability_nonneg _ _) (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    have hb' := hb (fun v => if h v = h a then 1 else 0)
      (fun v => by split_ifs <;> norm_num)
      (by intro ω v hv; simp only [hv])
    simpa only [ite_mul, one_mul, zero_mul, RiffleLowerV2.probability] using hb'

/-- Conditional monotonicity requires comparison only inside the conditioning event. -/
theorem conditionalExpect_mono_on (P : PMF Ω) (A : Ω → Prop) {f g : Ω → ℝ}
    (hfg : ∀ ω, A ω → f ω ≤ g ω) : conditionalExpect P f A ≤ conditionalExpect P g A := by
  apply div_le_div_of_nonneg_right _ (probability_nonneg P A)
  apply expect_mono
  intro ω
  by_cases ha : A ω <;> simp [ha, hfg ω]

/-- A function vanishing on the conditioning event has zero conditional expectation. -/
theorem conditionalExpect_zero_on (P : PMF Ω) (A : Ω → Prop) {f : Ω → ℝ}
    (hf : ∀ ω, A ω → f ω = 0) : conditionalExpect P f A = 0 := by
  change expect P (fun ω => if A ω then f ω else 0) / probability P A = 0
  have he : (fun ω => if A ω then f ω else 0) = (fun _ => 0) := by
    funext ω
    by_cases ha : A ω <;> simp [ha, hf ω]
  rw [he]
  simp [expect, RiffleLowerV2.expect]

end RiffleUpperV2.Exponential
