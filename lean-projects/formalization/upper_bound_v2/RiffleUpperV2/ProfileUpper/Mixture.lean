import RiffleUpperV2.EmpiricalUpper.FiniteTV
import RiffleUpperV2.GraphOverlap.FiniteProbability
import RiffleUpperV2.Contracts.V1.Profile
import RiffleUpperV2.ProfileUpper.Buffered

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Filter
namespace RiffleUpperV2.ProfileUpper
open RiffleLowerV2.Factorial

theorem tv_nonnegative {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) : 0 ≤ tv P Q := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem tv_at_most_one {Ω : Type*} [Fintype Ω] (P Q : PMF Ω) : tv P Q ≤ 1 := by
  have hsum (R : PMF Ω) : (∑ ω, (R ω).toReal) = 1 := by
    simpa only [RiffleLowerV2.expect, mul_one] using expect_const R 1
  have h := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    show |(P ω).toReal-(Q ω).toReal| ≤ (P ω).toReal+(Q ω).toReal from by
      apply abs_le.mpr
      constructor <;> linarith [ENNReal.toReal_nonneg (a := P ω),
        ENNReal.toReal_nonneg (a := Q ω)])
  rw [Finset.sum_add_distrib, hsum, hsum] at h
  change (∑ ω, |(P ω).toReal-(Q ω).toReal|)/2 ≤ 1
  linarith

/-- The event may be any event of the entire environment. -/
theorem mixtureTypicalBound {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (Q : PMF Ω) (laws : Ω → PMF Γ) (U : PMF Γ) (A : Ω → Prop) :
    tv (Q.bind laws) U ≤ probability Q (fun a => ¬ A a) +
      expect Q (fun a => if A a then tv (laws a) U else 0) := by
  have hc := EmpiricalUpper.tv_bind_le Q laws (fun _ => U)
  simp only [PMF.bind_const] at hc
  refine hc.trans ?_
  change RiffleLowerV2.expect Q _ ≤ RiffleLowerV2.expect Q _ + RiffleLowerV2.expect Q _
  rw [← expect_add]
  apply expect_mono
  intro a
  by_cases ha : A a
  · simp [ha]
  · simpa [ha] using tv_at_most_one (laws a) U

theorem mixtureBound {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (Q : PMF Ω) (laws : Ω → PMF Γ) (U : PMF Γ) (A : Ω → Prop)
    {δ : ℝ} (hδ : 0 ≤ δ) (hgood : ∀ a, A a → tv (laws a) U ≤ δ) :
    tv (Q.bind laws) U ≤ 1 - probability Q A + δ := by
  have h := mixtureTypicalBound Q laws U A
  change tv (Q.bind laws) U ≤ RiffleLowerV2.probability Q (fun a => ¬ A a) + _ at h
  rw [GraphOverlap.probability_compl] at h
  refine h.trans (add_le_add_right ?_ _)
  calc
    _ ≤ RiffleLowerV2.expect Q (fun _ => δ) := by
      apply expect_mono
      intro a
      by_cases ha : A a
      · simpa [ha] using hgood a ha
      · simpa [ha] using hδ
    _ = δ := expect_const Q δ

theorem mixtureTendsto {Ω Γ : ℕ → Type*} [∀ N, Fintype (Ω N)] [∀ N, Fintype (Γ N)]
    (Q : ∀ N, PMF (Ω N)) (laws : ∀ N, Ω N → PMF (Γ N))
    (U : ∀ N, PMF (Γ N)) (A : ∀ N, Ω N → Prop)
    (htyp : Tendsto (fun N => probability (Q N) (A N)) atTop (nhds 1))
    (hgood : ∀ δ : ℝ, 0 < δ → ∀ᶠ N in atTop,
      ∀ a, A N a → tv (laws N a) (U N) ≤ δ) :
    Tendsto (fun N => tv ((Q N).bind (laws N)) (U N)) atTop (nhds 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun N => ha.trans_le (tv_nonnegative _ _)
  · intro δ hδ
    have ht := htyp.eventually (eventually_gt_nhds (show 1-δ/2 < (1 : ℝ) by linarith))
    filter_upwards [ht, hgood (δ/2) (by positivity)] with N hN hG
    have hb := mixtureBound (Q N) (laws N) (U N) (A N) (by positivity : 0 ≤ δ/2) hG
    linarith

theorem probability_inter_lower {Ω : Type*} [Fintype Ω] (Q : PMF Ω) (A B : Ω → Prop) :
    probability Q A + probability Q B - 1 ≤ probability Q (fun a => A a ∧ B a) := by
  have h := expect_mono Q (f := fun a => (if A a then (1 : ℝ) else 0) +
      (if B a then 1 else 0) - 1) (g := fun a => if A a ∧ B a then 1 else 0) (by
    intro a
    by_cases ha : A a <;> by_cases hb : B a <;> simp [ha, hb])
  simp only [expect_sub, expect_add, expect_const] at h
  simpa [probability, RiffleLowerV2.probability, expect, RiffleLowerV2.expect] using h

theorem probability_at_most_one {Ω : Type*} [Fintype Ω] (Q : PMF Ω) (A : Ω → Prop) :
    probability Q A ≤ 1 := by
  calc
    _ ≤ RiffleLowerV2.expect Q (fun _ => 1) := expect_mono Q (by intro a; split_ifs <;> norm_num)
    _ = 1 := expect_const Q 1

theorem probabilityInterTendsto {Ω : ℕ → Type*} [∀ N, Fintype (Ω N)]
    (Q : ∀ N, PMF (Ω N)) (A B : ∀ N, Ω N → Prop)
    (hA : Tendsto (fun N => probability (Q N) (A N)) atTop (nhds 1))
    (hB : Tendsto (fun N => probability (Q N) (B N)) atTop (nhds 1)) :
    Tendsto (fun N => probability (Q N) (fun a => A N a ∧ B N a)) atTop (nhds 1) := by
  have hlow := (hA.add hB).sub_const 1
  norm_num only at hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlow) tendsto_const_nhds
    (fun N => probability_inter_lower (Q N) (A N) (B N))
    (fun N => probability_at_most_one (Q N) _)

end RiffleUpperV2.ProfileUpper
