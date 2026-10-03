import RiffleUpperV2.Hypergeometric.Estimates
import RiffleLowerV2.Thinning.Compat.SubsetTransform

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Hypergeometric
open RiffleLowerV2 RiffleLowerV2.Thinning RiffleLowerV2.Thinning.Compat
variable {α : Type*} [DecidableEq α]

/-- Complementation is a bijection of the exact fixed-size sample spaces. -/
def sampleComplementEquiv (V : Finset α) (m : ℕ) (hm : m ≤ V.card) :
    Compat.Sample V m ≃ Compat.Sample V (V.card - m) where
  toFun S := ⟨V \ S.val, Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset,
    by rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp S.property).1,
      (Finset.mem_powersetCard.mp S.property).2]⟩⟩
  invFun S := ⟨V \ S.val, Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset,
    by rw [Finset.card_sdiff_of_subset (Finset.mem_powersetCard.mp S.property).1,
      (Finset.mem_powersetCard.mp S.property).2, Nat.sub_sub_self hm]⟩⟩
  left_inv S := by
    apply Subtype.ext
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp S.property).1
  right_inv S := by
    apply Subtype.ext
    exact Finset.sdiff_sdiff_eq_self (Finset.mem_powersetCard.mp S.property).1

theorem sampleComplement_expect (V : Finset α) (m : ℕ) (hm : m ≤ V.card)
    (f : Compat.Sample V (V.card - m) → ℝ) :
    (sampleLaw V m hm).expect (fun S => f (sampleComplementEquiv V m hm S)) =
      (sampleLaw V (V.card - m) (Nat.sub_le _ _)).expect f := by
  letI : Nonempty (Compat.Sample V m) :=
    let ⟨S,hS⟩ := Finset.powersetCard_nonempty.mpr hm
    ⟨⟨S,hS⟩⟩
  letI : Nonempty (Compat.Sample V (V.card-m)) :=
    let ⟨S,hS⟩ := Finset.powersetCard_nonempty.mpr (Nat.sub_le V.card m)
    ⟨⟨S,hS⟩⟩
  change (FiniteLaw.uniform _).expect _ = (FiniteLaw.uniform _).expect _
  simp only [FiniteLaw.expect, FiniteLaw.uniform, ← Finset.mul_sum,
    (sampleComplementEquiv V m hm).sum_comp,
    Fintype.card_congr (sampleComplementEquiv V m hm)]

/-- Sampling-complement law, including all deterministic boundary cases. -/
theorem sampleComplementLaw (V A : Finset α) (m : ℕ) (hm : m ≤ V.card)
    (hA : A ⊆ V) (f : ℕ → ℝ) :
    (sampleLaw V m hm).expect (fun S => f (A.card - (A ∩ S.val).card)) =
      (samplingParams V A (V.card-m) hA (Nat.sub_le _ _)).law.expect (fun q => f q.val) := by
  have he (S : Compat.Sample V m) : A.card - (A ∩ S.val).card =
      (A ∩ (sampleComplementEquiv V m hm S).val).card := by
    have hset : A ∩ (V \ S.val) = A \ S.val := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro ⟨ha, _, hs⟩; exact ⟨ha, hs⟩
      · rintro ⟨ha, hs⟩; exact ⟨ha, hA ha, hs⟩
    change A.card - (A ∩ S.val).card = (A ∩ (V \ S.val)).card
    rw [hset]
    have hc := Finset.card_sdiff_add_card_inter A S.val
    omega
  simp_rw [he]
  rw [sampleComplement_expect V m hm (fun S => f (A ∩ S.val).card)]
  exact sample_expect_intersection_eq_hypergeom V A (V.card-m) (Nat.sub_le _ _) hA f

theorem finiteLaw_conditionalProbability {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (A B : Ω → Prop) : conditionalProbability P.toPMF A B = P.conditionalProb B A := by
  unfold conditionalProbability FiniteLaw.conditionalProb
  rw [finiteLaw_probability, finiteLaw_probability]

/-- Exact positive-fiber law. Feasibility is derived from the positive probability. -/
theorem conditionalSamplingLaw (V R A B : Finset α) (m : ℕ)
    (hm : m ≤ V.card) (hR : R ⊆ V) (hA : A ⊆ V \ R)
    (hp : 0 < probability (sampleLaw V m hm).toPMF (fun S => S.val ∩ R = B)) :
    ∃ hres : m - B.card ≤ (V \ R).card,
      ∀ q : ℕ,
        conditionalProbability (sampleLaw V m hm).toPMF
          (fun S => (A ∩ S.val).card = q) (fun S => S.val ∩ R = B) =
        probability (samplingParams (V \ R) A (m-B.card) hA hres).law.toPMF
          (fun x => x.val = q) := by
  letI : Nonempty (Compat.Sample V m) :=
    let ⟨S,hS⟩ := Finset.powersetCard_nonempty.mpr hm
    ⟨⟨S,hS⟩⟩
  rw [finiteLaw_probability] at hp
  obtain ⟨S,hS⟩ := (FiniteLaw.uniform_prob_pos_iff _).mp hp
  have hSV := (Finset.mem_powersetCard.mp S.property).1
  have hSm := (Finset.mem_powersetCard.mp S.property).2
  have hB : B ⊆ R := by rw [← hS]; exact Finset.inter_subset_right
  have hBm : B.card ≤ m := by
    calc
      B.card = (S.val ∩ R).card := congrArg Finset.card hS.symm
      _ ≤ S.val.card := Finset.card_le_card Finset.inter_subset_left
      _ = m := hSm
  have hres : m-B.card ≤ (V \ R).card := by
    have hc := Finset.card_sdiff_add_card_inter S.val R
    rw [hS, hSm] at hc
    have hs := Finset.card_le_card (Finset.sdiff_subset_sdiff hSV (le_refl R))
    omega
  refine ⟨hres, fun q => ?_⟩
  rw [finiteLaw_conditionalProbability, finiteLaw_probability]
  exact sample_conditional_hypergeom_law V R B A m hR hB hm hBm hres hA q

/-- Conditional expectations use the same positive-fiber finite law. -/
theorem finiteLaw_conditionalExpect {Ω : Type*} [Fintype Ω] (P : FiniteLaw Ω)
    (f : Ω → ℝ) (B : Ω → Prop) :
    conditionalExpect P.toPMF f B = P.conditionalExpect B f := by
  unfold conditionalExpect FiniteLaw.conditionalExpect
  rw [finiteLaw_expect, finiteLaw_probability]
  simp only [FiniteLaw.expect, mul_ite, mul_zero]

/-- Transport all count observables and events on each positive sampling fiber. -/
theorem conditionalSamplingTransport (V R A B : Finset α) (m : ℕ)
    (hm : m ≤ V.card) (hR : R ⊆ V) (hA : A ⊆ V \ R)
    (hp : 0 < probability (sampleLaw V m hm).toPMF (fun S => S.val ∩ R = B)) :
    ∃ hres : m - B.card ≤ (V \ R).card,
      (∀ f : ℕ → ℝ,
        conditionalExpect (sampleLaw V m hm).toPMF
          (fun S => f (A ∩ S.val).card) (fun S => S.val ∩ R = B) =
        expect (samplingParams (V \ R) A (m-B.card) hA hres).law.toPMF
          (fun x => f x.val)) ∧
      (∀ E : ℕ → Prop,
        conditionalProbability (sampleLaw V m hm).toPMF
          (fun S => E (A ∩ S.val).card) (fun S => S.val ∩ R = B) =
        probability (samplingParams (V \ R) A (m-B.card) hA hres).law.toPMF
          (fun x => E x.val)) := by
  obtain ⟨hres, hlaw⟩ := conditionalSamplingLaw V R A B m hm hR hA hp
  rw [finiteLaw_probability] at hp
  have hlaw' : ∀ q : ℕ, (sampleLaw V m hm).conditionalProb
      (fun S => S.val ∩ R = B) (fun S => (A ∩ S.val).card = q) =
      (samplingParams (V \ R) A (m-B.card) hA hres).law.prob (fun x => x.val = q) := by
    intro q
    simpa only [finiteLaw_conditionalProbability, finiteLaw_probability] using hlaw q
  refine ⟨hres, ?_, ?_⟩
  · intro f
    rw [finiteLaw_conditionalExpect, finiteLaw_expect]
    exact FiniteLaw.conditional_expect_eq_of_count_law _ _ hp _ _ _ hlaw' f
  · intro E
    rw [finiteLaw_conditionalProbability, finiteLaw_probability]
    exact FiniteLaw.conditional_prob_eq_of_count_law _ _ hp _ _ _ hlaw' E

end RiffleUpperV2.Hypergeometric
