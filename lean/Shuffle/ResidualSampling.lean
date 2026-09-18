import Shuffle.SubsetSampling

noncomputable section
open scoped BigOperators
open Finset

namespace Shuffle

variable {α : Type*} [DecidableEq α]

/-- The exact finite bijection behind C1. Feasibility is not replaced by a
positive-size assumption: residual populations may be empty. -/
def residualSampleEquiv (V R B : Finset α) (m : ℕ)
    (hR : R ⊆ V) (hB : B ⊆ R) (hBm : B.card ≤ m) :
    {S : Sample V m // S.val ∩ R = B} ≃ Sample (V \ R) (m - B.card) := by
  classical
  refine
    { toFun := fun S => ⟨S.val.val \ R, ?_⟩
      invFun := fun T => ⟨⟨B ∪ T.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨hSV, hSm⟩ := Finset.mem_powersetCard.mp S.val.property
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset_sdiff hSV (Subset.refl R), ?_⟩
    have hc := Finset.card_sdiff_add_card_inter S.val.val R
    rw [S.property, hSm] at hc
    omega
  · obtain ⟨hTV, hTm⟩ := Finset.mem_powersetCard.mp T.property
    have hd : Disjoint B T.val := by
      apply Finset.disjoint_left.mpr
      intro a haB haT
      exact (Finset.mem_sdiff.mp (hTV haT)).2 (hB haB)
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.union_subset (hB.trans hR) (hTV.trans Finset.sdiff_subset), ?_⟩
    rw [Finset.card_union_of_disjoint hd, hTm]
    omega
  · obtain ⟨hTV, _⟩ := Finset.mem_powersetCard.mp T.property
    ext a
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨haB | haT, haR⟩
      · exact haB
      · exact False.elim ((Finset.mem_sdiff.mp (hTV haT)).2 haR)
    · intro haB
      exact ⟨Or.inl haB, hB haB⟩
  · intro S
    apply Subtype.ext
    apply Subtype.ext
    change B ∪ (S.val.val \ R) = S.val.val
    calc
      B ∪ (S.val.val \ R) = (S.val.val ∩ R) ∪ (S.val.val \ R) :=
        congrArg (fun T => T ∪ (S.val.val \ R)) S.property.symm
      _ = S.val.val := by
        rw [Finset.union_comm]
        exact Finset.sdiff_union_inter S.val.val R
  · intro T
    obtain ⟨hTV, _⟩ := Finset.mem_powersetCard.mp T.property
    apply Subtype.ext
    change (B ∪ T.val) \ R = T.val
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨haB | haT, haR⟩
      · exact False.elim (haR (hB haB))
      · exact haT
    · intro haT
      exact ⟨Or.inr haT, (Finset.mem_sdiff.mp (hTV haT)).2⟩

/-- C1: the exact feasibility conditions characterize positive prescription
probability under uniform sampling. -/
theorem sample_prescription_pos_iff (V R B : Finset α) (m : ℕ)
    (hR : R ⊆ V) (hB : B ⊆ R) (hm : m ≤ V.card) :
    0 < (sampleLaw V m hm).prob (fun S => S.val ∩ R = B) ↔
      B.card ≤ m ∧ m - B.card ≤ (V \ R).card := by
  classical
  letI : Nonempty (Sample V m) :=
    let ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hm
    ⟨⟨S, hS⟩⟩
  change 0 < (FiniteLaw.uniform (Sample V m)).prob _ ↔ _
  rw [FiniteLaw.uniform_prob_pos_iff]
  constructor
  · rintro ⟨S, hS⟩
    have hSm := (Finset.mem_powersetCard.mp S.property).2
    have hBm : B.card ≤ m := by
      calc
        B.card = (S.val ∩ R).card := congrArg Finset.card hS.symm
        _ ≤ S.val.card := Finset.card_le_card Finset.inter_subset_left
        _ = m := hSm
    refine ⟨hBm, ?_⟩
    have T := residualSampleEquiv V R B m hR hB hBm ⟨S, hS⟩
    obtain ⟨hTV, hTm⟩ := Finset.mem_powersetCard.mp T.property
    rw [← hTm]
    exact Finset.card_le_card hTV
  · rintro ⟨hBm, hres⟩
    obtain ⟨T, hT⟩ := Finset.powersetCard_nonempty.mpr hres
    let S := (residualSampleEquiv V R B m hR hB hBm).symm ⟨T, hT⟩
    exact ⟨S.val, S.property⟩

/-- C1: conditional residual samples have exactly uniform point masses. -/
theorem sample_conditional_residual_mass (V R B : Finset α) (m : ℕ)
    (hR : R ⊆ V) (hB : B ⊆ R) (hm : m ≤ V.card)
    (hBm : B.card ≤ m) (hres : m - B.card ≤ (V \ R).card)
    (T : Sample (V \ R) (m - B.card)) :
    (sampleLaw V m hm).conditionalProb (fun S => S.val ∩ R = B)
      (fun S => S.val \ R = T.val) =
      1 / (Fintype.card (Sample (V \ R) (m - B.card)) : ℝ) := by
  classical
  letI : Nonempty (Sample V m) :=
    let ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hm
    ⟨⟨S, hS⟩⟩
  let e := residualSampleEquiv V R B m hR hB hBm
  have hcard : Fintype.card {S : Sample V m // S.val \ R = T.val ∧ S.val ∩ R = B} = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    have hd : (e.symm T).val.val \ R = T.val :=
      congrArg Subtype.val (e.apply_symm_apply T)
    refine ⟨⟨(e.symm T).val, hd, (e.symm T).property⟩, ?_⟩
    intro S
    apply Subtype.ext
    have heq : (⟨S.val, S.property.2⟩ : {S : Sample V m // S.val ∩ R = B}) =
        e.symm T := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      exact S.property.1
    exact congrArg (fun S : {S : Sample V m // S.val ∩ R = B} => S.val) heq
  change (FiniteLaw.uniform (Sample V m)).conditionalProb _ _ = _
  have hden := Fintype.card_congr e
  rw [FiniteLaw.uniform_conditionalProb]
  simp only [Fintype.card_eq_nat_card] at hcard hden ⊢
  rw [hcard, hden]
  simp

/-- C1: every test count in the unrevealed labels has the residual sample
law, before any hypergeometric moment theorem is used. -/
theorem sample_conditional_intersection_prob (V R B A : Finset α) (m q : ℕ)
    (hR : R ⊆ V) (hB : B ⊆ R) (hm : m ≤ V.card)
    (hBm : B.card ≤ m) (hres : m - B.card ≤ (V \ R).card)
    (hA : A ⊆ V \ R) :
    (sampleLaw V m hm).conditionalProb (fun S => S.val ∩ R = B)
      (fun S => (A ∩ S.val).card = q) =
      (sampleLaw (V \ R) (m - B.card) hres).prob
        (fun T => (A ∩ T.val).card = q) := by
  classical
  letI : Nonempty (Sample V m) :=
    let ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hm
    ⟨⟨S, hS⟩⟩
  letI : Nonempty (Sample (V \ R) (m - B.card)) :=
    let ⟨T, hT⟩ := Finset.powersetCard_nonempty.mpr hres
    ⟨⟨T, hT⟩⟩
  let e := residualSampleEquiv V R B m hR hB hBm
  have hinter : ∀ S : Finset α, A ∩ S = A ∩ (S \ R) := by
    intro S
    ext a
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    constructor
    · rintro ⟨haA, haS⟩
      exact ⟨haA, haS, (Finset.mem_sdiff.mp (hA haA)).2⟩
    · rintro ⟨haA, haS, _⟩
      exact ⟨haA, haS⟩
  let e0 : {S : Sample V m // (A ∩ S.val).card = q ∧ S.val ∩ R = B} ≃
      {S : {S : Sample V m // S.val ∩ R = B} // (A ∩ S.val.val).card = q} :=
    { toFun := fun S => ⟨⟨S.val, S.property.2⟩, S.property.1⟩
      invFun := fun S => ⟨S.val.val, S.property, S.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 : {S : {S : Sample V m // S.val ∩ R = B} // (A ∩ S.val.val).card = q} ≃
      {T : Sample (V \ R) (m - B.card) // (A ∩ T.val).card = q} :=
    e.subtypeEquiv (fun S => by
      change (A ∩ S.val.val).card = q ↔ (A ∩ (S.val.val \ R)).card = q
      rw [hinter S.val.val])
  have hnum := Fintype.card_congr (e0.trans e1)
  have hden := Fintype.card_congr e
  change (FiniteLaw.uniform (Sample V m)).conditionalProb _ _ =
    (FiniteLaw.uniform (Sample (V \ R) (m - B.card))).prob _
  rw [FiniteLaw.uniform_conditionalProb, FiniteLaw.uniform_prob]
  simp only [Fintype.card_eq_nat_card] at hnum hden ⊢
  rw [hnum, hden]

/-- C1's conditional hypergeometric law with the exact residual parameters. -/
theorem sample_conditional_hypergeom_mass (V R B A : Finset α) (m : ℕ)
    (hR : R ⊆ V) (hB : B ⊆ R) (hm : m ≤ V.card)
    (hBm : B.card ≤ m) (hres : m - B.card ≤ (V \ R).card)
    (hA : A ⊆ V \ R) (q : Fin (m - B.card + 1)) :
    (sampleLaw V m hm).conditionalProb (fun S => S.val ∩ R = B)
      (fun S => (A ∩ S.val).card = q.val) =
      (samplingParams (V \ R) A (m - B.card) hA hres).weight q := by
  rw [sample_conditional_intersection_prob V R B A m q.val hR hB hm hBm hres hA]
  exact sample_intersection_mass (V \ R) A (m - B.card) hA hres q

/-- H0's sampling bridge at every natural point, including points outside
the sampling support. -/
theorem sample_intersection_law (V A : Finset α) (m : ℕ)
    (hA : A ⊆ V) (hm : m ≤ V.card) (q : ℕ) :
    (sampleLaw V m hm).prob (fun S => (A ∩ S.val).card = q) =
      (samplingParams V A m hA hm).law.prob (fun x => x.val = q) := by
  change _ = (samplingParams V A m hA hm).pointMass q
  by_cases hq : q ≤ m
  · let q' : Fin (m + 1) := ⟨q, by omega⟩
    exact (sample_intersection_mass V A m hA hm q').trans
      ((samplingParams V A m hA hm).pointMass_eq_weight q').symm
  · have hfalse : (fun S : Sample V m => (A ∩ S.val).card = q) = (fun _ => False) := by
      funext S
      apply propext
      constructor
      · intro h
        have hcard := Finset.card_le_card (Finset.inter_subset_right : A ∩ S.val ⊆ S.val)
        have hSm := (Finset.mem_powersetCard.mp S.property).2
        omega
      · exact False.elim
    rw [hfalse, FiniteLaw.prob_false,
      HypergeomParams.pointMass_eq_zero_of_lt _ (by exact Nat.lt_of_not_ge hq)]

/-- C1's complete conditional count law, suitable for C4 moment transfer. -/
theorem sample_conditional_hypergeom_law (V R B A : Finset α) (m : ℕ)
    (hR : R ⊆ V) (hB : B ⊆ R) (hm : m ≤ V.card)
    (hBm : B.card ≤ m) (hres : m - B.card ≤ (V \ R).card)
    (hA : A ⊆ V \ R) (q : ℕ) :
    (sampleLaw V m hm).conditionalProb (fun S => S.val ∩ R = B)
      (fun S => (A ∩ S.val).card = q) =
      (samplingParams (V \ R) A (m - B.card) hA hres).law.prob
        (fun x => x.val = q) := by
  rw [sample_conditional_intersection_prob V R B A m q hR hB hm hBm hres hA]
  exact sample_intersection_law (V \ R) A (m - B.card) hA hres q

/-- C3: an atomwise uniform sample remains an exact hypergeometric count
when the marked set is determined by the already revealed atom. -/
theorem conditional_uniform_sample_intersection_mass
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (p : FiniteLaw Ω)
    (Z : Ω → Γ) (V : Finset α) (m : ℕ) (hm : m ≤ V.card)
    (S : Ω → Sample V m) (A : Γ → Finset α) (z : Γ)
    (hz : 0 < p.prob (fun ω => Z ω = z)) (hA : A z ⊆ V)
    (hlaw : (p.condition (fun ω => Z ω = z) hz).map S = sampleLaw V m hm)
    (q : Fin (m + 1)) :
    p.conditionalProb (fun ω => Z ω = z)
      (fun ω => (A (Z ω) ∩ (S ω).val).card = q.val) =
      (samplingParams V (A z) m hA hm).weight q := by
  have heq : p.conditionalProb (fun ω => Z ω = z)
        (fun ω => (A (Z ω) ∩ (S ω).val).card = q.val) =
      p.conditionalProb (fun ω => Z ω = z)
        (fun ω => (A z ∩ (S ω).val).card = q.val) := by
    apply le_antisymm
    · apply p.conditionalProb_mono_on
      intro ω hω hcount
      simpa only [hω] using hcount
    · apply p.conditionalProb_mono_on
      intro ω hω hcount
      simpa only [hω] using hcount
  rw [heq]
  rw [p.conditional_prob_eq_of_map_eq _ hz S (sampleLaw V m hm) hlaw
    (fun T => (A z ∩ T.val).card = q.val)]
  exact sample_intersection_mass V (A z) m hA hm q

/-- C3 at every natural point, with no extra support assumption. -/
theorem conditional_uniform_sample_intersection_law
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (p : FiniteLaw Ω)
    (Z : Ω → Γ) (V : Finset α) (m : ℕ) (hm : m ≤ V.card)
    (S : Ω → Sample V m) (A : Γ → Finset α) (z : Γ)
    (hz : 0 < p.prob (fun ω => Z ω = z)) (hA : A z ⊆ V)
    (hlaw : (p.condition (fun ω => Z ω = z) hz).map S = sampleLaw V m hm)
    (q : ℕ) :
    p.conditionalProb (fun ω => Z ω = z)
      (fun ω => (A (Z ω) ∩ (S ω).val).card = q) =
      (samplingParams V (A z) m hA hm).law.prob (fun x => x.val = q) := by
  have heq : p.conditionalProb (fun ω => Z ω = z)
        (fun ω => (A (Z ω) ∩ (S ω).val).card = q) =
      p.conditionalProb (fun ω => Z ω = z)
        (fun ω => (A z ∩ (S ω).val).card = q) := by
    apply le_antisymm
    · apply p.conditionalProb_mono_on
      intro ω hω hcount
      simpa only [hω] using hcount
    · apply p.conditionalProb_mono_on
      intro ω hω hcount
      simpa only [hω] using hcount
  rw [heq]
  rw [p.conditional_prob_eq_of_map_eq _ hz S (sampleLaw V m hm) hlaw
    (fun T => (A z ∩ T.val).card = q)]
  exact sample_intersection_law V (A z) m hA hm q

end Shuffle
