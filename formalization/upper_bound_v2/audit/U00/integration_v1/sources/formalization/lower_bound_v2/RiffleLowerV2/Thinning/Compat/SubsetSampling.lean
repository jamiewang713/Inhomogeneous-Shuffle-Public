/- LB02 source compatibility port of `lean/Shuffle/SubsetSampling.lean`.
Original SHA-256: 23da7cc182126632e7f5f0f0e897f9da15bd06aa17247023a9722ccd74d86042.
Original files and freeze records are unchanged. -/

import RiffleLowerV2.Thinning.Compat.Conditioning
import RiffleLowerV2.Thinning.Compat.Hypergeometric
import Mathlib.Data.Finset.Powerset

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Finset

namespace RiffleLowerV2.Thinning.Compat

variable {α : Type*} [DecidableEq α]

abbrev Sample (V : Finset α) (m : ℕ) := {S : Finset α // S ∈ V.powersetCard m}

def sampleLaw (V : Finset α) (m : ℕ) (hm : m ≤ V.card) : FiniteLaw (Sample V m) := by
  letI : Nonempty (Sample V m) :=
    let ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hm
    ⟨⟨S, hS⟩⟩
  exact FiniteLaw.uniform _

def samplingParams (V A : Finset α) (m : ℕ) (hA : A ⊆ V) (hm : m ≤ V.card) :
    HypergeomParams := ⟨V.card, A.card, m, Finset.card_le_card hA, hm⟩

def intersectionCount (A : Finset α) {V : Finset α} {m : ℕ}
    (S : Sample V m) : Fin (m + 1) :=
  ⟨(A ∩ S.val).card, by
    have h1 : (A ∩ S.val).card ≤ S.val.card :=
      Finset.card_le_card Finset.inter_subset_right
    have h2 := (Finset.mem_powersetCard.mp S.property).2
    omega⟩

theorem intersection_fibre_card (V A : Finset α) (m q : ℕ)
    (hA : A ⊆ V) (hq : q ≤ m) :
    ((V.powersetCard m).filter (fun S => (A ∩ S).card = q)).card =
      A.card.choose q * (V.card - A.card).choose (m - q) := by
  classical
  have hc : ((V.powersetCard m).filter (fun S => (A ∩ S).card = q)).card =
      ((A.powersetCard q) ×ˢ ((V \ A).powersetCard (m - q))).card := by
    apply Finset.card_nbij' (fun S => (A ∩ S, S \ A)) (fun U => U.1 ∪ U.2)
    · intro S hS
      obtain ⟨hS, hSq⟩ := Finset.mem_filter.mp hS
      obtain ⟨hSV, hSm⟩ := Finset.mem_powersetCard.mp hS
      have hcard := Finset.card_sdiff_add_card_inter S A
      rw [Finset.inter_comm S A, hSq, hSm] at hcard
      refine Finset.mem_product.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_left, hSq⟩,
         Finset.mem_powersetCard.mpr
           ⟨Finset.sdiff_subset_sdiff hSV (Subset.refl A), ?_⟩⟩
      change (S \ A).card = m - q
      omega
    · intro U hU
      obtain ⟨hU1, hU2⟩ := Finset.mem_product.mp hU
      obtain ⟨hU1A, hU1q⟩ := Finset.mem_powersetCard.mp hU1
      obtain ⟨hU2V, hU2q⟩ := Finset.mem_powersetCard.mp hU2
      have hdis : Disjoint U.1 U.2 := by
        apply Finset.disjoint_left.mpr
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp (hU2V hx2)).2 (hU1A hx1)
      have hinter : A ∩ (U.1 ∪ U.2) = U.1 := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxA, hx1 | hx2⟩
          · exact hx1
          · exact False.elim ((Finset.mem_sdiff.mp (hU2V hx2)).2 hxA)
        · intro hx1
          exact ⟨hU1A hx1, Or.inl hx1⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.union_subset (hU1A.trans hA) (hU2V.trans Finset.sdiff_subset)
      · rw [Finset.card_union_of_disjoint hdis, hU1q, hU2q]
        omega
      · rw [hinter, hU1q]
    · intro S _
      change (A ∩ S) ∪ (S \ A) = S
      rw [Finset.union_comm, Finset.inter_comm]
      exact Finset.sdiff_union_inter S A
    · intro U hU
      obtain ⟨hU1, hU2⟩ := Finset.mem_product.mp hU
      obtain ⟨hU1A, _⟩ := Finset.mem_powersetCard.mp hU1
      obtain ⟨hU2V, _⟩ := Finset.mem_powersetCard.mp hU2
      apply Prod.ext
      · ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨hxA, hx1 | hx2⟩
          · exact hx1
          · exact False.elim ((Finset.mem_sdiff.mp (hU2V hx2)).2 hxA)
        · intro hx1
          exact ⟨hU1A hx1, Or.inl hx1⟩
      · ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨hx1 | hx2, hxA⟩
          · exact False.elim (hxA (hU1A hx1))
          · exact hx2
        · intro hx2
          exact ⟨Or.inr hx2, (Finset.mem_sdiff.mp (hU2V hx2)).2⟩
  rw [hc, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hA]

theorem sample_intersection_mass (V A : Finset α) (m : ℕ)
    (hA : A ⊆ V) (hm : m ≤ V.card) (q : Fin (m + 1)) :
    (sampleLaw V m hm).prob (fun S => (A ∩ S.val).card = q.val) =
      (samplingParams V A m hA hm).weight q := by
  classical
  letI : Nonempty (Sample V m) :=
    let ⟨S, hS⟩ := Finset.powersetCard_nonempty.mpr hm
    ⟨⟨S, hS⟩⟩
  have he : {S : Sample V m // (A ∩ S.val).card = q.val} ≃
      {S : Finset α // S ∈ (V.powersetCard m).filter (fun T => (A ∩ T).card = q.val)} :=
    { toFun := fun S => ⟨S.val.val, Finset.mem_filter.mpr ⟨S.val.property, S.property⟩⟩
      invFun := fun S => ⟨⟨S.val, (Finset.mem_filter.mp S.property).1⟩,
        (Finset.mem_filter.mp S.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hf := Fintype.card_congr he
  rw [Fintype.card_coe, intersection_fibre_card V A m q.val hA (by omega)] at hf
  change (FiniteLaw.uniform (Sample V m)).prob _ = _
  rw [FiniteLaw.uniform_prob]
  unfold HypergeomParams.weight samplingParams
  dsimp only
  congr 1
  · norm_cast
    simpa only [Fintype.card_eq_nat_card] using hf
  · simp [Sample, Finset.card_powersetCard]

/-- The sampling and binomial-coefficient laws agree at every natural point,
including points beyond the sample size. -/
theorem sample_intersection_pointMass (V A : Finset α) (m : ℕ)
    (hA : A ⊆ V) (hm : m ≤ V.card) (q : ℕ) :
    (sampleLaw V m hm).prob (fun S => (A ∩ S.val).card = q) =
      (samplingParams V A m hA hm).pointMass q := by
  by_cases hq : q ≤ m
  · let j : Fin (m + 1) := ⟨q, by omega⟩
    exact (sample_intersection_mass V A m hA hm j).trans
      ((samplingParams V A m hA hm).pointMass_eq_weight j).symm
  · rw [(samplingParams V A m hA hm).pointMass_eq_zero_of_lt (by
      change m < q
      omega)]
    apply le_antisymm _ ((sampleLaw V m hm).prob_nonneg _)
    calc
      _ ≤ (sampleLaw V m hm).prob (fun _ => False) := by
        apply FiniteLaw.prob_mono
        intro S hS
        have hb := (intersectionCount A S).isLt
        change (A ∩ S.val).card < m + 1 at hb
        omega
      _ = 0 := FiniteLaw.prob_false _

end RiffleLowerV2.Thinning.Compat
