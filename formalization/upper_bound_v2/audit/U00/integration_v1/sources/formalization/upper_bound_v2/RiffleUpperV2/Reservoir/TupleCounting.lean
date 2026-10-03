import RiffleUpperV2.Reservoir.MarkedRefinement

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

/-- Counting ordered distinct marked tuples in an arbitrary row predicate. -/
theorem sum_marked_indicators {n m : ℕ} (B : Fin n → Prop) [DecidablePred B] :
    (∑ f : Fin m ↪ Fin n, if ∀ i, B (f i) then (1:ℝ) else 0) =
      RiffleLowerV2.falling (Finset.univ.filter B).card m := by
  let e : {f : Fin m ↪ Fin n // ∀ i, B (f i)} ≃ (Fin m ↪ {r : Fin n // B r}) :=
    { toFun := fun f => ⟨fun i => ⟨f.val i,f.property i⟩, fun i j h => f.val.injective (congrArg Subtype.val h)⟩
      invFun := fun f => ⟨f.trans (Function.Embedding.subtype B),fun i => (f i).property⟩
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl }
  have hc := Fintype.card_congr e
  rw [Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_subtype] at hc
  have hc' := congrArg (fun n : ℕ => (n:ℝ)) hc
  simpa only [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,
    apply_ite,Nat.cast_one,Nat.cast_zero,RiffleLowerV2.falling] using hc'

def pileTailCount {k n L E : ℕ} {cuts : Cuts k n (L+1)} (p : Fin k)
    (v : Word k (min E L)) (ω : Sample cuts) : ℕ :=
  (Finset.univ.filter fun r : Fin n => (rowWord ω r).get 0=p ∧ tailPrefix E (rowWord ω r)=v).card

theorem sum_markedPile_indicators {k n L m : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) :
    (∑ f : Fin m ↪ Fin n, if markedPileEvent p f ω then (1:ℝ) else 0) =
      RiffleLowerV2.falling (pileSize cuts p) m := by
  have h := sum_marked_indicators (m := m) (fun r : Fin n => (rowWord ω r).get 0=p)
  rw [show (Finset.univ.filter (fun r : Fin n => (rowWord ω r).get 0=p)).card=pileSize cuts p from
    pileLabels_card cuts p ω] at h
  calc
    _ = ∑ f : Fin m ↪ Fin n, if ∀ i, (rowWord ω (f i)).get 0=p then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      unfold markedPileEvent
      split_ifs <;> rfl
    _ = _ := h

theorem sum_markedTail_indicators {k n L m E : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (v : Word k (min E L)) (ω : Sample cuts) :
    (∑ f : Fin m ↪ Fin n, if markedTailEvent p f v ω then (1:ℝ) else 0) =
      RiffleLowerV2.falling (pileTailCount p v ω) m := by
  have h := sum_marked_indicators (m := m)
    (fun r : Fin n => (rowWord ω r).get 0=p ∧ tailPrefix E (rowWord ω r)=v)
  calc
    _ = ∑ f : Fin m ↪ Fin n,
        if ∀ i, (rowWord ω (f i)).get 0=p ∧ tailPrefix E (rowWord ω (f i))=v then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      by_cases hh : markedTailEvent p f v ω
      · have hh' : ∀ i, (rowWord ω (f i)).get 0=p ∧ tailPrefix E (rowWord ω (f i))=v :=
          fun i => ⟨hh.1 i,hh.2 i⟩
        simp [hh,hh']
      · have hh' : ¬∀ i, (rowWord ω (f i)).get 0=p ∧ tailPrefix E (rowWord ω (f i))=v :=
          fun h => hh ⟨fun i => (h i).1,fun i => (h i).2⟩
        simp only [hh,hh',if_false]
    _ = _ := by
      rw [h]
      congr 1

theorem conditionalExpect_sum_marked {Ω I : Type*} [Fintype Ω] [Fintype I]
    (P : PMF Ω) (B : I → Ω → Prop) (H : Ω → Prop) :
    conditionalExpect P (fun ω => ∑ i, if B i ω then (1:ℝ) else 0) H =
      ∑ i, conditionalProbability P (B i) H := by
  unfold conditionalExpect conditionalProbability RiffleLowerV2.conditionalExpect RiffleLowerV2.conditionalProbability
  unfold RiffleLowerV2.probability RiffleLowerV2.expect
  rw [← Finset.sum_div,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [← Finset.mul_sum]
  congr 1
  by_cases hH : H ω
  · simp only [hH,if_true,and_true]
  · simp only [hH,if_false,and_false,Finset.sum_const_zero]

theorem conditionalExpect_const_pos {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (H : Ω → Prop) (hH : 0<probability P H) (c : ℝ) :
    conditionalExpect P (fun _ => c) H=c := by
  unfold conditionalExpect RiffleLowerV2.conditionalExpect
  have he : expect P (fun ω => if H ω then c else 0)=probability P H*c := by
    unfold expect probability RiffleLowerV2.probability RiffleLowerV2.expect
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hh : H ω <;> simp [hh]
  change expect P (fun ω => if H ω then c else 0) / probability P H=c
  rw [he,mul_div_cancel_left₀ c (ne_of_gt hH)]

theorem sum_markedPile_conditionalProbability {k n L m : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (H : Sample cuts → Prop) (hH : 0<probability (fixedCountPMF cuts) H) :
    (∑ f : Fin m ↪ Fin n, conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H)=
      RiffleLowerV2.falling (pileSize cuts p) m := by
  rw [← conditionalExpect_sum_marked]
  simp_rw [sum_markedPile_indicators cuts p]
  exact conditionalExpect_const_pos _ H hH _

end RiffleUpperV2.Reservoir
