import RiffleUpperV2.Reservoir.CollisionPower

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open TimeProfile Exploration RiffleUpperV2.Localization
attribute [local instance 2000] wordDecEq

def markedWordEvent {k n d m : ℕ} {cuts : Cuts k n d} (f : Fin m ↪ Fin n)
    (w : Word k d) (ω : Sample cuts) : Prop := ∀ i, rowWord ω (f i)=w

def markedCollisionEvent {k n d : ℕ} {cuts : Cuts k n d} (f : Fin 2 ↪ Fin n)
    (x : Prefix k d) (ω : Sample cuts) : Prop :=
  (rowWord ω (f 0)).toList.take x.1.val=x.2.toList ∧
    markedWordEvent f (rowWord ω (f 0)) ω

theorem sum_markedWord_indicators {k n d m : ℕ} (cuts : Cuts k n d)
    (w : Word k d) (ω : Sample cuts) :
    (∑ f : Fin m ↪ Fin n, if markedWordEvent f w ω then (1:ℝ) else 0)=
      RiffleLowerV2.falling (wordCount ω w) m := by
  have h := sum_marked_indicators (m := m) (fun r : Fin n => rowWord ω r=w)
  calc
    _ = ∑ f : Fin m ↪ Fin n, if ∀ i, rowWord ω (f i)=w then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro f _
      unfold markedWordEvent
      split_ifs <;> rfl
    _ = _ := h

theorem markedCollision_indicator_partition {k n d : ℕ} (cuts : Cuts k n d)
    (f : Fin 2 ↪ Fin n) (x : Prefix k d) (G : Sample cuts → Prop) (ω : Sample cuts) :
    (∑ w : Word k d, if w.toList.take x.1.val=x.2.toList ∧ markedWordEvent f w ω ∧ G ω then (1:ℝ) else 0)=
      if markedCollisionEvent f x ω ∧ G ω then 1 else 0 := by
  rw [Finset.sum_eq_single (rowWord ω (f 0))]
  · simp only [markedCollisionEvent,and_assoc]
  · intro w _ hw
    have hn : ¬markedWordEvent f w ω := fun h => hw (h 0).symm
    simp only [hn,and_false,false_and,if_false]
  · simp

theorem conditionalCollision_good_partition {k n d : ℕ} (cuts : Cuts k n d)
    (f : Fin 2 ↪ Fin n) (x : Prefix k d) (G H : Sample cuts → Prop) :
    conditionalProbability (fixedCountPMF cuts) (fun ω => markedCollisionEvent f x ω ∧ G ω) H =
      ∑ w : Word k d, if w.toList.take x.1.val=x.2.toList then
        conditionalProbability (fixedCountPMF cuts) (fun ω => markedWordEvent f w ω ∧ G ω) H else 0 := by
  have hh : conditionalProbability (fixedCountPMF cuts) (fun ω => markedCollisionEvent f x ω ∧ G ω) H =
      ∑ w : Word k d, conditionalProbability (fixedCountPMF cuts)
        (fun ω => w.toList.take x.1.val=x.2.toList ∧ markedWordEvent f w ω ∧ G ω) H := by
    unfold conditionalProbability RiffleLowerV2.conditionalProbability RiffleLowerV2.probability RiffleLowerV2.expect
    rw [← Finset.sum_div,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro ω _
    rw [← Finset.mul_sum]
    congr 1
    by_cases hH : H ω
    · simp only [hH,and_true]
      exact (markedCollision_indicator_partition cuts f x G ω).symm
    · simp only [hH,and_false,if_false,Finset.sum_const_zero]
  rw [hh]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w.toList.take x.1.val=x.2.toList
  · simp only [hw,true_and,if_true]
  · simp only [hw,false_and,if_false]
    unfold conditionalProbability RiffleLowerV2.conditionalProbability
    simp only [false_and,RiffleLowerV2.probability,RiffleLowerV2.expect,if_false,mul_zero,Finset.sum_const_zero,zero_div]

theorem orderedCollision_count {k n d : ℕ} (cuts : Cuts k n d) (x : Prefix k d) (ω : Sample cuts) :
    (∑ w : Word k d, if w.toList.take x.1.val=x.2.toList then
      RiffleLowerV2.falling (wordCount ω w) 2 else 0)=
      ∑ f : Fin 2 ↪ Fin n, if markedCollisionEvent f x ω then (1:ℝ) else 0 := by
  simp_rw [← sum_markedWord_indicators]
  have hf (w : Word k d) :
      (if w.toList.take x.1.val=x.2.toList then
        ∑ f : Fin 2 ↪ Fin n, if markedWordEvent f w ω then (1:ℝ) else 0 else 0) =
      ∑ f : Fin 2 ↪ Fin n, if w.toList.take x.1.val=x.2.toList ∧ markedWordEvent f w ω ∧ True then (1:ℝ) else 0 := by
    by_cases hw : w.toList.take x.1.val=x.2.toList <;> simp only [hw,if_true,if_false,true_and,false_and,and_true,Finset.sum_const_zero]
  simp_rw [hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  simpa only [and_true] using markedCollision_indicator_partition cuts f x (fun _ => True) ω

/-- One ordered-pair exceptional probability controls all equal completions. -/
theorem collision_expectation_sum_bound {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (x : Prefix k (L+1)) (H : Sample cuts → Prop)
    (hH : 0<probability (fixedCountPMF cuts) H) (b ε : ℝ) (hε : 0≤ε)
    (hb : ∀ f : Fin 2 ↪ Fin n,
      conditionalProbability (fixedCountPMF cuts) (markedCollisionEvent f x) H≤
        b*conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H+ε) :
    conditionalExpect (fixedCountPMF cuts) (fun ω => ∑ w : Word k (L+1),
      if w.toList.take x.1.val=x.2.toList then ((wordCount ω w).choose 2:ℝ) else 0) H ≤
      b*RiffleLowerV2.falling (pileSize cuts p) 2+(n:ℝ)^2*ε := by
  have hsum := Finset.sum_le_sum (fun f (_ : f∈Finset.univ) => hb f)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_markedPile_conditionalProbability cuts p H hH,
    Finset.sum_const,Finset.card_univ,Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have he := conditionalExpect_sum_marked (fixedCountPMF cuts) (fun f ω => markedCollisionEvent f x ω) H
  simp_rw [← orderedCollision_count] at he
  have hmono : conditionalExpect (fixedCountPMF cuts) (fun ω => ∑ w : Word k (L+1),
      if w.toList.take x.1.val=x.2.toList then ((wordCount ω w).choose 2:ℝ) else 0) H ≤
      conditionalExpect (fixedCountPMF cuts) (fun ω => ∑ w : Word k (L+1),
      if w.toList.take x.1.val=x.2.toList then RiffleLowerV2.falling (wordCount ω w) 2 else 0) H := by
    apply conditionalExpect_mono_on
    intro ω _
    apply Finset.sum_le_sum
    intro w _
    split_ifs
    · unfold RiffleLowerV2.falling
      exact_mod_cast Nat.choose_le_descFactorial (wordCount ω w) 2
    · exact le_rfl
  apply (hmono.trans (he.trans_le hsum)).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow n 2) hε

end RiffleUpperV2.Reservoir
