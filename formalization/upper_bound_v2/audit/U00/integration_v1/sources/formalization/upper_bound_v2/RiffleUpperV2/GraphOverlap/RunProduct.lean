import RiffleUpperV2.GraphOverlap.Density

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.GraphOverlap
open RiffleLowerV2 RiffleLowerV2.Model

theorem prod_initialCard {α : Type*} [LinearOrder α] (s : Finset α) :
    (∏ i ∈ s, (s.filter (fun j => j ≤ i)).card) = s.card.factorial := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | @insert a s hmax ih =>
    have ha : a ∉ s := by intro h; exact (lt_irrefl a) (hmax a h)
    have hall : (insert a s).filter (fun j => j ≤ a) = insert a s := by
      apply Finset.filter_eq_self.mpr
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact le_rfl
      · exact (hmax j hj).le
    have hfilter (i : α) (hi : i ∈ s) :
        (insert a s).filter (fun j => j ≤ i) = s.filter (fun j => j ≤ i) := by
      rw [Finset.filter_insert, if_neg (not_le.mpr (hmax i hi))]
    rw [Finset.prod_insert ha, hall, Finset.card_insert_of_notMem ha]
    have hp : (∏ i ∈ s, ((insert a s).filter (fun j => j ≤ i)).card) =
        ∏ i ∈ s, (s.filter (fun j => j ≤ i)).card :=
      Finset.prod_congr rfl (fun i hi => congrArg Finset.card (hfilter i hi))
    rw [hp, ih, Nat.factorial_succ]

/-- Number of vertices up to `i` in the component containing `i`. -/
def runLength {N : ℕ} (G : PathEdges N) (i : Fin N) : ℕ :=
  (Finset.univ.filter fun j => componentKey G j = componentKey G i ∧ j ≤ i).card

theorem runLength_pos {N : ℕ} (G : PathEdges N) (i : Fin N) : 0 < runLength G i := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp⟩

/-- Each component contributes `1 · 2 · ... · size`, including singleton components. -/
theorem componentFactorial_eq_runProduct {N : ℕ} (G : PathEdges N) :
    componentFactorial G = ∏ i : Fin N, runLength G i := by
  rw [← Finset.prod_fiberwise Finset.univ (componentKey G) (runLength G)]
  unfold componentFactorial
  apply Finset.prod_congr rfl
  intro c _
  rw [← prod_initialCard]
  apply Finset.prod_congr rfl
  intro i hi
  have hc := (Finset.mem_filter.mp hi).2
  unfold runLength
  congr 1
  ext j
  simp [hc]

theorem componentIndex_eq_iff_between {N : ℕ} (G : PathEdges N)
    {i j : Fin N} (hij : i ≤ j) :
    componentIndex G i = componentIndex G j ↔
      ∀ e : Fin (N-1), i.val ≤ e.val → e.val < j.val → e ∈ G := by
  have hsub : (Finset.univ.filter fun e : Fin (N-1) => e.val < i.val ∧ e ∉ G) ⊆
      Finset.univ.filter fun e : Fin (N-1) => e.val < j.val ∧ e ∉ G := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    exact ⟨lt_of_lt_of_le he.1 hij, he.2⟩
  constructor
  · intro hc e hie hej
    by_contra hn
    have hs := Finset.eq_of_subset_of_card_le hsub (le_of_eq hc.symm)
    have he : e ∈ Finset.univ.filter (fun e : Fin (N-1) => e.val < j.val ∧ e ∉ G) :=
      by simp [hej, hn]
    rw [← hs] at he
    have he' := (Finset.mem_filter.mp he).2.1
    omega
  · intro h
    unfold componentIndex
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hei, hn⟩
      exact ⟨lt_of_lt_of_le hei hij, hn⟩
    · rintro ⟨hej, hn⟩
      refine ⟨?_, hn⟩
      by_contra hi
      exact hn (h e (by omega) hej)

theorem runLength_mono {N : ℕ} {G H : PathEdges N} (hGH : G ⊆ H) (i : Fin N) :
    runLength G i ≤ runLength H i := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, componentKey_eq_iff] at hj ⊢
  refine ⟨?_, hj.2⟩
  apply (componentIndex_eq_iff_between H hj.2).mpr
  intro e hje hei
  exact hGH ((componentIndex_eq_iff_between G hj.2).mp hj.1 e hje hei)

theorem runLength_le_componentSize {N : ℕ} (G : PathEdges N) (i : Fin N) :
    runLength G i ≤ (Finset.univ.filter fun j => componentKey G j = componentKey G i).card := by
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.1

theorem runLength_eq_one_of_no_predecessor {N : ℕ} (G : PathEdges N) (i : Fin N)
    (hi : ∀ e ∈ G, edgeRight e ≠ i) : runLength G i = 1 := by
  have hs : Finset.univ.filter (fun j => componentKey G j = componentKey G i ∧ j ≤ i) =
      {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hc, hji⟩
      by_contra hj
      have hlt : j < i := lt_of_le_of_ne hji hj
      let e : Fin (N-1) := ⟨i.val-1, by have := i.isLt; have : j.val < i.val := hlt; omega⟩
      have he : e ∈ G := (componentIndex_eq_iff_between G hji).mp
        ((componentKey_eq_iff G j i).mp hc) e (by dsimp [e]; omega) (by dsimp [e]; omega)
      exact hi e he (by apply Fin.ext; dsimp [edgeRight, e]; omega)
    · rintro rfl
      simp
  unfold runLength
  rw [hs, Finset.card_singleton]

def BoundedComponents {N : ℕ} (G : PathEdges N) (B : ℕ) : Prop :=
  ∀ c : Fin (N+1), (Finset.univ.filter fun i => componentKey G i = c).card ≤ B

/-- Stronger alternate path proof: only the components of `H` are bounded. -/
theorem boundedComponentFactorial {N B : ℕ} (G H : PathEdges N)
    (hH : BoundedComponents H B) :
    componentFactorial G * componentFactorial H ≤
      componentFactorial (G ∪ H) * B ^ (G ∩ H).card := by
  let S := (G ∩ H).image (edgeRight (N := N))
  have hpoint (i : Fin N) : runLength G i * runLength H i ≤
      runLength (G ∪ H) i * (if i ∈ S then B else 1) := by
    have hg := runLength_mono (Finset.subset_union_left (s₁ := G) (s₂ := H)) i
    have hh := runLength_mono (Finset.subset_union_right (s₁ := G) (s₂ := H)) i
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      exact Nat.mul_le_mul hg ((runLength_le_componentSize H i).trans (hH _))
    · rw [if_neg hi, mul_one]
      by_cases hp : ∃ e ∈ G, edgeRight e = i
      · obtain ⟨e, he, hei⟩ := hp
        have hnone : ∀ e' ∈ H, edgeRight e' ≠ i := by
          intro e' he' he'i
          have heq : e = e' := Fin.ext (by
            have hval := congrArg Fin.val (hei.trans he'i.symm)
            dsimp [edgeRight] at hval
            omega)
          apply hi
          exact Finset.mem_image.mpr ⟨e, Finset.mem_inter.mpr ⟨he, heq ▸ he'⟩, hei⟩
        rw [runLength_eq_one_of_no_predecessor H i hnone, mul_one]
        exact hg
      · have hnone : ∀ e ∈ G, edgeRight e ≠ i := by simpa using hp
        rw [runLength_eq_one_of_no_predecessor G i hnone, one_mul]
        exact hh
  have hprod := Finset.prod_le_prod (fun i _ => Nat.zero_le (runLength G i * runLength H i))
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) => hpoint i)
  simp only [Finset.prod_mul_distrib, ← componentFactorial_eq_runProduct] at hprod
  have hcard : S.card = (G ∩ H).card := by
    apply Finset.card_image_of_injective
    intro e e' he
    apply Fin.ext
    have hh := congrArg Fin.val he
    dsimp [edgeRight] at hh
    omega
  have hp : (∏ i : Fin N, if i ∈ S then B else 1) = B ^ S.card := by
    rw [← Finset.prod_filter]
    simp
  rwa [hp, hcard] at hprod

theorem boundedComponentOverlap_strong {N B : ℕ} (G H : PathEdges N)
    (hH : BoundedComponents H B) : overlap G H ≤ (B : ℝ) ^ (G ∩ H).card := by
  rw [overlapIdentity]
  apply (div_le_iff₀ (by exact_mod_cast componentFactorial_pos (G ∪ H))).mpr
  have h := boundedComponentFactorial G H hH
  exact_mod_cast (by simpa [mul_comm] using h)

/-- The frozen central-binomial constant follows from the stronger `B` bound. -/
theorem boundedComponentOverlap {N B : ℕ} (G H : PathEdges N) (hB : 2 ≤ B)
    (hH : BoundedComponents H B) :
    overlap G H ≤ (B.choose (B/2) : ℝ) ^ (G ∩ H).card := by
  apply (boundedComponentOverlap_strong G H hH).trans
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast (by simpa using Nat.choose_le_middle 1 B)

end RiffleUpperV2.GraphOverlap
