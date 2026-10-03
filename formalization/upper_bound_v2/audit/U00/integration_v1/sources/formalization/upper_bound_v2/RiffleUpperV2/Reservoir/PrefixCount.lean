import RiffleUpperV2.Reservoir.NaturalAveraging
import RiffleUpperV2.Reservoir.TupleCounting
import RiffleUpperV2.Reservoir.Normalization

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem pileTailMass_eq_prefixMass {k n L E : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (v : Word k (min E L)) :
    ((pileSize cuts p:ℝ)/n)*tailMass cuts E v=RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v) := by
  unfold RiffleUpperV2.prefixMass RiffleLowerV2.prefixMass tailBinPrefix
  rw [Fin.prod_univ_succ]
  simp only [List.Vector.get_cons_zero,List.Vector.get_cons_succ]
  rfl

/-- Actual natural-history factorial count estimate, with the bad event
charged once for each ordered marked tuple and the exact pile factor kept. -/
theorem natural_prefixFactorial_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, 0≤ε → ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .forward (j.val+1) ω →
      historyGood cuts D g ξ ε p .forward (j.val+1) ω →
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      ∀ m : ℕ, (m=1 ∨ m=2) → ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → pileWords cuts p ω j<w) →
      conditionalExpect (fixedCountPMF cuts) (fun z => RiffleLowerV2.falling (pileTailCount p v z) m)
        (historyFiber cuts p .forward (j.val+1) ω) ≤
      (2^m/((reserveMass k D g)^m/2))*(n:ℝ)^m*
        (RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v))^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))+
        (n:ℝ)^m*ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_marked_good_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir m hm E v hfuture
  let H := historyFiber cuts p .forward (j.val+1) ω
  let b : ℝ := (2^m*(tailMass cuts E v)^((m:ℝ)*(1-Real.log (1/g)/Real.log (1/τ)))) /
    ((reserveMass k D g)^m/2)
  have hb : ∀ f : Fin m ↪ Fin n,
      conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v) H ≤
        b*conditionalProbability (fixedCountPMF cuts) (markedPileEvent p f) H+ε := by
    intro f
    exact (natural_marked_probability_good_bad cuts D g ξ ε p f ω (j.val+1) v hhistory).trans
      (add_le_add (hN0 n hn L hL cuts hn0 hgood ξ p ω j hpos hdir m hm f E v hfuture) le_rfl)
  have hsum := Finset.sum_le_sum (fun f (_ : f∈Finset.univ) => hb f)
  rw [Finset.sum_add_distrib,← Finset.mul_sum,sum_markedPile_conditionalProbability cuts p H hpos,
    Finset.sum_const,Finset.card_univ,Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have hcount : conditionalExpect (fixedCountPMF cuts)
      (fun z => RiffleLowerV2.falling (pileTailCount p v z) m) H =
      ∑ f : Fin m ↪ Fin n, conditionalProbability (fixedCountPMF cuts) (markedTailEvent p f v) H := by
    rw [← conditionalExpect_sum_marked]
    congr 1
    funext z
    exact (sum_markedTail_indicators cuts p v z).symm
  rw [hcount]
  apply hsum.trans
  have hnorm := initialPile_normalization (m := m) hn0
    (show pileSize cuts p≤n by have := pileOffset_add_size_le cuts p; omega)
    (q := tailMass cuts E v) (by unfold tailMass; positivity)
    (rareExponent_nonneg hg hg1 hτ (hτg.trans hg1)) hα.le
  rw [pileTailMass_eq_prefixMass] at hnorm
  have hcoef : 0≤(2:ℝ)^m/((reserveMass k D g)^m/2) := by unfold reserveMass; positivity
  have hmain := mul_le_mul_of_nonneg_left hnorm hcoef
  have hfall : (n.descFactorial m:ℝ)≤(n:ℝ)^m := by exact_mod_cast Nat.descFactorial_le_pow n m
  have herr := mul_le_mul_of_nonneg_right hfall hε
  convert add_le_add hmain herr using 1 <;> (try dsimp only [b]) <;> ring

/-- The source conditional cylinder-count estimate for every positive
forward natural history. Constants are fixed before the cut array. -/
theorem prefixCount (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1/2) :
    ∃ C1 : ℝ, 0<C1 ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ ε : ℝ, 0≤ε → ∀ p : Fin k,
      ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      positiveHistory cuts p .forward (j.val+1) ω →
      historyGood cuts D g ξ ε p .forward (j.val+1) ω →
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → pileWords cuts p ω j<w) →
      conditionalExpect (fixedCountPMF cuts)
        (fun z => (RiffleUpperV2.prefixCount (tailBinPrefix E p v) z:ℝ))
        (historyFiber cuts p .forward (j.val+1) ω) ≤
        C1*n*(RiffleUpperV2.prefixMass cuts (tailBinPrefix E p v))^(1-Real.log (1/g)/Real.log (1/τ)) + n*ε := by
  obtain ⟨N0,hN01,hN0⟩ := natural_prefixFactorial_upper_uniform k D hk hD g τ T hg hg1 hτ hτg hT (by linarith)
  refine ⟨2/(reserveMass k D g/2),by exact div_pos (by norm_num) (div_pos (reserveMass_pos hk hg) (by norm_num)),N0,hN01,?_⟩
  intro n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir E v hfuture
  have hh := hN0 n hn L hL cuts hn0 hgood ξ ε hε p ω j hpos hhistory hdir 1 (Or.inl rfl) E v hfuture
  have he (z : Sample cuts) : pileTailCount p v z=RiffleUpperV2.prefixCount (tailBinPrefix E p v) z := by
    rw [← tailBinCount_prefix cuts E p v z]
    unfold pileTailCount tailBinCount
    congr 1
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  simpa only [RiffleLowerV2.falling,Nat.descFactorial_one,he,pow_one,Nat.cast_one,one_mul] using hh

end RiffleUpperV2.Reservoir
