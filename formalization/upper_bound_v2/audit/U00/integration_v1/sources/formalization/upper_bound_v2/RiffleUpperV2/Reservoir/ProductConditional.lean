import RiffleUpperV2.Reservoir.ProductUniform
import RiffleUpperV2.Reservoir.Denominator

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

/-- Uniform regular/rare estimate for the actual marked-prefix marginal on
the concrete exposed-pile base. Every count and probability is model-derived. -/
theorem pileBase_tailPrefix_upper_uniform (g τ T : ℝ) (hg : 0<g) (hg1 : g<1)
    (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ k L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ D : ℕ, ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ e : Fin (pileSize cuts p) ↪ Fin n, ∀ A : Finset (Fin (pileSize cuts p)),
      ∀ a : Fin (pileSize cuts p) → Word k (L+1), (Finset.univ \ A).card≤2 →
      ∀ ω₀ : Sample cuts, pileBase cuts p e A a ω₀ → concentrationEvent cuts D g ξ ω₀ →
      ∀ E : ℕ, ∀ v : Word k (min E L),
      conditionalProbability (fixedCountPMF cuts)
        (fun ω => ∀ q, q∉A → tailPrefix E (tupleWords e ω q)=v)
        (pileBase cuts p e A a) ≤
      2^(Finset.univ \ A).card * (tailMass cuts E v)^(((Finset.univ \ A).card:ℝ)*
        (1-Real.log (1/g)/Real.log (1/τ))) := by
  obtain ⟨N0,hN01,hN0⟩ := residual_product_upper_uniform g τ T hg hg1 hτ hτg hT hα
  refine ⟨N0,hN01,?_⟩
  intro n hn k L hL cuts hn0 hgood D ξ p e A a hm ω₀ hreal hH E v
  have hap : ∀ q∈A, (a q).get 0=p := by
    intro q hq
    rw [← hreal.2 q hq]
    exact hreal.1 q
  rw [pileBase_tailPrefix_probability cuts p e A a ω₀ hreal.2 hap E v]
  simp_rw [residualCount_eq_remaining cuts p e A a ω₀ hreal]
  let M := (Finset.univ \ A).map e
  have hM : ∀ r∈M, (rowWord ω₀ r).get 0=p := by
    intro r hr
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hr
    exact hreal.1 q
  apply hN0 n hn (n-pileSize cuts p) (Finset.univ \ A).card
    (outsidePopulation_goodColumn cuts hn0 g hgood p) hm
    (Fin (min E L)) Finset.univ
    (fun r => (cuts.count ⟨r.val+1, by have := r.isLt; omega⟩ (v.get r):ℝ)/n)
    (fun r => remainingCount p M ⟨r.val+1, by have := r.isLt; omega⟩ (v.get r) ω₀)
  · simp only [Finset.card_univ,Fintype.card_fin]
    have hlen : ((min E L:ℕ):ℝ)≤((L+1:ℕ):ℝ) := by
      exact_mod_cast (Nat.min_le_right E L).trans (Nat.le_succ L)
    exact hlen.trans hL
  · intro r _
    refine ⟨by positivity,?_⟩
    apply (div_le_one (by exact_mod_cast hn0 : (0:ℝ)<n)).mpr
    exact_mod_cast GraphOverlap.count_le_population cuts _ (v.get r)
  · intro r _
    simpa only [M,Finset.card_map] using remainingCount_le_population cuts p M ω₀ hM
      (⟨r.val+1, by have := r.isLt; omega⟩ : Fin (L+1)) (v.get r)
  · intro r _
    have hn' : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn0)
    rw [mul_div_cancel₀ _ hn']
    exact_mod_cast remainingCount_le_cut cuts p M ω₀
      (⟨r.val+1, by have := r.isLt; omega⟩ : Fin (L+1)) (v.get r)
  · intro r _
    simpa only [M,Finset.card_map] using concentration_remainingCount cuts D g ξ p M ω₀ hH hM
      (⟨r.val+1, by have := r.isLt; omega⟩ : Fin (L+1)) (v.get r) (by simp)

end RiffleUpperV2.Reservoir
