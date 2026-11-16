import RiffleUpperV2.Conditional.RemainingCover
import RiffleUpperV2.Conditional.GoodRefinement
import RiffleUpperV2.Conditional.LateTail
import RiffleUpperV2.Reservoir.SeparatedCylinders

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open Exploration TimeProfile Reservoir

/-- Concrete cylinder preparation from the integer-window assumption.
Every block is tiny or begins at an actual good triple; all constants precede
all models and all revealed histories. -/
theorem preparedFamily_exists (k : ℕ) (hk : 1≤k) (η ρ ξ γ : ℝ)
    (hρ : 0<ρ) (hγ : 0<γ) (hγ1 : γ≤1) (hgap : ξ<η-ρ*Real.log (k:ℝ)) :
    ∃N0:ℕ,2≤N0 ∧ ∀N:ℕ,N0≤N → ∀L:ℕ,∀T:ℝ,
      ((L+1:ℕ):ℝ)≤T*Real.log (N:ℝ) → ∀cuts:Cuts k N (L+1),∀hN:0<N,∀g:ℝ,
      integerWindowGood N cuts hN ρ γ g → empiricalBeta N 0 cuts hN (L+1)≤-η →
      ∀p:Fin k,∀d:Direction,∀s:Word k (L+1),s.get 0=p →
      ∃B:Finset (Prefix k (L+1)),
        (B.card:ℝ)≤(2*(k:ℝ)^3*T)*Real.log (N:ℝ)*(N:ℝ)^(ρ*Real.log (k:ℝ)) ∧
        (∀w:Word k (L+1),(w.get 0=p ∧ strictFuture d s w)↔∃x∈B,inCylinder x w) ∧
        (∀x∈B,0<x.1.val) ∧
        (∀x∈B,∀y∈B,x≠y → prefixSeparated x y) ∧
        (∀x∈B,prefixMean cuts x<(N:ℝ)^(-ξ) ∨ goodRefinement cuts hN γ g x 0) := by
  obtain ⟨N1,hN1,hchoose⟩ := chooseGoodRefinement_uniform hρ hγ hγ1
  obtain ⟨N2,hN2,hlate⟩ := lateShort_tiny_uniform k hk η ρ ξ hρ.le hgap
  refine ⟨max N1 N2,hN1.trans (le_max_left _ _),?_⟩
  intro N hNN L T hL cuts hN g hwindow hterminal p d s hs
  let B0 := pileFutureCylinders p d s hs
  obtain ⟨m,hm,hb,hgood,hshort⟩ := hchoose N ((le_max_left _ _).trans hNN) k N L cuts hN g hwindow B0
  let B := refineFamily B0 m hm
  refine ⟨B,refinedPileFuture_card hk (by omega) hρ.le hL p d s hs m hm hb,?_,?_,?_,?_⟩
  · exact refinedPileFuture_cover p d s hs m hm
  · intro x hx
    exact refinedPileFuture_depth_pos p d s hs m hm hx
  · intro x hx y hy hne
    constructor
    · intro hxy
      exact hne (refineFamily_antichain B0 m hm
        (fun x hx y hy hne => (pileFutureCylinders_antichain p d s hs hx hy hne).1) hx hy hxy)
    · intro hyx
      exact hne (refineFamily_antichain B0 m hm
        (fun x hx y hy hne => (pileFutureCylinders_antichain p d s hs hx hy hne).1) hy hx hyx).symm
  · intro y hy
    obtain ⟨x,_,hxy⟩ := Finset.mem_biUnion.mp hy
    have hlen := (refineCylinder_extension x.val (hm x) hxy).1
    by_cases hx : x.val.1.val+windowLength N ρ≤L+1
    · right
      obtain ⟨a,j,c,ha,haj,hjc,hspan,hga,hgj,hgc⟩ := hgood x hx
      exact ⟨a,j,c,by omega,haj,hjc,hspan,hga,hgj,hgc⟩
    · left
      have hm0 := hshort x (by omega)
      exact hlate N ((le_max_right _ _).trans hNN) N (L+1) cuts hN y (by omega) hterminal

end RiffleUpperV2.Conditional
