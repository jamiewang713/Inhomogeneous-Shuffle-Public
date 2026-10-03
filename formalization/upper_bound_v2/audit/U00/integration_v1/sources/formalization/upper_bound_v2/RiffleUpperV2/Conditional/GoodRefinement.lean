import RiffleUpperV2.Conditional.RefinedCylinders
import RiffleUpperV2.Exploration.WindowClusters

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Conditional
open Exploration TimeProfile

/-- The literal good-cluster conclusion at a prefix's refined tail start. -/
def goodRefinement {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (γ g : ℝ) (x : Prefix k (L+1)) (m : ℕ) : Prop :=
  ∃ a j c : Fin (L+1), a.val = x.1.val+m ∧ a < j ∧ j < c ∧
    c.val-a.val ≤ clusterSpan γ ∧ GoodColumn (cuts.profile hn a) g ∧
      GoodColumn (cuts.profile hn j) g ∧ GoodColumn (cuts.profile hn c) g

/-- Choose an actual nearby good triple for every prefix that has a full
refinement window available. Short terminal tails receive zero extra digits. -/
theorem goodRefinement_exists {k n L N : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    {ρ γ g : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hN : 1 ≤ N)
    (hlarge : 8 < γ*(ρ*Real.log (N : ℝ)))
    (hgood : integerWindowGood N cuts hn ρ γ g) (x : Prefix k (L+1)) :
    ∃ m : ℕ, x.1.val+m ≤ L+1 ∧ m ≤ windowLength N ρ ∧
      (x.1.val+windowLength N ρ ≤ L+1 → goodRefinement cuts hn γ g x m) ∧
      (L+1 < x.1.val+windowLength N ρ → m = 0) := by
  by_cases hx : x.1.val+windowLength N ρ ≤ L+1
  · obtain ⟨a,j,c,hxa,hcw,haj,hjc,hspan,hga,hgj,hgc⟩ :=
      integerWindow_cluster cuts hn hρ hγ hγ1 hN hlarge hgood x.1.val hx
    refine ⟨a.val-x.1.val, ?_, ?_, ?_, ?_⟩
    · have := a.isLt; omega
    · have haj' : a.val < j.val := haj
      have hjc' : j.val < c.val := hjc
      omega
    · intro _
      exact ⟨a,j,c,by omega,haj,hjc,hspan,hga,hgj,hgc⟩
    · intro h; omega
  · exact ⟨0,by have := x.1.isLt; omega,Nat.zero_le _,
      fun h => False.elim (hx h),fun _ => rfl⟩

/-- All depth choices are derived from the deterministic cut array. This
contains no history-dependent probability or supplied block-law premise. -/
theorem chooseGoodRefinement {k n L N : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    {ρ γ g : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hN : 1 ≤ N)
    (hlarge : 8 < γ*(ρ*Real.log (N : ℝ)))
    (hgood : integerWindowGood N cuts hn ρ γ g) (B : Finset (Prefix k (L+1))) :
    ∃ m : B → ℕ, (∀ x, x.val.1.val+m x ≤ L+1) ∧
      (∀ x, m x ≤ windowLength N ρ) ∧
      (∀ x, x.val.1.val+windowLength N ρ ≤ L+1 → goodRefinement cuts hn γ g x.val (m x)) ∧
      (∀ x, L+1 < x.val.1.val+windowLength N ρ → m x = 0) := by
  have h (x : B) := goodRefinement_exists cuts hn hρ hγ hγ1 hN hlarge hgood x.val
  choose m hm hb hg hs using h
  exact ⟨m,hm,hb,hg,hs⟩

/-- The threshold for choosing these depths precedes every array and prefix family. -/
theorem chooseGoodRefinement_uniform {ρ γ : ℝ}
    (hρ : 0 < ρ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ k n L : ℕ,
    ∀ cuts : Cuts k n (L+1), ∀ hn : 0 < n, ∀ g : ℝ,
    integerWindowGood N cuts hn ρ γ g → ∀ B : Finset (Prefix k (L+1)),
    ∃ m : B → ℕ, (∀ x, x.val.1.val+m x ≤ L+1) ∧
      (∀ x, m x ≤ windowLength N ρ) ∧
      (∀ x, x.val.1.val+windowLength N ρ ≤ L+1 → goodRefinement cuts hn γ g x.val (m x)) ∧
      (∀ x, L+1 < x.val.1.val+windowLength N ρ → m x = 0) := by
  obtain ⟨N0,hN0,hlarge⟩ := cluster_threshold_eventually hρ hγ
  refine ⟨N0,hN0,?_⟩
  intro N hN k n L cuts hn g hgood B
  exact chooseGoodRefinement cuts hn hρ.le hγ hγ1 (by omega) (hlarge N hN) hgood B

end RiffleUpperV2.Conditional
