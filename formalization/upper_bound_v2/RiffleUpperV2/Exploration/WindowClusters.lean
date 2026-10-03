import RiffleUpperV2.Exploration.Clusters
import RiffleUpperV2.Exploration.LocalGood
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exploration
open TimeProfile Filter

/-- The finite cluster theorem instantiated in an arbitrary actual integer window. -/
theorem integerWindow_cluster {k n L N : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    {ρ γ g : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hN : 1 ≤ N)
    (hlarge : 8 < γ*(ρ*Real.log (N : ℝ)))
    (hgood : integerWindowGood N cuts hn ρ γ g) (b : ℕ)
    (hb : b+windowLength N ρ ≤ L+1) :
    ∃ a j c : Fin (L+1), b ≤ a.val ∧ c.val < b+windowLength N ρ ∧
      a < j ∧ j < c ∧ c.val-a.val ≤ clusterSpan γ ∧
      GoodColumn (cuts.profile hn a) g ∧ GoodColumn (cuts.profile hn j) g ∧ GoodColumn (cuts.profile hn c) g := by
  let J := Finset.univ.filter fun j : Fin (L+1) => b ≤ j.val ∧
    j.val < b+windowLength N ρ ∧ GoodColumn (cuts.profile hn j) g
  let G := J.image (fun j => j.val-b)
  have hcard : G.card = J.card := Finset.card_image_iff.mpr (by
    intro i hi j hj hij
    have hi' := (Finset.mem_filter.mp hi).2.1
    have hj' := (Finset.mem_filter.mp hj).2.1
    apply Fin.ext
    change i.val-b = j.val-b at hij
    omega)
  have hG : ∀ t ∈ G, t < ⌈ρ*Real.log (N : ℝ)⌉₊+1 := by
    intro t ht
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    have hmem := (Finset.mem_filter.mp hj).2
    change b ≤ j.val ∧ j.val < b+(⌈ρ*Real.log (N : ℝ)⌉₊+1) ∧ _ at hmem
    omega
  have hcount : γ*(ρ*Real.log (N : ℝ))-2 ≤ (G.card : ℝ) := by
    rw [hcard]
    simpa only [mul_assoc] using hgood b hb
  have hx : 0 ≤ ρ*Real.log (N : ℝ) := mul_nonneg hρ (Real.log_nonneg (by exact_mod_cast hN))
  obtain ⟨a,j,c,ha,hj,hc,haj,hjc,hspan⟩ := goodCluster G hx hγ hγ1 hlarge hG hcount
  obtain ⟨a',ha',hea⟩ := Finset.mem_image.mp ha
  obtain ⟨j',hj',hej⟩ := Finset.mem_image.mp hj
  obtain ⟨c',hc',hec⟩ := Finset.mem_image.mp hc
  have hma := (Finset.mem_filter.mp ha').2
  have hmj := (Finset.mem_filter.mp hj').2
  have hmc := (Finset.mem_filter.mp hc').2
  refine ⟨a',j',c',hma.1,hmc.2.1,?_,?_,?_,hma.2.2,hmj.2.2,hmc.2.2⟩ <;> omega

/-- The logarithmic counting threshold is fixed before all arrays and windows. -/
theorem cluster_threshold_eventually {ρ γ : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → 8 < γ*(ρ*Real.log (N : ℝ)) := by
  have ht : Tendsto (fun N : ℕ => γ*ρ*Real.log (N : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (mul_pos hγ hρ)).mpr
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp (ht.eventually_gt_atTop 8)
  refine ⟨max N0 2,le_max_right _ _,?_⟩
  intro N hN
  simpa only [mul_assoc] using hN0 N ((le_max_left _ _).trans hN)

/-- Every fitting integer window has a bounded-span good triple, uniformly in cuts. -/
theorem goodCluster_uniform {ρ γ : ℝ} (hρ : 0 < ρ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ N0 : ℕ, ∃ hN0 : 2 ≤ N0, ∀ (N : ℕ) (hN : N0 ≤ N),
      ∀ k n L : ℕ, ∀ cuts : Cuts k n (L+1), ∀ hn : 0 < n, ∀ g : ℝ,
      integerWindowGood N cuts hn ρ γ g → ∀ b : ℕ, b+windowLength N ρ ≤ L+1 →
      ∃ a j c : Fin (L+1), b ≤ a.val ∧ c.val < b+windowLength N ρ ∧
        a < j ∧ j < c ∧ c.val-a.val ≤ clusterSpan γ ∧
        GoodColumn (cuts.profile hn a) g ∧ GoodColumn (cuts.profile hn j) g ∧ GoodColumn (cuts.profile hn c) g := by
  obtain ⟨N0,hN0,ht⟩ := cluster_threshold_eventually hρ hγ
  refine ⟨N0,hN0,?_⟩
  intro N hN k n L cuts hn g hgood b hb
  exact integerWindow_cluster cuts hn hρ.le hγ hγ1 (by omega) (ht N hN) hgood b hb

end RiffleUpperV2.Exploration
