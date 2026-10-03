import RiffleUpperV2.Exploration.Objects
import Mathlib.Combinatorics.Pigeonhole

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Exploration

/-- Finite cluster lemma. The harmless extra block avoids an integer-division endpoint case. -/
theorem goodCluster_finite (G : Finset ℕ) (m D : ℕ) (hD : 0 < D)
    (hG : ∀ j ∈ G, j < m) (hcard : 2 * (m / D + 1) < G.card) :
    ∃ a b c : ℕ, a ∈ G ∧ b ∈ G ∧ c ∈ G ∧ a < b ∧ b < c ∧ c-a ≤ D := by
  have hmap : ∀ j ∈ G, j / D ∈ Finset.range (m / D + 1) := by
    intro j hj
    apply Finset.mem_range.mpr
    have hh := Nat.div_le_div_right (Nat.le_of_lt (hG j hj)) (c := D)
    omega
  have hc : (Finset.range (m/D+1)).card * 2 < G.card := by
    simpa only [Finset.card_range, Nat.mul_comm] using hcard
  obtain ⟨q, _, hq⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmap hc
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp hq
  simp only [Finset.mem_filter] at ha hb hc
  have habound : q*D ≤ a ∧ a < q*D+D := by
    have hmod := Nat.mod_lt a hD
    have he := Nat.div_add_mod a D
    rw [ha.2, Nat.mul_comm D q] at he
    omega
  have hbbound : q*D ≤ b ∧ b < q*D+D := by
    have hmod := Nat.mod_lt b hD
    have he := Nat.div_add_mod b D
    rw [hb.2, Nat.mul_comm D q] at he
    omega
  have hcbound : q*D ≤ c ∧ c < q*D+D := by
    have hmod := Nat.mod_lt c hD
    have he := Nat.div_add_mod c D
    rw [hc.2, Nat.mul_comm D q] at he
    omega
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact ⟨a,b,c,ha.1,hb.1,hc.1,hab,hbc,by omega⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨a,c,b,ha.1,hc.1,hb.1,hac,hcb,by omega⟩
      · exact ⟨c,a,b,hc.1,ha.1,hb.1,hca,hab,by omega⟩
  · rcases lt_or_gt_of_ne hac with hac | hca
    · exact ⟨b,a,c,hb.1,ha.1,hc.1,hba,hac,by omega⟩
    · rcases lt_or_gt_of_ne hbc with hbc | hcb
      · exact ⟨b,c,a,hb.1,hc.1,ha.1,hbc,hca,by omega⟩
      · exact ⟨c,b,a,hc.1,hb.1,ha.1,hcb,hba,by omega⟩

/-- An explicit sufficient largeness threshold for the source counting argument. -/
theorem cluster_count_threshold {x γ : ℝ} (hx : 0 ≤ x) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hlarge : 8 < γ*x) :
    ((2 * ((⌈x⌉₊+1) / clusterSpan γ + 1) : ℕ) : ℝ) < γ*x-2 := by
  let m : ℕ := ⌈x⌉₊+1
  let D : ℕ := clusterSpan γ
  let q : ℕ := m/D
  have hm : (m : ℝ) < x+2 := by
    have hh := Nat.ceil_lt_add_one hx
    dsimp [m]
    push_cast
    linarith
  have hD : 6 ≤ γ*(D : ℝ) := by
    have hh : 6/γ ≤ (D : ℝ) := Nat.le_ceil _
    exact (div_le_iff₀ hγ).mp hh |>.trans_eq (mul_comm _ _)
  have hqm : (q : ℝ)*(D : ℝ) ≤ m := by
    exact_mod_cast (Nat.div_mul_le_self m D)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have h₁ := mul_le_mul_of_nonneg_left hD hq0
  have h₂ := mul_le_mul_of_nonneg_left hqm hγ.le
  have h₃ := mul_lt_mul_of_pos_left hm hγ
  change ((2 * (q+1) : ℕ) : ℝ) < γ*x-2
  push_cast
  nlinarith

/-- Source cluster counting with m=ceil(x)+1 and D=ceil(6/gamma).
The explicit condition 8<gamma*x is sufficient for 'all sufficiently large N'. -/
theorem goodCluster (G : Finset ℕ) {x γ : ℝ} (hx : 0 ≤ x) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hlarge : 8 < γ*x)
    (hG : ∀ j ∈ G, j < ⌈x⌉₊+1) (hcount : γ*x-2 ≤ (G.card : ℝ)) :
    ∃ a b c : ℕ, a ∈ G ∧ b ∈ G ∧ c ∈ G ∧ a < b ∧ b < c ∧ c-a ≤ clusterSpan γ := by
  have hD : 0 < clusterSpan γ := by
    unfold clusterSpan
    exact Nat.ceil_pos.mpr (by positivity)
  apply goodCluster_finite G (⌈x⌉₊+1) (clusterSpan γ) hD hG
  have hlt := (cluster_count_threshold hx hγ hγ1 hlarge).trans_le hcount
  exact_mod_cast hlt

end RiffleUpperV2.Exploration
