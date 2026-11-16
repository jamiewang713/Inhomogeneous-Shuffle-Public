import RiffleUpperV2.Reservoir.ReserveWeight
import RiffleUpperV2.Reservoir.Counts
import RiffleUpperV2.Exploration.ReserveExistence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile Filter

/-- A threshold fixed before the array absorbs the N^(2/3) count error and
both marked-row corrections. -/
theorem eventual_twoThirds_budget (B : ℝ) (hB : 0 < B) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ n : ℕ, N0 ≤ n →
      (n : ℝ)^((2:ℝ)/3)+5 ≤ B*n := by
  have he : ∀ᶠ n : ℕ in atTop, 6/B ≤ (n : ℝ)^((1:ℝ)/3) :=
    ((tendsto_rpow_atTop (by norm_num : 0 < (1:ℝ)/3)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp he
  refine ⟨max N0 1, le_max_right _ _, ?_⟩
  intro n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N0 1).trans hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hpow : 1 ≤ (n : ℝ)^((2:ℝ)/3) := Real.one_le_rpow hn1 (by norm_num)
  have hlow : 6 ≤ B*(n : ℝ)^((1:ℝ)/3) :=
    by simpa only [mul_comm] using (div_le_iff₀ hB).mp (hN0 n ((le_max_left _ _).trans hn))
  have heq : (n : ℝ)^((2:ℝ)/3)*(n : ℝ)^((1:ℝ)/3) = n := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hm := mul_le_mul_of_nonneg_left hlow
    (Real.rpow_nonneg hn0.le ((2:ℝ)/3))
  nlinarith

theorem outsidePopulation_goodColumn {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (g : ℝ) (hg : GoodColumn (cuts.profile hn 0) g) (p : Fin k) :
    g*n ≤ (n-pileSize cuts p : ℕ) := by
  obtain ⟨a,b,hab,ha,hb⟩ := hg
  have he : ∃ q : Fin k, q ≠ p ∧ g ≤ (cuts.count 0 q : ℝ)/n := by
    by_cases h : a=p
    · exact ⟨b, by intro hh; exact hab (h.trans hh.symm), hb⟩
    · exact ⟨a,h,ha⟩
  obtain ⟨q,hq,hqg⟩ := he
  have hsum : cuts.count 0 p + cuts.count 0 q ≤ n := by
    have hh := Finset.sum_le_univ_sum_of_nonneg (s := {p,q})
      (f := cuts.count 0) (fun _ => Nat.zero_le _)
    simpa [Finset.sum_pair (Ne.symm hq), cuts.sum_count] using hh
  have hqn : cuts.count 0 q ≤ n-pileSize cuts p := by unfold pileSize; omega
  exact ((le_div_iff₀ (by exact_mod_cast hn : (0:ℝ)<n)).mp hqg).trans
    (by exact_mod_cast hqn)

/-- Literal H gives the source reserve weight uniformly for every marked
set of size one or two. The prefix may be either chosen extreme reserve. -/
theorem reserve_tailWeight_finite {k n L D : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (hk : 0 < k) (hD : 1 ≤ D) (g ξ : ℝ) (hg : 0 < g)
    (p : Fin k) (M : Finset (Fin n)) (ω : Sample cuts)
    (hM : ∀ r ∈ M, (rowWord ω r).get 0 = p)
    (hm : M.card=1 ∨ M.card=2) (hH : concentrationEvent cuts D g ξ ω)
    (v : Word k (min D L)) (hv : reserveMass k D g ≤ tailMass cuts D v)
    (hc : 1 ≤ n-pileSize cuts p)
    (hbudget : (n : ℝ)^((2:ℝ)/3)+5 ≤
      (n-pileSize cuts p : ℕ)*(1/(4*(D : ℝ)))*reserveMass k D g) :
    (reserveMass k D g)^M.card/2 ≤
      ∏ r : Fin (min D L),
        RiffleLowerV2.falling (remainingCount p M ⟨r.val+1, by have := r.isLt; omega⟩ (v.get r) ω) M.card /
        RiffleLowerV2.falling ((n-pileSize cuts p)+M.card) M.card := by
  refine reserve_product_lower Finset.univ D (n-pileSize cuts p) M.card hD hc hm
    (by simp) (fun r : Fin (min D L) =>
      (cuts.count ⟨r.val+1, by have := r.isLt; omega⟩ (v.get r) : ℝ)/n)
    (fun r => remainingCount p M ⟨r.val+1, by have := r.isLt; omega⟩ (v.get r) ω)
    (reserveMass k D g) ((n : ℝ)^((2:ℝ)/3)) (reserveMass_pos hk hg) ?_ hv hbudget ?_
  · intro r _
    refine ⟨by positivity, ?_⟩
    apply (div_le_one (by exact_mod_cast hn : (0:ℝ)<n)).mpr
    have h := Finset.single_le_sum (f := cuts.count ⟨r.val+1, by have := r.isLt; omega⟩)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (v.get r))
    rw [cuts.sum_count] at h
    exact_mod_cast h
  · intro r _
    exact concentration_remainingCount cuts D g ξ p M ω hH hM _ _ (by simp)

/-- Constants precede n,L,cuts and the marked set. This produces the exact
uniform d0^m/2 quantitative reserve product from the actual H event. -/
theorem reserve_tailWeight_uniform (k D : ℕ) (hk : 0 < k) (hD : 1 ≤ D)
    (g : ℝ) (hg : 0 < g) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ n : ℕ, N0 ≤ n → ∀ L : ℕ,
      ∀ cuts : Cuts k n (L+1), ∀ hn : 0 < n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ M : Finset (Fin n), ∀ ω : Sample cuts,
      (∀ r ∈ M, (rowWord ω r).get 0 = p) → (M.card=1 ∨ M.card=2) →
      concentrationEvent cuts D g ξ ω → ∀ v : Word k (min D L),
      reserveMass k D g ≤ tailMass cuts D v →
      (reserveMass k D g)^M.card/2 ≤
        ∏ r : Fin (min D L),
          RiffleLowerV2.falling (remainingCount p M ⟨r.val+1, by have := r.isLt; omega⟩ (v.get r) ω) M.card /
          RiffleLowerV2.falling ((n-pileSize cuts p)+M.card) M.card := by
  have hd : 0 < reserveMass k D g := reserveMass_pos hk hg
  have hDp : (0:ℝ)<D := by exact_mod_cast (by omega : 0<D)
  obtain ⟨N0,hN01,hN0⟩ := eventual_twoThirds_budget (g*(1/(4*(D:ℝ)))*reserveMass k D g) (by positivity)
  refine ⟨N0,hN01,?_⟩
  intro n hn L cuts hn0 hgood ξ p M ω hM hm hH v hv
  have hc : g*n ≤ (n-pileSize cuts p : ℕ) := outsidePopulation_goodColumn cuts hn0 g hgood p
  have hcp : 1 ≤ n-pileSize cuts p := by
    have hpos : (0:ℝ)<(n-pileSize cuts p : ℕ) := lt_of_lt_of_le (by positivity) hc
    exact Nat.succ_le_of_lt (by exact_mod_cast hpos)
  apply reserve_tailWeight_finite cuts hn0 hk hD g ξ hg p M ω hM hm hH v hv hcp
  calc
    _ ≤ (g*(1/(4*(D:ℝ)))*reserveMass k D g)*n := hN0 n hn
    _ = (g*n)*(1/(4*(D:ℝ)))*reserveMass k D g := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (by positivity)) hd.le

end RiffleUpperV2.Reservoir
