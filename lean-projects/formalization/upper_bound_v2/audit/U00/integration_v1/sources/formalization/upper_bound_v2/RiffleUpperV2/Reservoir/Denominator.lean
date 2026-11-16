import RiffleUpperV2.Reservoir.PilePrefix
import RiffleUpperV2.Reservoir.ReserveUniform

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem conditionalProbability_mono_on {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E F B : Ω → Prop) (h : ∀ ω, B ω → E ω → F ω) :
    conditionalProbability P E B ≤ conditionalProbability P F B := by
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  apply div_le_div_of_nonneg_right
  · exact RiffleLowerV2.Thinning.probability_mono P (fun ω hh => ⟨h ω hh.2 hh.1,hh.2⟩)
  · exact RiffleLowerV2.Thinning.probability_nonneg P B

/-- The literal natural-history denominator contains every right-reserve
completion of the marked rows whenever the deleted rows leave the history
satisfied. Its mass is computed by the actual residual law. -/
theorem history_denominator_ge_reserveWeight {k n L D : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (g : ℝ) (e : Fin (pileSize cuts p) ↪ Fin n)
    (ω : Sample cuts) (j : Fin (pileSize cuts p)) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1))
    (ω₀ : Sample cuts) (hreal : pileBase cuts p e A a ω₀)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g=some v)
    (hd : hasDirection cuts D g .forward (pileWords cuts p ω j))
    (ha : unmarkedHistoryConstraint cuts p ω j A a) :
    (∏ r : Fin (min D L), RiffleLowerV2.falling
      (remainingCount p ((Finset.univ \ A).map e) ⟨r.val+1, by have := r.isLt; omega⟩ (v.2.2.get r) ω₀)
        (Finset.univ \ A).card /
      RiffleLowerV2.falling ((n-pileSize cuts p)+(Finset.univ \ A).card) (Finset.univ \ A).card) ≤
    conditionalProbability (fixedCountPMF cuts) (historyFiber cuts p .forward (j.val+1) ω)
      (pileBase cuts p e A a) := by
  have hp := pileBase_tailPrefix_probability cuts p e A a ω₀ hreal.2 ha.1 D v.2.2
  simp_rw [residualCount_eq_remaining cuts p e A a ω₀ hreal] at hp
  rw [← hp]
  apply conditionalProbability_mono_on
  intro w hB hE
  have hh := chosenReserve_tuple_allowed cuts p g ω j A a (tupleWords e w) v hv hd ha hB.2 hB.1 hE
  exact ((tupleHistoryConstraint_iff cuts p e ω w j).mp hh).2

/-- Quantitative reserve normalization for the actual natural history. All
capacities come from one realization of the literal H event; m is one or two. -/
theorem history_denominator_lower_finite {k n L D : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0<n) (hk : 0<k) (hD : 1≤D) (p : Fin k) (g ξ : ℝ) (hg : 0<g)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (A : Finset (Fin (pileSize cuts p))) (a : Fin (pileSize cuts p) → Word k (L+1))
    (hm : (Finset.univ \ A).card=1 ∨ (Finset.univ \ A).card=2)
    (ω₀ : Sample cuts) (hreal : pileBase cuts p e A a ω₀)
    (hH : concentrationEvent cuts D g ξ ω₀)
    (hc : 1≤n-pileSize cuts p)
    (hbudget : (n : ℝ)^((2:ℝ)/3)+5 ≤
      (n-pileSize cuts p : ℕ)*(1/(4*(D : ℝ)))*reserveMass k D g)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g=some v)
    (hd : hasDirection cuts D g .forward (pileWords cuts p ω j))
    (ha : unmarkedHistoryConstraint cuts p ω j A a) :
    (reserveMass k D g)^(Finset.univ \ A).card/2 ≤
    conditionalProbability (fixedCountPMF cuts) (historyFiber cuts p .forward (j.val+1) ω)
      (pileBase cuts p e A a) := by
  have hM : ∀ r∈(Finset.univ \ A).map e, (rowWord ω₀ r).get 0=p := by
    intro r hr
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hr
    exact hreal.1 q
  have hh := reserve_tailWeight_finite cuts hn hk hD g ξ hg p ((Finset.univ \ A).map e)
    ω₀ hM (by simpa using hm) hH v.2.2 (chosenReserves_spec cuts D g v hv).2.2.2.2 hc hbudget
  simp only [Finset.card_map] at hh
  exact hh.trans (history_denominator_ge_reserveWeight cuts p g e ω j A a ω₀ hreal v hv hd ha)

/-- The reserve denominator bound is uniform before the array, history,
labeled pile and exposed configuration are chosen. A realization of H in
the exposed fiber supplies all residual-count hypotheses. -/
theorem history_denominator_lower_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g : ℝ) (hg : 0<g) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ e : Fin (pileSize cuts p) ↪ Fin n, ∀ ω : Sample cuts,
      ∀ j : Fin (pileSize cuts p), ∀ A : Finset (Fin (pileSize cuts p)),
      ∀ a : Fin (pileSize cuts p) → Word k (L+1),
      ((Finset.univ \ A).card=1 ∨ (Finset.univ \ A).card=2) →
      ∀ ω₀ : Sample cuts, pileBase cuts p e A a ω₀ → concentrationEvent cuts D g ξ ω₀ →
      ∀ v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L),
      chosenReserves cuts D g=some v →
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      unmarkedHistoryConstraint cuts p ω j A a →
      (reserveMass k D g)^(Finset.univ \ A).card/2 ≤
      conditionalProbability (fixedCountPMF cuts) (historyFiber cuts p .forward (j.val+1) ω)
        (pileBase cuts p e A a) := by
  obtain ⟨N0,hN01,hN0⟩ := reserve_tailWeight_uniform k D hk hD g hg
  refine ⟨N0,hN01,?_⟩
  intro n hn L cuts hn0 hgood ξ p e ω j A a hm ω₀ hreal hH v hv hd ha
  have hM : ∀ r∈(Finset.univ \ A).map e, (rowWord ω₀ r).get 0=p := by
    intro r hr
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hr
    exact hreal.1 q
  have hh := hN0 n hn L cuts hn0 hgood ξ p ((Finset.univ \ A).map e) ω₀ hM
    (by simpa using hm) hH v.2.2 (chosenReserves_spec cuts D g v hv).2.2.2.2
  simp only [Finset.card_map] at hh
  exact hh.trans (history_denominator_ge_reserveWeight cuts p g e ω j A a ω₀ hreal v hv hd ha)

end RiffleUpperV2.Reservoir
