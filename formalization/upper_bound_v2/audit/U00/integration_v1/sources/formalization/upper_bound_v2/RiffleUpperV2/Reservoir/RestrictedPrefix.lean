import RiffleUpperV2.Reservoir.ProductConditional

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem pileBase_probability_pos {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (A : Finset (Fin (pileSize cuts p)))
    (a : Fin (pileSize cuts p) → Word k (L+1)) (ω : Sample cuts)
    (h : pileBase cuts p e A a ω) : 0<probability (fixedCountPMF cuts) (pileBase cuts p e A a) := by
  have hh := tupleWords_event_positive cuts e
    (fun w => (∀ q, (w q).get 0=p) ∧ ∀ q∈A, w q=a q) ω h
  rw [← tupleWords_event] at hh
  exact hh

theorem conditionalProbability_restrict_le {Ω : Type*} [Fintype Ω] (P : PMF Ω)
    (E B H : Ω → Prop) {b d : ℝ} (hB : probability P B≠0) (hd : 0<d)
    (hden : d≤conditionalProbability P H B) (hnum : conditionalProbability P E B≤b) :
    conditionalProbability P E (fun ω => B ω ∧ H ω) ≤ b/d := by
  rw [conditionalProbability_refine P E B H hB]
  have hnonneg : 0≤conditionalProbability P (fun ω => E ω ∧ H ω) B :=
    div_nonneg (RiffleLowerV2.Thinning.probability_nonneg P _)
      (RiffleLowerV2.Thinning.probability_nonneg P _)
  have hn : conditionalProbability P (fun ω => E ω ∧ H ω) B≤b :=
    (conditionalProbability_mono_on P _ _ B (fun _ _ h => h.1)).trans hnum
  exact (div_le_div_of_nonneg_left hnonneg hd hden).trans
    (div_le_div_of_nonneg_right hn hd.le)

/-- If removing strictly future marked words fails the observed count
constraint, the target is impossible, including null conditional fibers. -/
theorem history_future_impossible {k n L E : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p) ↪ Fin n) (ω : Sample cuts) (j : Fin (pileSize cuts p))
    (A : Finset (Fin (pileSize cuts p))) (a : Fin (pileSize cuts p) → Word k (L+1))
    (v : Word k (min E L))
    (hfuture : ∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → pileWords cuts p ω j<w)
    (ha : ¬unmarkedHistoryConstraint cuts p ω j A a) :
    conditionalProbability (fixedCountPMF cuts)
      (fun z => ∀ q, q∉A → tailPrefix E (tupleWords e z q)=v)
      (fun z => pileBase cuts p e A a z ∧ historyFiber cuts p .forward (j.val+1) ω z)=0 := by
  have himp (z : Sample cuts) : ¬((∀ q, q∉A → tailPrefix E (tupleWords e z q)=v) ∧
      pileBase cuts p e A a z ∧ historyFiber cuts p .forward (j.val+1) ω z) := by
    rintro ⟨hE,hB,hH⟩
    have hconstraint := (tupleHistoryConstraint_iff cuts p e ω z j).mpr ⟨hB.1,hH⟩
    apply ha
    exact (tupleHistoryConstraint_future_iff cuts p ω j A a (tupleWords e z)
      hB.2 hB.1 (fun q hq => hfuture _ (hB.1 q) (hE q hq))).mp hconstraint
  unfold conditionalProbability RiffleLowerV2.conditionalProbability
  have he : (fun z : Sample cuts => (∀ q, q∉A → tailPrefix E (tupleWords e z q)=v) ∧
      pileBase cuts p e A a z ∧ historyFiber cuts p .forward (j.val+1) ω z) = fun _ => False := by
    funext z
    exact propext (iff_false_intro (himp z))
  rw [he]
  simp only [RiffleLowerV2.probability,RiffleLowerV2.expect,if_false,mul_zero,Finset.sum_const_zero,zero_div]

/-- The complete good-fiber marked-prefix bound under literal natural
history and unmarked-row conditioning. The allowed-set denominator and
regular/rare numerator are both derived from the actual fixed-count law. -/
theorem history_prefixProbability_upper_uniform (k D : ℕ) (hk : 0<k) (hD : 1≤D)
    (g τ T : ℝ) (hg : 0<g) (hg1 : g<1) (hτ : 0<τ) (hτg : τ<g) (hT : 0<T)
    (hα : Real.log (1/g)/Real.log (1/τ)<1) :
    ∃ N0 : ℕ, 1≤N0 ∧ ∀ n : ℕ, N0≤n → ∀ L : ℕ,
      ((L+1:ℕ):ℝ)≤T*Real.log (n:ℝ) → ∀ cuts : Cuts k n (L+1), ∀ hn : 0<n,
      GoodColumn (cuts.profile hn 0) g → ∀ ξ : ℝ, ∀ p : Fin k,
      ∀ e : Fin (pileSize cuts p) ↪ Fin n, ∀ ω : Sample cuts, ∀ j : Fin (pileSize cuts p),
      hasDirection cuts D g .forward (pileWords cuts p ω j) →
      ∀ A : Finset (Fin (pileSize cuts p)), ∀ a : Fin (pileSize cuts p) → Word k (L+1),
      ((Finset.univ \ A).card=1 ∨ (Finset.univ \ A).card=2) →
      ∀ ω₀ : Sample cuts, pileBase cuts p e A a ω₀ → concentrationEvent cuts D g ξ ω₀ →
      ∀ E : ℕ, ∀ v : Word k (min E L),
      (∀ w : Word k (L+1), w.get 0=p → tailPrefix E w=v → pileWords cuts p ω j<w) →
      conditionalProbability (fixedCountPMF cuts)
        (fun z => ∀ q, q∉A → tailPrefix E (tupleWords e z q)=v)
        (fun z => pileBase cuts p e A a z ∧ historyFiber cuts p .forward (j.val+1) ω z) ≤
      (2^(Finset.univ \ A).card * (tailMass cuts E v)^(((Finset.univ \ A).card:ℝ)*
        (1-Real.log (1/g)/Real.log (1/τ)))) / ((reserveMass k D g)^(Finset.univ \ A).card/2) := by
  obtain ⟨N₁,hN₁1,hN₁⟩ := history_denominator_lower_uniform k D hk hD g hg
  obtain ⟨N₂,hN₂1,hN₂⟩ := pileBase_tailPrefix_upper_uniform g τ T hg hg1 hτ hτg hT hα
  refine ⟨max N₁ N₂, hN₁1.trans (le_max_left _ _), ?_⟩
  intro n hn L hL cuts hn0 hgood ξ p e ω j hdir A a hm ω₀ hreal hH E v hfuture
  have hnum := hN₂ n ((le_max_right _ _).trans hn) k L hL cuts hn0 hgood D ξ p e A a
    (by rcases hm with h | h <;> omega) ω₀ hreal hH E v
  by_cases ha : unmarkedHistoryConstraint cuts p ω j A a
  · have hex : ∃ v, chosenReserves cuts D g=some v := by
      cases hv : chosenReserves cuts D g with
      | none => simp only [hasDirection,hv] at hdir
      | some v => exact ⟨v,rfl⟩
    obtain ⟨v',hv'⟩ := hex
    exact conditionalProbability_restrict_le _ _ _ _
      (ne_of_gt (pileBase_probability_pos cuts p e A a ω₀ hreal))
      (by exact div_pos (pow_pos (reserveMass_pos hk hg) _) (by norm_num))
      (hN₁ n ((le_max_left _ _).trans hn) L cuts hn0 hgood ξ p e ω j A a hm ω₀ hreal hH
        v' hv' hdir ha) hnum
  · rw [history_future_impossible cuts p e ω j A a v hfuture ha]
    unfold tailMass reserveMass
    positivity

end RiffleUpperV2.Reservoir
