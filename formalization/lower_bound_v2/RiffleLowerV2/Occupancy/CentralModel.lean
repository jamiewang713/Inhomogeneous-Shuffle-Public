import RiffleLowerV2.Occupancy.CentralScales
import RiffleLowerV2.Occupancy.ModelInputs

noncomputable section
attribute [local instance] Classical.propDecidable

namespace RiffleLowerV2.Occupancy
open TimeProfile

/-- Absolute central marginal comparison for the actual fixed-column model. -/
theorem central_marginal_absolute (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ k K : ℕ,
      (K : ℝ) ≤ C*logScale N → ∀ (cuts : Cuts k N K) (w : Word k K),
      (∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) →
      (N : ℝ)*wordMass cuts w ≤ 2*centralBound N →
      |probability (fixedCountPMF cuts) (collisionEvent w) -
        poissonCollision ((N : ℝ)*wordMass cuts w)| ≤ A*(N : ℝ)^(-7/10 : ℝ) := by
  obtain ⟨D,hD,N1,hF⟩ := original_one_factorial_inputs c C hc hC
  obtain ⟨N2,hS⟩ := eventual_central_scales D C hD hC
  obtain ⟨N3,hE⟩ := eventual_central_error_bounds D C hD hC
  refine ⟨centralConstant D C, by unfold centralConstant; positivity, max N1 (max N2 N3), ?_⟩
  intro N hN k K hK cuts w hw hμB
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : N2 ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hN3 : N3 ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  obtain ⟨hNN,hL,hm2,heven,hmR,hR,hmlow,hmN,hbudget,hcube,he0,he1⟩ := hS N hN2
  have hμ : 0 < (N : ℝ)*wordMass cuts w := wordMean_pos cuts w hc (by omega) hw
  have hMom (r : ℕ) (hr : r ≤ bonferroniOrder N) :
      |expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) r) -
        ((N : ℝ)*wordMass cuts w)^r| ≤ momentError D C N*((N : ℝ)*wordMass cuts w)^r := by
    have hrR : r ≤ momentRadius N := by omega
    have hrR' : (r : ℝ) ≤ momentRadius N := by exact_mod_cast hrR
    have hh := hF N hN1 k K hK cuts w hw r (hrR'.trans hR)
    apply hh.trans
    unfold momentError
    gcongr
  have hcentral := Factorial.centralComparisonOne (Sample cuts) (fixedCountPMF cuts)
    (wordCount w) ((N : ℝ)*wordMass cuts w) (momentError D C N) (bonferroniOrder N)
    hμ he0 he1 hm2 heven hMom
  exact hcentral.trans ((hE N hN3).2 _ hμ.le hμB)

/-- Absolute two-category central comparison, retaining the actual joint law. -/
theorem central_pair_absolute (c C : ℝ) (hc : 0 < c) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∃ N0 : ℕ, ∀ N ≥ N0, ∀ k K : ℕ,
      (K : ℝ) ≤ C*logScale N → ∀ (cuts : Cuts k N K) (w v : Word k K), w ≠ v →
      (∀ j, c*N ≤ (cuts.count j (w.get j) : ℝ)) →
      (∀ j, c*N ≤ (cuts.count j (v.get j) : ℝ)) →
      (N : ℝ)*wordMass cuts w ≤ centralBound N →
      (N : ℝ)*wordMass cuts v ≤ centralBound N →
      |probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
        poissonCollision ((N : ℝ)*wordMass cuts w) * poissonCollision ((N : ℝ)*wordMass cuts v)| ≤
      A*(N : ℝ)^(-7/10 : ℝ) := by
  obtain ⟨D,hD,N1,hF⟩ := original_two_factorial_inputs c C hc hC
  obtain ⟨N2,hS⟩ := eventual_central_scales D C hD hC
  obtain ⟨N3,hE⟩ := eventual_central_error_bounds D C hD hC
  refine ⟨centralConstant D C, by unfold centralConstant; positivity, max N1 (max N2 N3), ?_⟩
  intro N hN k K hK cuts w v hwv hw hv hμB hνB
  have hN1 : N1 ≤ N := (le_max_left _ _).trans hN
  have hN2 : N2 ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hN3 : N3 ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  obtain ⟨hNN,hL,hm2,heven,hmR,hR,hmlow,hmN,hbudget,hcube,he0,he1⟩ := hS N hN2
  have hμ : 0 < (N : ℝ)*wordMass cuts w := wordMean_pos cuts w hc (by omega) hw
  have hν : 0 < (N : ℝ)*wordMass cuts v := wordMean_pos cuts v hc (by omega) hv
  have hMom (r s : ℕ) (hrs : r+s ≤ 2*bonferroniOrder N) :
      |expect (fixedCountPMF cuts) (fun ω => falling (wordCount w ω) r * falling (wordCount v ω) s) -
        ((N : ℝ)*wordMass cuts w)^r*((N : ℝ)*wordMass cuts v)^s| ≤
      momentError D C N * (((N : ℝ)*wordMass cuts w)^r*((N : ℝ)*wordMass cuts v)^s) := by
    have hrsR : r+s ≤ momentRadius N := hrs.trans hmR
    have hrsR' : ((r+s : ℕ) : ℝ) ≤ momentRadius N := by exact_mod_cast hrsR
    have hh := hF N hN1 k K hK cuts w v hwv hw hv r s (hrsR'.trans hR)
    apply hh.trans
    unfold momentError
    gcongr
  have hcentral := Factorial.centralComparison (Sample cuts) (fixedCountPMF cuts)
    (wordCount w) (wordCount v) ((N : ℝ)*wordMass cuts w) ((N : ℝ)*wordMass cuts v)
    (momentError D C N) (bonferroniOrder N) hμ hν he0 he1 hm2 heven
      (by intro r s hrs; simpa only [mul_assoc] using hMom r s hrs)
  exact hcentral.trans ((hE N hN3).1 _ _ hμ.le hμB hν.le hνB)

end RiffleLowerV2.Occupancy
