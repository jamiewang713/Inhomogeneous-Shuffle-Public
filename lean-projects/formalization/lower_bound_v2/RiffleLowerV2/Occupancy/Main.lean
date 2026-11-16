import RiffleLowerV2.Occupancy.RarePair
import RiffleLowerV2.Occupancy.Nonrare
import RiffleLowerV2.Occupancy.Covariance
import Contracts.v1.AssemblyInputs

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleLowerV2.Occupancy
open TimeProfile

/-- The complete actual-model occupancy estimate; every mean regime is included. -/
theorem uniformOccupancy : Targets.UniformOccupancy := by
  intro c C hc hC
  obtain ⟨Dr,hDr,Nr,hNr2,hRare⟩ := rare_pair_relative_uniform c C hc hC
  obtain ⟨Nn,hNn2,hNonrare⟩ := nonrare_pair_relative c C hc hC
  obtain ⟨Nm,hNm2,hMarginal⟩ := uniform_marginal c C hc hC
  let D : ℝ := max Dr 128
  have hD : 0 < D := hDr.trans_le (le_max_left _ _)
  have hDrD : Dr ≤ D := le_max_left _ _
  have h128D : 128 ≤ D := le_max_right _ _
  refine ⟨D,hD,max Nr (max Nn Nm),?_⟩
  intro N hN k K hK cuts W hW
  have hNr : Nr ≤ N := (le_max_left _ _).trans hN
  have hNn : Nn ≤ N := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hN
  have hNm : Nm ≤ N := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hN
  have hNp : 0 < N := by omega
  have ht : 0 ≤ tau N := (tau_pos hNp).le
  have hmarg (w : Word k K) (hw : w ∈ W) :
      |probability (fixedCountPMF cuts) (collisionEvent w) -
        poissonCollision ((N : ℝ)*wordMass cuts w)| ≤
        D*tau N*poissonCollision ((N : ℝ)*wordMass cuts w) := by
    have hh := hMarginal N hNm k K hK cuts w (hW w hw)
    have hf := (poissonCollision_pos (wordMean_pos cuts w hc hNp (hW w hw))).le
    apply hh.trans
    gcongr
    linarith
  have hpair (w : Word k K) (hw : w ∈ W) (v : Word k K) (hv : v ∈ W) (hwv : w ≠ v) :
      |probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
        probability (fixedCountPMF cuts) (collisionEvent w)*probability (fixedCountPMF cuts) (collisionEvent v)| ≤
        D*tau N*probability (fixedCountPMF cuts) (collisionEvent w)*
          probability (fixedCountPMF cuts) (collisionEvent v) := by
    have hp := probability_nonneg (fixedCountPMF cuts) (collisionEvent w)
    have hq := probability_nonneg (fixedCountPMF cuts) (collisionEvent v)
    by_cases hwr : (N : ℝ)*wordMass cuts w ≤ tau N
    · exact (hRare N hNr k K hK cuts w v hwv (hW w hw) (hW v hv) hwr).trans
        (by gcongr)
    · by_cases hvr : (N : ℝ)*wordMass cuts v ≤ tau N
      · have hh := hRare N hNr k K hK cuts v w hwv.symm (hW v hv) (hW w hw) hvr
        have heq := probability_congr (fixedCountPMF cuts)
          (A := fun ω => collisionEvent v ω ∧ collisionEvent w ω)
          (B := fun ω => collisionEvent w ω ∧ collisionEvent v ω) (fun _ => and_comm)
        rw [heq] at hh
        have hh' : |probability (fixedCountPMF cuts) (fun ω => collisionEvent w ω ∧ collisionEvent v ω) -
            probability (fixedCountPMF cuts) (collisionEvent w)*probability (fixedCountPMF cuts) (collisionEvent v)| ≤
            Dr*tau N*probability (fixedCountPMF cuts) (collisionEvent w)*
              probability (fixedCountPMF cuts) (collisionEvent v) := by
          simpa only [mul_comm, mul_left_comm, mul_assoc] using hh
        exact hh'.trans (by gcongr)
      · exact (hNonrare N hNn k K hK cuts w v hwv (hW w hw) (hW v hv)
          (lt_of_not_ge hwr) (lt_of_not_ge hvr)).trans (by gcongr)
  exact ⟨hmarg,hpair,variance_collisionCount_le cuts W (D*tau N)
    (mul_nonneg hD.le ht) hpair⟩

/-- Explicit two-sided collision-count concentration from the proved actual law. -/
theorem collisionChebyshev : Targets.CollisionChebyshev := by
  intro c C hc hC
  obtain ⟨D,hD,N0,hOcc⟩ := uniformOccupancy c C hc hC
  refine ⟨D,hD,N0,?_⟩
  intro N hN k K hK cuts W hW t ht hmean
  exact chebyshev_of_variance_le (fixedCountPMF cuts) (collisionCount W)
    (D*(N : ℝ)^(-1/100 : ℝ)) t hmean ht (hOcc N hN k K hK cuts W hW).2.2

/-- In particular at least half the expected collision count is attained with
probability at least 1−4/EZ−4D N^(-1/100). -/
theorem collision_success :
    ∀ c C : ℝ, 0 < c → 0 < C → ∃ D : ℝ, 0 < D ∧ ∃ N0 : ℕ,
    ∀ N ≥ N0, ∀ k K : ℕ, (K : ℝ) ≤ C*logScale N →
    ∀ (cuts : Cuts k N K) (W : Finset (Word k K)), selectedPiles cuts W c →
    0 < expect (fixedCountPMF cuts) (collisionCount W) →
    1 - 4/expect (fixedCountPMF cuts) (collisionCount W) - 4*D*tau N ≤
      probability (fixedCountPMF cuts) (fun ω =>
        expect (fixedCountPMF cuts) (collisionCount W)/2 ≤ collisionCount W ω) := by
  intro c C hc hC
  obtain ⟨D,hD,N0,hOcc⟩ := uniformOccupancy c C hc hC
  refine ⟨D,hD,N0,?_⟩
  intro N hN k K hK cuts W hW hmean
  have hh := lower_tail_success (fixedCountPMF cuts) (collisionCount W)
    (D*tau N) (1/2) hmean (by norm_num) (hOcc N hN k K hK cuts W hW).2.2
  have hm : probability (fixedCountPMF cuts)
      (fun ω => (1-1/2)*expect (fixedCountPMF cuts) (collisionCount W) < collisionCount W ω) ≤
      probability (fixedCountPMF cuts)
      (fun ω => expect (fixedCountPMF cuts) (collisionCount W)/2 ≤ collisionCount W ω) := by
    apply probability_mono
    intro ω h
    linarith
  have hh' := hh.trans hm
  convert! hh' using 1
  field_simp
  ring

end RiffleLowerV2.Occupancy
