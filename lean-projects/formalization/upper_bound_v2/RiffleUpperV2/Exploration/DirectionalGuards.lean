import RiffleUpperV2.Exploration.GuardConcentration
import RiffleUpperV2.Exploration.ReserveExistence

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration

theorem tailBinMean_eq {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (D : ℕ) (p : Fin k) (v : Word k (min D L)) :
    prefixMean cuts (tailBinPrefix D p v) = pileSize cuts p * tailMass cuts D v := by
  unfold RiffleUpperV2.prefixMean RiffleLowerV2.prefixMean RiffleLowerV2.prefixMass tailBinPrefix
  rw [Fin.prod_univ_succ]
  simp only [List.Vector.get_cons_zero, List.Vector.get_cons_succ]
  change (n : ℝ)*((cuts.count 0 p : ℝ)/n * tailMass cuts D v) = _
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold pileSize
  field_simp

theorem guardMean_gap {k n L : ℕ} (cuts : Cuts k n (L+1)) (hn : 0 < n)
    (D : ℕ) (g : ℝ) (p : Fin k)
    (v : Word k (min D L) ×ₗ Word k (min D L) ×ₗ Word k (min D L))
    (hv : chosenReserves cuts D g = some v) :
    guardMean cuts D g p true - guardMean cuts D g p false =
      pileSize cuts p * tailMass cuts D v.2.1 := by
  have hbins : guardBins cuts D g true = insert v.2.1 (guardBins cuts D g false) := by
    ext w
    simp [guardBins, hv, le_iff_eq_or_lt]
  have hnot : v.2.1 ∉ guardBins cuts D g false := by simp [guardBins, hv]
  rw [guardMean_sum cuts hn, guardMean_sum cuts hn, hbins, Finset.sum_insert hnot,
    add_sub_cancel_right, tailBinMean_eq cuts hn]

/-- H yields strict interlacing of the guards in any two matrices. -/
theorem guards_interlace_on_concentration {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (hk : 1 ≤ k) (D : ℕ) {g ξ : ℝ} (hg : 0 < g)
    (hc : retainedGoodCluster cuts hn D g) (p : Fin k)
    (hp : (n : ℝ)^ξ ≤ pileSize cuts p) {ω ω' : Sample cuts}
    (h : concentrationEvent cuts D g ξ ω) (h' : concentrationEvent cuts D g ξ ω') :
    guardCount cuts D g p false ω < guardCount cuts D g p true ω' := by
  obtain ⟨v,hv⟩ := chosenReserves_of_retainedGoodCluster cuts hn hk D hg.le hc
  have hmass := (chosenReserves_spec cuts D g v hv).2.2.2.1
  have hnp : (0:ℝ) < pileSize cuts p := (Real.rpow_pos_of_pos (by exact_mod_cast hn) ξ).trans_le hp
  have hδ : 0 < reserveMass k D g * pileSize cuts p := mul_pos (reserveMass_pos (by omega) hg) hnp
  have hgap : reserveMass k D g*pileSize cuts p ≤ guardMean cuts D g p true-guardMean cuts D g p false := by
    rw [guardMean_gap cuts hn D g p v hv]
    nlinarith [mul_le_mul_of_nonneg_right hmass hnp.le]
  exact_mod_cast guard_interlace hδ hgap (h.2.2 p hp false) (h'.2.2 p hp true)

end RiffleUpperV2.Exploration
