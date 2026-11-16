import RiffleUpperV2.Reservoir.Counts

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Reservoir
open Exploration TimeProfile
attribute [local instance 2000] wordDecEq

theorem outsideCount_le_population {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (ω : Sample cuts) (j : Fin (L+1)) (d : Fin k) :
    outsideCount cuts p j d ω ≤ n-pileSize cuts p := by
  have hf : (Finset.univ.filter (fun r : Fin n => (rowWord ω r).get 0=p)).card=pileSize cuts p := by
    simpa only [RiffleLowerV2.rowWord_get,sampleEntry,pileSize] using (ω 0).property p
  have hh := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun r : Fin n => (rowWord ω r).get 0=p)
  rw [hf,Finset.card_univ,Fintype.card_fin] at hh
  have hb : outsideCount cuts p j d ω ≤ (Finset.univ.filter (fun r : Fin n => (rowWord ω r).get 0≠p)).card := by
    apply Finset.card_le_card
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2.1⟩
  have hh' : pileSize cuts p+(Finset.univ.filter (fun r : Fin n => (rowWord ω r).get 0≠p)).card=n := by
    simpa only [ne_eq] using hh
  omega

theorem remainingCount_le_population {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (M : Finset (Fin n)) (ω : Sample cuts) (hM : ∀ r∈M, (rowWord ω r).get 0=p)
    (j : Fin (L+1)) (d : Fin k) :
    remainingCount p M j d ω ≤ (n-pileSize cuts p)+M.card := by
  rw [remainingCount_eq cuts p M ω hM]
  exact Nat.add_le_add (outsideCount_le_population cuts p ω j d) (Finset.card_filter_le _ _)

theorem remainingCount_le_cut {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (M : Finset (Fin n)) (ω : Sample cuts) (j : Fin (L+1)) (d : Fin k) :
    remainingCount p M j d ω ≤ cuts.count j d := by
  have h : (Finset.univ.filter (fun r : Fin n => (rowWord ω r).get j=d)).card=cuts.count j d := by
    simpa only [RiffleLowerV2.rowWord_get,sampleEntry] using (ω j).property d
  rw [← h]
  apply Finset.card_le_card
  intro r hr
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2.2⟩

end RiffleUpperV2.Reservoir
