import RiffleUpperV2.FirstMoment.FirstColumn
import RiffleUpperV2.FirstMoment.Exponents
import RiffleUpperV2.FirstMoment.Entropy

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Hypergeometric

/-- Removing the exposed coordinate only reindexes the remaining grid; original
N and the full population n are unchanged. -/
theorem gridSum_tail {N d : ℕ} (f : Fin (d+1) → ℝ) (a s u : ℕ) (hs : a+1 ≤ s) :
    RiffleLowerV2.gridSum N (fun j : Fin d => f j.succ) (s-(a+1)) (u-(a+1)) =
      RiffleLowerV2.gridSum N f (s-a) (u-a) := by
  classical
  unfold RiffleLowerV2.gridSum
  congr 1
  apply Finset.sum_bij (fun j _ => j.succ)
  · intro j hj
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
    change s-a ≤ j.val+1 ∧ j.val+1 < u-a
    omega
  · intro j _ j' _ he
    exact Fin.succ_injective _ he
  · intro j hj
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj
    refine ⟨⟨j.val-1,by omega⟩,?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    · apply Fin.ext
      simp only [Fin.val_succ]
      omega
  · intro j _
    rfl

theorem empiricalB_tailCuts {k n d N : ℕ} (cuts : Cuts k n (d+1)) (hn : 0 < n)
    (a s u : ℕ) (hs : a+1 ≤ s) (theta : ℝ) :
    empiricalB N (a+1) (tailCuts cuts) hn theta s u = empiricalB N a cuts hn theta s u := by
  exact gridSum_tail (fun j => psi (cuts.profile hn j) theta) a s u hs

theorem empiricalA_tailCuts {k n d N : ℕ} (cuts : Cuts k n (d+1)) (hn : 0 < n)
    (a s u : ℕ) (hs : a+1 ≤ s) :
    empiricalA N (a+1) (tailCuts cuts) hn s u = empiricalA N a cuts hn s u := by
  exact gridSum_tail (fun j => maxCost (cuts.profile hn j)) a s u hs

/-- Selected future-column psi sums equal the original-array interval cost. -/
theorem selectedPsi_eq_originalB {k n d N : ℕ} (cuts : Cuts k n (d+1)) (hn : 0 < n)
    (a s u : ℕ) (theta : ℝ) :
    (∑ j ∈ empiricalPositions d 0 s u, psi ((tailCuts cuts).profile hn j) theta)/logScale N =
      empiricalB N a cuts hn theta (a+1+s) (a+1+u) := by
  rw [← empiricalB_tailCuts cuts hn a (a+1+s) (a+1+u) (by omega) theta]
  simp [empiricalB,RiffleLowerV2.gridSum,empiricalPositions,Nat.add_sub_cancel_left]

end RiffleUpperV2.FirstMoment
