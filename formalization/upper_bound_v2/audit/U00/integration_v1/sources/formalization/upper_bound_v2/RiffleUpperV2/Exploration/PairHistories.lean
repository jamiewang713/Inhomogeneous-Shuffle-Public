import RiffleUpperV2.Exploration.Processes

noncomputable section
namespace RiffleUpperV2.Exploration

theorem pairHistory_refinement {k n L : ℕ} (cuts : Cuts k n (L+1))
    (p : Fin k) (d : Direction) {i j : ℕ} (hij : i ≤ j)
    {ω v : Sample cuts × Sample cuts} (h : pairHistory cuts p d j ω = pairHistory cuts p d j v) :
    pairHistory cuts p d i ω = pairHistory cuts p d i v := by
  exact Prod.ext (history_refinement cuts p d hij (congrArg Prod.fst h))
    (history_refinement cuts p d hij (congrArg Prod.snd h))

theorem pairHistoryGood_adapted {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε : ℝ) (p : Fin k) (d : Direction) (i : ℕ)
    {ω v : Sample cuts × Sample cuts} (h : pairHistory cuts p d i ω = pairHistory cuts p d i v) :
    pairHistoryGood cuts D g ξ ε p d i ω ↔ pairHistoryGood cuts D g ξ ε p d i v := by
  unfold pairHistoryGood
  split_ifs
  · rfl
  · exact and_congr (historyGood_adapted cuts D g ξ ε p d i (congrArg Prod.fst h))
      (historyGood_adapted cuts D g ξ ε p d i (congrArg Prod.snd h))

/-- R is used only for the final event inclusion, never as part of a history. -/
theorem regularity_pairHistoryGood {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε : ℝ) (p : Fin k) (d : Direction) (i : ℕ)
    {ω : Sample cuts × Sample cuts}
    (h : regularityEvent cuts D g ξ ε ω.1) (h' : regularityEvent cuts D g ξ ε ω.2) :
    pairHistoryGood cuts D g ξ ε p d i ω := by
  by_cases hi : i = 0 ∨ pileSize cuts p ≤ i
  · simp only [pairHistoryGood,if_pos hi]
  · simp only [pairHistoryGood,if_neg hi]
    have hi0 : 0 < i := by omega
    have hip : i < pileSize cuts p := by omega
    exact ⟨h.2.1 p d i hi0 hip,h'.2.1 p d i hi0 hip⟩

end RiffleUpperV2.Exploration
