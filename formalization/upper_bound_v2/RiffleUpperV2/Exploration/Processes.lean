import RiffleUpperV2.Exploration.Histories

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration

@[simp] theorem directionalProcess_zero {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (ω ω' : Sample cuts) :
    directionalProcess cuts D g ξ p d 0 ω ω' = 0 := by
  simp [directionalProcess]

@[simp] theorem directionalProcess_one {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (ω ω' : Sample cuts) :
    directionalProcess cuts D g ξ p d 1 ω ω' = 0 := by
  simp [directionalProcess]

theorem directionalEdge_adapted {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g : ℝ) (p : Fin k) (d : Direction) (i : ℕ)
    (e : Fin (pileSize cuts p - 1)) (he : e.val+1 < i) {ω v : Sample cuts}
    (h : naturalHistory cuts p d i ω = naturalHistory cuts p d i v) :
    directionalEdge cuts D g p d e ω ↔ directionalEdge cuts D g p d e v := by
  have h₁ := revealed_word_eq cuts p d i h ⟨e.val, by omega⟩ (show e.val < i by omega)
  have h₂ := revealed_word_eq cuts p d i h ⟨e.val+1, by omega⟩ he
  simp only [directionalEdge, h₁, h₂]

theorem directionalProcess_adapted {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (i : ℕ)
    {ω v : Sample cuts × Sample cuts} (h : pairHistory cuts p d i ω = pairHistory cuts p d i v) :
    directionalProcess cuts D g ξ p d i ω.1 ω.2 =
      directionalProcess cuts D g ξ p d i v.1 v.2 := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  unfold directionalProcess
  split_ifs
  · congr 1
    apply Finset.filter_congr
    intro e _
    by_cases he : e.val+1 < i
    · simp only [he, true_and, directionalEdge_adapted cuts D g p d i e he h₁,
        directionalEdge_adapted cuts D g p d i e he h₂]
    · simp only [he, false_and]
  · rfl

/-- Generic deterministic fact for adjacent revealed vertices. -/
theorem revealedEdges_step {m i : ℕ} (P : Fin m → Prop) [DecidablePred P] :
    let S := fun j => Finset.univ.filter (fun e : Fin m => e.val+1 < j ∧ P e)
    (S (i+1)).card = (S i).card ∨ (S (i+1)).card = (S i).card + 1 := by
  dsimp only
  by_cases hex : ∃ e : Fin m, e.val+1 = i ∧ P e
  · obtain ⟨e, he, hP⟩ := hex
    have hs : Finset.univ.filter (fun e : Fin m => e.val+1 < i+1 ∧ P e) =
        insert e (Finset.univ.filter (fun e : Fin m => e.val+1 < i ∧ P e)) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨ha, hPa⟩
        by_cases hai : a.val+1 < i
        · exact Or.inr ⟨hai, hPa⟩
        · left
          apply Fin.ext
          omega
      · rintro (rfl | ⟨ha, hPa⟩)
        · exact ⟨by omega, hP⟩
        · exact ⟨by omega, hPa⟩
    right
    rw [hs, Finset.card_insert_of_notMem]
    simp [he]
  · left
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he, hP⟩
      refine ⟨?_, hP⟩
      have hne : e.val+1 ≠ i := fun hh => hex ⟨e, hh, hP⟩
      omega
    · rintro ⟨he, hP⟩
      exact ⟨by omega, hP⟩

theorem unitIncrements {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (i : ℕ) (ω ω' : Sample cuts) :
    directionalProcess cuts D g ξ p d (i+1) ω ω' =
      directionalProcess cuts D g ξ p d i ω ω' ∨
    directionalProcess cuts D g ξ p d (i+1) ω ω' =
      directionalProcess cuts D g ξ p d i ω ω' + 1 := by
  unfold directionalProcess
  split_ifs
  · simpa only using (revealedEdges_step (m := pileSize cuts p - 1) (i := i)
      (fun e => directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω'))
  · exact Or.inl rfl

/-- Explicit unseen-edge formula. At i>0 the index i-1 is included when it is an edge. -/
theorem remainingDirectionalCount_eq {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (i : ℕ) (ω ω' : Sample cuts) :
    remainingDirectionalCount cuts D g ξ p d i ω ω' =
      if (n : ℝ)^ξ ≤ (pileSize cuts p : ℝ) then
        (Finset.univ.filter fun e : Fin (pileSize cuts p - 1) => i ≤ e.val+1 ∧
          directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω').card
      else 0 := by
  let S := Finset.univ.filter (fun e : Fin (pileSize cuts p - 1) =>
    directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω')
  unfold remainingDirectionalCount directionalProcess
  split_ifs with h
  · have ht : Finset.univ.filter (fun e : Fin (pileSize cuts p - 1) =>
        e.val+1 < pileSize cuts p ∧ directionalEdge cuts D g p d e ω ∧
          directionalEdge cuts D g p d e ω') = S := by
      ext e
      have he := e.isLt
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact and_iff_right (by omega)
    have hs : Finset.univ.filter (fun e : Fin (pileSize cuts p - 1) =>
        e.val+1 < i ∧ directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω') =
        S.filter (fun e => e.val+1 < i) := by ext e; simp [S, and_comm, and_left_comm]
    have hr : Finset.univ.filter (fun e : Fin (pileSize cuts p - 1) =>
        i ≤ e.val+1 ∧ directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω') =
        S.filter (fun e => ¬ e.val+1 < i) := by
      ext e
      simp [S, not_lt, and_comm, and_left_comm]
    rw [ht, hs, hr]
    have hc := Finset.card_filter_add_card_filter_not (s := S) (fun e => e.val+1 < i)
    omega
  · simp

theorem remaining_terminal {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (ω ω' : Sample cuts) :
    remainingDirectionalCount cuts D g ξ p d (pileSize cuts p) ω ω' = 0 := by
  simp [remainingDirectionalCount]

theorem pairHistoryGood_initial {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε : ℝ) (p : Fin k) (d : Direction) (ω : Sample cuts × Sample cuts) :
    pairHistoryGood cuts D g ξ ε p d 0 ω := by simp [pairHistoryGood]

theorem pairHistoryGood_terminal {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ ε : ℝ) (p : Fin k) (d : Direction) (ω : Sample cuts × Sample cuts) :
    pairHistoryGood cuts D g ξ ε p d (pileSize cuts p) ω := by simp [pairHistoryGood]

end RiffleUpperV2.Exploration
