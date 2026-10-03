import RiffleUpperV2.Exploration.DirectionalCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Exploration
open RiffleLowerV2.Model

/-- The global edge at a local zero-based spatial edge position. -/
def spatialPileEdge {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p-1)) : Fin (n-1) :=
  ⟨pileOffset cuts p+e.val, by have := pileOffset_add_size_le cuts p; have := e.isLt; omega⟩

theorem spatialPileEdge_left {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p-1)) :
    RiffleLowerV2.edgeLeft (spatialPileEdge cuts p e) =
      pilePosition cuts p .forward ⟨e.val,by omega⟩ := rfl

theorem spatialPileEdge_right {k n L : ℕ} (cuts : Cuts k n (L+1)) (p : Fin k)
    (e : Fin (pileSize cuts p-1)) :
    RiffleLowerV2.edgeRight (spatialPileEdge cuts p e) =
      pilePosition cuts p .forward ⟨e.val+1,by omega⟩ := by apply Fin.ext; dsimp [RiffleLowerV2.edgeRight,spatialPileEdge,pilePosition,spatialIndex]; omega

/-- Every actual tied edge belongs to a single initial pile, including near pile boundaries. -/
theorem shuffleEdge_in_pile {k n L : ℕ} (cuts : Cuts k n (L+1)) (ω : Sample cuts)
    (e : Fin (n-1)) (he : e ∈ shuffleEdges ω) :
    ∃ p : Fin k, ∃ f : Fin (pileSize cuts p-1), spatialPileEdge cuts p f = e := by
  have htie := (Finset.mem_filter.mp he).2
  let p := (sortedWord ω (RiffleLowerV2.edgeLeft e)).get 0
  have hpos (j : Fin n) (hj : (sortedWord ω j).get 0 = p) :
      pileOffset cuts p ≤ j.val ∧ j.val < pileOffset cuts p+pileSize cuts p := by
    have hw : (sortedWord ω j).toList.take 1 = [p] := by
      change (rowWord ω (RiffleLowerV2.stableSort ω j)).toList.take 1 = [p]
      rw [row_take_one]
      simpa only [RiffleLowerV2.sortedWord,RiffleLowerV2.rowWord_get,TimeProfile.sampleEntry,List.singleton_inj] using hj
    have hh := (RiffleLowerV2.Model.prefixRanks cuts ω (pilePrefix (L := L) p)).1 j |>.mp hw
    simpa only [pilePrefix_lowerRank,pilePrefix_upperRank] using hh
  have hl := hpos (RiffleLowerV2.edgeLeft e) rfl
  have hr := hpos (RiffleLowerV2.edgeRight e) (congrArg (fun w => w.get 0) htie.symm)
  simp only [RiffleLowerV2.edgeLeft,RiffleLowerV2.edgeRight] at hl hr
  refine ⟨p,⟨e.val-pileOffset cuts p,by omega⟩,?_⟩
  apply Fin.ext
  simp only [spatialPileEdge]
  omega

/-- A local pair of common directional edges is counted at terminal time. -/
theorem directionalProcess_terminal {k n L : ℕ} (cuts : Cuts k n (L+1))
    (D : ℕ) (g ξ : ℝ) (p : Fin k) (d : Direction) (ω ω' : Sample cuts) :
    directionalProcess cuts D g ξ p d (pileSize cuts p) ω ω' =
      (if (n : ℝ)^ξ ≤ pileSize cuts p then
        (Finset.univ.filter fun e : Fin (pileSize cuts p-1) =>
          directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω').card else 0) := by
  unfold directionalProcess
  split_ifs with hp
  · congr 1
    ext e
    have he : e.val+1 < pileSize cuts p := by omega
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
  · rfl

/-- On the actual one-matrix regularity events, all shared graph edges are covered
by the terminal values of the 2k directional processes. -/
theorem sharedEdges_le_directionalProcesses {k n L : ℕ} (cuts : Cuts k n (L+1))
    (hn : 0 < n) (hk : 1 ≤ k) (D : ℕ) {g ξ ε : ℝ} (hg : 0 < g)
    (hc : retainedGoodCluster cuts hn D g) {ω ω' : Sample cuts}
    (h : regularityEvent cuts D g ξ ε ω) (h' : regularityEvent cuts D g ξ ε ω') :
    (shuffleEdges ω ∩ shuffleEdges ω').card ≤
      ∑ p : Fin k, ∑ d : Direction, directionalProcess cuts D g ξ p d (pileSize cuts p) ω ω' := by
  let S : Finset (Σ p : Fin k, Σ _d : Direction, Fin (pileSize cuts p-1)) :=
    Finset.univ.sigma fun p => Finset.univ.sigma fun d =>
      if (n : ℝ)^ξ ≤ pileSize cuts p then
        Finset.univ.filter fun e => directionalEdge cuts D g p d e ω ∧ directionalEdge cuts D g p d e ω'
      else ∅
  let f : (Σ p : Fin k, Σ _d : Direction, Fin (pileSize cuts p-1)) → Fin (n-1) :=
    fun q => spatialPileEdge cuts q.1 (match q.2.1 with | .forward => q.2.2 | .backward => reversePileEdge q.2.2)
  have hcard : S.card = ∑ p : Fin k, ∑ d : Direction,
      directionalProcess cuts D g ξ p d (pileSize cuts p) ω ω' := by
    simp only [S, Finset.card_sigma, directionalProcess_terminal]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  rw [← hcard]
  apply Finset.card_le_card_of_surjOn f
  intro e he
  obtain ⟨hpω,hpω'⟩ := Finset.mem_inter.mp he
  obtain ⟨p,t,ht⟩ := shuffleEdge_in_pile cuts ω e hpω
  have hties (a : Sample cuts) (ha : e ∈ shuffleEdges a) :
      sortedWord a (pilePosition cuts p .forward ⟨t.val,by omega⟩) =
        sortedWord a (pilePosition cuts p .forward ⟨t.val+1,by omega⟩) := by
    have hh := (Finset.mem_filter.mp ha).2
    rw [← ht,spatialPileEdge_left,spatialPileEdge_right] at hh
    exact hh
  have hlarge : (n : ℝ)^ξ ≤ pileSize cuts p := by
    by_contra hh
    exact h.2.2 p (lt_of_not_ge hh) t (hties ω hpω)
  rcases directionalCover cuts hn hk D hg hc p hlarge h.1 h'.1 t (hties ω hpω) (hties ω' hpω') with hf | hb
  · refine ⟨⟨p,.forward,t⟩,?_,?_⟩
    · change (⟨p,.forward,t⟩ : Σ p : Fin k, Σ _d : Direction, Fin (pileSize cuts p-1)) ∈ S
      simpa only [S,Finset.mem_sigma,Finset.mem_univ,true_and,hlarge,if_true,Finset.mem_filter] using hf
    · exact ht
  · refine ⟨⟨p,.backward,reversePileEdge t⟩,?_,?_⟩
    · change (⟨p,.backward,reversePileEdge t⟩ : Σ p : Fin k, Σ _d : Direction, Fin (pileSize cuts p-1)) ∈ S
      simpa only [S,Finset.mem_sigma,Finset.mem_univ,true_and,hlarge,if_true,Finset.mem_filter] using hb
    · simpa only [f,reversePileEdge_involutive] using ht

end RiffleUpperV2.Exploration
