import RiffleUpperV2.FirstMoment.Discard

noncomputable section
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization
attribute [local instance] Classical.propDecidable

abbrev BlockTriple (k d : ℕ) := Prefix k d × Prefix k d × Prefix k d

def ValidBlock {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (R : Finset (Fin n))
    (chi delta : ℝ) (b : BlockTriple k d) : Prop :=
  LeftBoundary cuts R chi b.1 ∧ RightBoundary cuts R chi b.2.1 ∧
  IsPrefix b.1 b.2.2 ∧ IsPrefix b.2.1 b.2.2 ∧
  Stable N cuts R (boundaryJoin b.1 b.2.1) delta b.2.2

abbrev Blocks {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (R : Finset (Fin n))
    (chi delta : ℝ) := {b : BlockTriple k d // ValidBlock N cuts R chi delta b}

/-- Every legal full future word belongs to exactly one actual boundary/stable block. -/
theorem blockPartition {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (chi delta : ℝ) (w : Prefix k d)
    (hw : Legal cuts R w) (hfull : w.1.val = d) :
    ∃! b : Blocks N cuts R chi delta, IsPrefix b.1.2.2 w := by
  obtain ⟨⟨y,hy,hyuniq⟩,⟨z,hz,hzuniq⟩⟩ := boundaries_existUnique cuts hn R chi hw hfull
  have hj := boundaryJoin_properties hy.2 hz.2
  obtain ⟨x,hx,hxuniq⟩ := stableCover N cuts hn R (boundaryJoin y z) delta
    (show w ∈ FullCylinder cuts R (boundaryJoin y z) from ⟨hw,hfull,hj.2.2.2⟩)
  let b : Blocks N cuts R chi delta :=
    ⟨(y,z,x),hy.1,hz.1,hj.1.trans hx.1.2.1,hj.2.1.trans hx.1.2.1,hx.1⟩
  refine ⟨b,hx.2,?_⟩
  intro c hc
  have hyc : c.1.1 = y := hyuniq c.1.1 ⟨c.2.1,c.2.2.2.1.trans hc⟩
  have hzc : c.1.2.1 = z := hzuniq c.1.2.1 ⟨c.2.2.1,c.2.2.2.2.1.trans hc⟩
  have hxc : c.1.2.2 = x := hxuniq c.1.2.2 ⟨by simpa [hyc,hzc] using c.2.2.2.2.2,hc⟩
  apply Subtype.ext
  exact Prod.ext hyc (Prod.ext hzc hxc)

/-- Terminal boundary classes contain a single full word, including a genuine
crossing at the last future column. -/
theorem terminalBlock_full {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {chi delta : ℝ} (b : Blocks N cuts R chi delta)
    (ht : TerminalBoundaryPair b.1.1 b.1.2.1) : b.1.2.2.1.val = d := by
  have hx := b.1.2.2.1.isLt
  rcases ht with hy | hz
  · have h := prefix_length_le b.2.2.2.1
    omega
  · have h := prefix_length_le b.2.2.2.2.1
    omega

theorem terminalBlock_singleton {k n d : ℕ} {N : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {chi delta : ℝ} (b : Blocks N cuts R chi delta)
    (ht : TerminalBoundaryPair b.1.1 b.1.2.1) {w : Prefix k d}
    (hw : IsPrefix b.1.2.2 w) : w = b.1.2.2 := by
  have hwlen := w.1.isLt
  have hbfull := terminalBlock_full b ht
  have hlen := prefix_length_le hw
  exact (prefix_eq_of_length hw (by omega)).symm

/-- Completing a prefix agrees with its full-word extension at every stored digit. -/
theorem completePrefix_eq_fullword {k d : ℕ} (default : Fin d → Fin k)
    (x : Prefix k d) (w : Fin d → Fin k)
    (hprefix : IsPrefix x (RiffleLowerV2.fullPrefix (List.Vector.ofFn w)))
    (j : Fin d) (hj : j.val < x.1.val) : completePrefix default x j = w j := by
  have hget := hprefix.getElem (by simpa using hj)
  have hget' : x.2.get ⟨j.val,hj⟩ = (List.Vector.ofFn w).get j := by
    simpa [List.Vector.get,List.Vector.toList,RiffleLowerV2.fullPrefix] using hget
  simpa [completePrefix,hj] using hget'

/-- Every exceptional position in a selected extension is a rare position of the
actual complete word, independently of the chosen stable stopping time. -/
theorem extensionExceptions_le_badCount {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (default : Fin d → Fin k) (v x : Prefix k d) (w : Fin d → Fin k)
    (hprefix : IsPrefix x (RiffleLowerV2.fullPrefix (List.Vector.ofFn w))) (chi : ℝ) :
    (exceptionalPositions (cuts.profile hn) (empiricalPositions d 0 v.1.val x.1.val)
      chi (completePrefix default x)).card ≤ Compat.badCount (rareDigits cuts hn chi) w := by
  apply Finset.card_le_card
  intro j hj
  have hjI := (Finset.mem_filter.mp hj).1
  have hjlen : j.val < x.1.val := by simpa [empiricalPositions] using (Finset.mem_filter.mp hjI).2.2
  have hrare := (Finset.mem_filter.mp hj).2
  rw [completePrefix_eq_fullword default x w hprefix j hjlen] at hrare
  simpa [Compat.badPositions,rareDigits] using hrare

/-- Actual left boundary exceptions are bounded by the full row's rare count. -/
theorem leftBoundaryExceptions_le_badCount {k n d : ℕ} (hk : 0 < k)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (y : Prefix k d) (w : Fin d → Fin k)
    (hy : LeftBoundary cuts R chi y)
    (hprefix : IsPrefix y (RiffleLowerV2.fullPrefix (List.Vector.ofFn w))) :
    (boundaryExceptions (leftDefault hk cuts hn chi hchi) y).card ≤
      Compat.badCount (rareDigits cuts hn chi) w := by
  apply Finset.card_le_card
  intro j hj
  have hjlen := (Finset.mem_filter.mp hj).2.1
  have hr := leftBoundary_exception_rare hk cuts hn chi hchi R y hy j hj
  rw [completePrefix_eq_fullword _ y w hprefix j (by omega)] at hr
  change prob (cuts.profile hn j) (w j) < chi at hr
  simpa [Compat.badPositions,rareDigits] using hr

/-- Actual right boundary exceptions satisfy the same full-row bound. -/
theorem rightBoundaryExceptions_le_badCount {k n d : ℕ} (hk : 0 < k)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    (chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (y : Prefix k d) (w : Fin d → Fin k)
    (hy : RightBoundary cuts R chi y)
    (hprefix : IsPrefix y (RiffleLowerV2.fullPrefix (List.Vector.ofFn w))) :
    (boundaryExceptions (rightDefault hk cuts hn chi hchi) y).card ≤
      Compat.badCount (rareDigits cuts hn chi) w := by
  apply Finset.card_le_card
  intro j hj
  have hjlen := (Finset.mem_filter.mp hj).2.1
  have hr := rightBoundary_exception_rare hk cuts hn chi hchi R y hy j hj
  rw [completePrefix_eq_fullword _ y w hprefix j (by omega)] at hr
  change prob (cuts.profile hn j) (w j) < chi at hr
  simpa [Compat.badPositions,rareDigits] using hr


/-- The manuscript's three truncations, on the actual unique boundary/stable block. -/
def RetainedBlock {k n d : ℕ} (hk : 0 < k) (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (C chi : ℝ) (hchi : chi ≤ 1/(k : ℝ)) (b : BlockTriple k d) : Prop :=
  (boundaryExceptions (leftDefault hk cuts hn chi hchi) b.1).card ≤ boundaryBudget N C chi ∧
  (boundaryExceptions (rightDefault hk cuts hn chi hchi) b.2.1).card ≤ boundaryBudget N C chi ∧
  (exceptionalPositions (cuts.profile hn)
    (empiricalPositions d 0 (boundaryJoin b.1 b.2.1).1.val b.2.2.1.val) chi
    (completePrefix (leftDefault hk cuts hn chi hchi) b.2.2)).card ≤ extensionBudget N chi

def discardedWords {k n d : ℕ} (hk : 0 < k) (N : ℕ) (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (C chi delta : ℝ) (hchi : chi ≤ 1/(k : ℝ)) :
    Finset (Fin d → Fin k) :=
  Finset.univ.filter fun w => ∃ b : Blocks N cuts R chi delta,
    IsPrefix b.1.2.2 (RiffleLowerV2.fullPrefix (List.Vector.ofFn w)) ∧
      ¬RetainedBlock hk N cuts hn C chi hchi b.1

/-- Actual omitted boundary/stable cylinders are contained in the rare-row majorant. -/
theorem discardedWords_subset_envelope {k n d : ℕ} (hk : 0 < k) (N : ℕ)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n))
    (C chi delta : ℝ) (hchi : chi ≤ 1/(k : ℝ)) :
    discardedWords hk N cuts hn R C chi delta hchi ⊆
      rareWords cuts hn chi (boundaryBudget N C chi+1) ∪
        rareWords cuts hn chi (extensionBudget N chi+1) := by
  intro w hw
  obtain ⟨b,hbw,hnot⟩ := (Finset.mem_filter.mp hw).2
  by_contra hnone
  have hbadb : Compat.badCount (rareDigits cuts hn chi) w ≤ boundaryBudget N C chi := by
    by_contra h
    exact hnone (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩))
  have hbade : Compat.badCount (rareDigits cuts hn chi) w ≤ extensionBudget N chi := by
    by_contra h
    exact hnone (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩))
  apply hnot
  refine ⟨?_,?_,?_⟩
  · exact (leftBoundaryExceptions_le_badCount hk cuts hn R chi hchi b.1.1 w b.2.1
      (b.2.2.2.1.trans hbw)).trans hbadb
  · exact (rightBoundaryExceptions_le_badCount hk cuts hn R chi hchi b.1.2.1 w b.2.2.1
      (b.2.2.2.2.1.trans hbw)).trans hbadb
  · exact (extensionExceptions_le_badCount cuts hn _ (boundaryJoin b.1.1 b.1.2.1)
      b.1.2.2 w hbw chi).trans hbade

/-- Expected discarded labels for the actual block construction. The threshold chi0
is independent of N,n,d, cuts, R and delta, and C is chosen first. -/
theorem discardedRows_power_bound (k : ℕ) (T D C : ℝ) (hk : 2 ≤ k)
    (hT : 0 ≤ T) (hD : 0 < D) (hC : D+3 ≤ C) :
    ∃ chi0 : ℝ, 0 < chi0 ∧ chi0 < min 1 (1/(k : ℝ)) ∧
      ∀ chi : ℝ, 0 < chi → chi < chi0 → ∀ hchi : chi ≤ 1/(k : ℝ),
        ∀ N n d : ℕ, 2 ≤ N → ∀ hn : 0 < n, n ≤ N →
          (d : ℝ) ≤ T*logScale N → ∀ cuts : Cuts k n d, ∀ R : Finset (Fin n), ∀ delta : ℝ,
          expect (fixedCountPMF cuts) (fun omega =>
            ((rowsInWords R (discardedWords (by omega) N cuts hn R C chi delta hchi) omega).card : ℝ)) ≤
            (N : ℝ)^(-D) := by
  obtain ⟨chi1,hchi1,hchi11,hpow⟩ := discardEnvelope_power_bound k T D C hT hD hC
  have hkr : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  let chi0 := min chi1 (1/(2*(k : ℝ)))
  refine ⟨chi0,lt_min hchi1 (by positivity),lt_min
    ((min_le_left _ _).trans_lt hchi11) ?_,?_⟩
  · apply (min_le_right _ _).trans_lt
    apply (div_lt_div_iff₀ (by positivity) hkr).mpr
    nlinarith
  · intro chi hchi hchi0 hchiK N n d hN hn hnN hd cuts R delta
    exact (rowsInWords_expect_mono cuts R
      (discardedWords_subset_envelope (by omega) N cuts hn R C chi delta hchiK)).trans
      (hpow chi hchi (hchi0.trans_le (min_le_left _ _)) N n d hN hn hnN hd cuts R)

end RiffleUpperV2.FirstMoment
