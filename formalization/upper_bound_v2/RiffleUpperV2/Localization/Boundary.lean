import RiffleUpperV2.Localization.Stopping

noncomputable section
open scoped BigOperators
namespace RiffleUpperV2.Localization
open Anchor

/-- The local empty prefix is the already-exposed anchor, never a random side. -/
def anchorPrefix (k d : ℕ) : Prefix k d := ⟨⟨0, Nat.zero_lt_succ _⟩, ⟨[],rfl⟩⟩

/-- Digit greater than the smallest chi-large digit, without choosing an extremum. -/
def LeftBoundaryTest {k n d : ℕ} (cuts : Cuts k n d) (χ : ℝ) (x : Prefix k d) : Prop :=
  ∃ hx : 0 < x.1.val, ∃ b : Fin k,
    χ ≤ digitProbability cuts (prefixColumn x ⟨x.1.val-1, by omega⟩) b ∧
    b < x.2.get ⟨x.1.val-1, by omega⟩

/-- Digit smaller than the largest chi-large digit. -/
def RightBoundaryTest {k n d : ℕ} (cuts : Cuts k n d) (χ : ℝ) (x : Prefix k d) : Prop :=
  ∃ hx : 0 < x.1.val, ∃ b : Fin k,
    χ ≤ digitProbability cuts (prefixColumn x ⟨x.1.val-1, by omega⟩) b ∧
    x.2.get ⟨x.1.val-1, by omega⟩ < b

def LeftBoundary {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (χ : ℝ) (x : Prefix k d) : Prop :=
  Legal cuts R x ∧ FirstCut (anchorPrefix k d) (LeftBoundaryTest cuts χ) x

def RightBoundary {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (χ : ℝ) (x : Prefix k d) : Prop :=
  Legal cuts R x ∧ FirstCut (anchorPrefix k d) (RightBoundaryTest cuts χ) x

def boundaryJoin {k d : ℕ} (y z : Prefix k d) : Prefix k d :=
  if z.1.val ≤ y.1.val then y else z

/-- Reaching depth d is terminal even if a genuine crossing occurs there. -/
def TerminalBoundaryPair {k d : ℕ} (y z : Prefix k d) : Prop :=
  y.1.val = d ∨ z.1.val = d

theorem digit_le_leftProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    {b a : Fin k} (hba : b < a) : digitProbability cuts j b ≤ leftProbability cuts j a := by
  apply div_le_div_of_nonneg_right
  · apply Nat.cast_le.mpr
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hba⟩)
  · exact Nat.cast_nonneg _

theorem digit_le_rightProbability {k n d : ℕ} (cuts : Cuts k n d) (j : Fin d)
    {b a : Fin k} (hab : a < b) : digitProbability cuts j b ≤ rightProbability cuts j a := by
  apply div_le_div_of_nonneg_right
  · apply Nat.cast_le.mpr
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
  · exact Nat.cast_nonneg _

theorem leftBoundaryTest_crossing {k n d : ℕ} {cuts : Cuts k n d} {χ : ℝ}
    {x : Prefix k d} (hx : LeftBoundaryTest cuts χ x) : LeftCrossing cuts χ x := by
  obtain ⟨hlen,b,hprob,hb⟩ := hx
  exact ⟨hlen, hprob.trans (digit_le_leftProbability cuts _ hb)⟩

theorem rightBoundaryTest_crossing {k n d : ℕ} {cuts : Cuts k n d} {χ : ℝ}
    {x : Prefix k d} (hx : RightBoundaryTest cuts χ x) : RightCrossing cuts χ x := by
  obtain ⟨hlen,b,hprob,hb⟩ := hx
  exact ⟨hlen, hprob.trans (digit_le_rightProbability cuts _ hb)⟩

theorem boundaryJoin_properties {k d : ℕ} {y z w : Prefix k d}
    (hyw : IsPrefix y w) (hzw : IsPrefix z w) :
    IsPrefix y (boundaryJoin y z) ∧ IsPrefix z (boundaryJoin y z) ∧
      (boundaryJoin y z = y ∨ boundaryJoin y z = z) ∧ IsPrefix (boundaryJoin y z) w := by
  unfold boundaryJoin
  split_ifs with hlen
  · refine ⟨List.prefix_rfl, ?_, Or.inl rfl, hyw⟩
    exact List.prefix_of_prefix_length_le hzw hyw (by simpa using hlen)
  · refine ⟨?_, List.prefix_rfl, Or.inr rfl, hzw⟩
    apply List.prefix_of_prefix_length_le hyw hzw
    simp only [List.Vector.toList_length]
    omega

theorem boundaries_existUnique {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) (χ : ℝ) {w : Prefix k d}
    (hw : Legal cuts R w) (hwfull : w.1.val = d) :
    (∃! y, LeftBoundary cuts R χ y ∧ IsPrefix y w) ∧
    (∃! z, RightBoundary cuts R χ z ∧ IsPrefix z w) := by
  constructor
  · obtain ⟨y,hy,hu⟩ := firstCut_existsUnique (v := anchorPrefix k d)
      (Q := LeftBoundaryTest cuts χ) hwfull List.nil_prefix
    exact ⟨y, ⟨⟨legal_prefix cuts hn R hw hy.2,hy.1⟩,hy.2⟩,
      fun z hz => hu z ⟨hz.1.2,hz.2⟩⟩
  · obtain ⟨z,hz,hu⟩ := firstCut_existsUnique (v := anchorPrefix k d)
      (Q := RightBoundaryTest cuts χ) hwfull List.nil_prefix
    exact ⟨z, ⟨⟨legal_prefix cuts hn R hw hz.2,hz.1⟩,hz.2⟩,
      fun y hy => hu y ⟨hy.1.2,hy.2⟩⟩

/-- Literal nonterminal first boundaries satisfy U03's sufficient crossing contract. -/
theorem genuine_of_nonterminal_boundaries {k n d : ℕ} {cuts : Cuts k n d}
    {R : Finset (Fin n)} {χ : ℝ} (hχ : 0 < χ) (hχ1 : χ < 1)
    {y z w : Prefix k d} (hy : LeftBoundary cuts R χ y) (hz : RightBoundary cuts R χ z)
    (hyw : IsPrefix y w) (hzw : IsPrefix z w) (hnt : ¬TerminalBoundaryPair y z) :
    GenuineBoundaryPair cuts R χ y z (boundaryJoin y z) := by
  have hp := boundaryJoin_properties hyw hzw
  have hyn : y.1.val ≠ d := fun h => hnt (Or.inl h)
  have hzn : z.1.val ≠ d := fun h => hnt (Or.inr h)
  refine ⟨hχ,hχ1,hp.1,hp.2.1,hp.2.2.1,?_,?_,?_⟩
  · rcases hp.2.2.1 with h | h
    · simpa [h] using hy.1
    · simpa [h] using hz.1
  · exact leftBoundaryTest_crossing (hy.2.2.1.resolve_right hyn)
  · exact rightBoundaryTest_crossing (hz.2.2.1.resolve_right hzn)

end RiffleUpperV2.Localization
