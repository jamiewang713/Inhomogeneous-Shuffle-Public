import RiffleUpperV2.Anchor.EqualLaw

noncomputable section
attribute [local instance] Classical.propDecidable
namespace RiffleUpperV2.Anchor
open TimeProfile

inductive SuffixSide where
  | lower
  | upper
  deriving DecidableEq

def SuffixSide.test {α : Type*} [LT α] (s : SuffixSide) (u v : α) : Prop :=
  match s with
  | .lower => u < v
  | .upper => v < u

def SuffixSide.allowed {k : ℕ} (s : SuffixSide) (a : Fin k) : Finset (Fin k) :=
  Finset.univ.filter (fun b => match s with | .lower => b ≤ a | .upper => b < a)

/-- The whole equal-length suffix through x is compared. This enlarges the
source witness set, while keeping every prefix-x row in the exposed complement. -/
def unequalSampleRows {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :=
  (matchingBeforeRows R x j ω).filter (fun r =>
    s.test (rowSlice ω r (j.val+1) x.1.val) (x.2.toList.drop (j.val+1)))

def unequalExposedRows {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :=
  matchingBeforeRows R x j ω \ unequalSampleRows s R x j ω

def unequalRevealFiber {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω₀ ω : Sample cuts) :=
  partialRevealFiber (prefixColumn x j) (unequalExposedRows s R x j ω₀) ω₀ ω

def unequalRevealHistory {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :=
  (otherColumnHistory (prefixColumn x j) ω,
    fun r : Fin n => if r ∈ unequalExposedRows s R x j ω
      then some (sampleEntry ω r (prefixColumn x j)) else none)

theorem other_beforeSlice {k n d : ℕ} {cuts : Cuts k n d}
    (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : ∀ t : Fin d, t ≠ prefixColumn x j → ω t = ω₀ t) (r : Fin n) :
    rowSlice ω r 0 j.val = rowSlice ω₀ r 0 j.val := by
  apply rowSlice_eq _ _ _ _ _ (Nat.zero_le _)
    (le_trans j.isLt.le (Nat.le_of_lt_succ x.1.isLt))
  intro t _ ht
  have hne : t ≠ prefixColumn x j := by
    intro he
    have hv := congrArg (fun t : Fin d => t.val) he
    change t.val = j.val at hv
    omega
  exact congrArg (fun c => c.val r) (hf t hne)

theorem other_afterSlice {k n d : ℕ} {cuts : Cuts k n d}
    (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : ∀ t : Fin d, t ≠ prefixColumn x j → ω t = ω₀ t) (r : Fin n) :
    rowSlice ω r (j.val+1) x.1.val = rowSlice ω₀ r (j.val+1) x.1.val := by
  apply rowSlice_eq _ _ _ _ _ (Nat.succ_le_of_lt j.isLt) (Nat.le_of_lt_succ x.1.isLt)
  intro t ht _
  have hne : t ≠ prefixColumn x j := by
    intro he
    have hv := congrArg (fun t : Fin d => t.val) he
    change t.val = j.val at hv
    omega
  exact congrArg (fun c => c.val r) (hf t hne)

theorem other_matchingBeforeRows {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : ∀ t : Fin d, t ≠ prefixColumn x j → ω t = ω₀ t) :
    matchingBeforeRows R x j ω = matchingBeforeRows R x j ω₀ := by
  apply Finset.filter_congr
  intro r _
  exact Iff.of_eq (congrArg (fun u => u = x.2.toList.take j.val) (other_beforeSlice x j hf r))

theorem other_unequalRows {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) {ω₀ ω : Sample cuts}
    (hf : ∀ t : Fin d, t ≠ prefixColumn x j → ω t = ω₀ t) :
    unequalSampleRows s R x j ω = unequalSampleRows s R x j ω₀ ∧
    unequalExposedRows s R x j ω = unequalExposedRows s R x j ω₀ := by
  have hb : unequalSampleRows s R x j ω = unequalSampleRows s R x j ω₀ := by
    unfold unequalSampleRows
    rw [other_matchingBeforeRows R x j hf]
    apply Finset.filter_congr
    intro r _
    rw [other_afterSlice x j hf r]
  exact ⟨hb, by unfold unequalExposedRows; rw [hb, other_matchingBeforeRows R x j hf]⟩

theorem unequalSampleRows_subset {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω : Sample cuts) :
    unequalSampleRows s R x j ω ⊆ Finset.univ \ unequalExposedRows s R x j ω := by
  intro r hr
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, fun h => (Finset.mem_sdiff.mp h).2 hr⟩

theorem unequalRevealHistory_eq_iff {k n d : ℕ} {cuts : Cuts k n d} (s : SuffixSide)
    (R : Finset (Fin n)) (x : Prefix k d) (j : Fin x.1.val) (ω₀ ω : Sample cuts) :
    unequalRevealHistory s R x j ω = unequalRevealHistory s R x j ω₀ ↔
      unequalRevealFiber s R x j ω₀ ω := by
  constructor
  · intro he
    have ho := (otherColumnHistory_eq_iff (prefixColumn x j) ω₀ ω).mp (congrArg Prod.fst he)
    refine ⟨ho, ?_⟩
    intro r hr
    have ha := (other_unequalRows s R x j ho).2
    have he' := congrFun (congrArg Prod.snd he) r
    change (if r ∈ unequalExposedRows s R x j ω then some (sampleEntry ω r (prefixColumn x j)) else none) =
      (if r ∈ unequalExposedRows s R x j ω₀ then some (sampleEntry ω₀ r (prefixColumn x j)) else none) at he'
    change sampleEntry ω r (prefixColumn x j) = sampleEntry ω₀ r (prefixColumn x j)
    simpa only [ha, hr, if_true, Option.some.injEq] using he'
  · intro hf
    apply Prod.ext
    · exact (otherColumnHistory_eq_iff (prefixColumn x j) ω₀ ω).mpr hf.1
    · funext r
      have ha := (other_unequalRows s R x j hf.1).2
      change (if r ∈ unequalExposedRows s R x j ω then some (sampleEntry ω r (prefixColumn x j)) else none) =
        (if r ∈ unequalExposedRows s R x j ω₀ then some (sampleEntry ω₀ r (prefixColumn x j)) else none)
      rw [ha]
      by_cases hr : r ∈ unequalExposedRows s R x j ω₀
      · simp only [hr, if_true, hf.2 r hr, sampleEntry]
      · simp only [hr, if_false]

end RiffleUpperV2.Anchor
