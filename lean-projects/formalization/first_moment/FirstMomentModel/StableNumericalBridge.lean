import Riffle.SourceStable
import Riffle.Pieces
import RiffleTimeProfile.ExpectedMass
import RiffleTimeProfile.SideMass

/-!
Exact finite adapters between actual stable words and the time-profile layer.
The interfaces are frozen in STABLE_NUMERICAL_BRIDGE_CONTRACT.md.
-/

namespace InhomogeneousShuffle.FirstMoment.Model

noncomputable section
open scoped BigOperators
open MeasureTheory

def asCuts (D : Riffle.Model) : TimeProfile.Cuts D.k D.N D.K where
  count j l := D.n j.val l.val
  sum_count j := by
    rw [Fin.sum_univ_eq_sum_range]
    exact D.sum_counts j.val j.isLt

def asProfile (D : Riffle.Model) : Fin D.K → TimeProfile.Simplex D.k :=
  (asCuts D).profile (lt_trans Nat.zero_lt_one D.one_lt_N)

def legalVector {D : Riffle.Model} (x : Riffle.Word) (hx : Riffle.Legal D x) :
    Fin D.K → Fin D.k := fun j =>
  if hj : j.val < x.length then ⟨Riffle.digit x j.val, (hx.2 j.val hj).1⟩
  else ⟨0, lt_of_lt_of_le (by decide : 0 < 2) D.two_le_k⟩

def sideProbability {k : ℕ} (s : Riffle.Side) : TimeProfile.Simplex k → Fin k → ℝ :=
  match s with
  | .left => TimeProfile.leftProbability
  | .right => TimeProfile.rightProbability

theorem asProfile_prob (D : Riffle.Model) (j : Fin D.K) (l : Fin D.k) :
    TimeProfile.prob (asProfile D j) l = (Riffle.prob D j.val l.val : ℝ) := by
  simp [asProfile, TimeProfile.Cuts.profile_prob, asCuts, Riffle.prob]

variable {D : Riffle.Model}

theorem legalVector_digit (x : Riffle.Word) (hx : Riffle.Legal D x)
    (j : Fin D.K) (hj : j.val < x.length) :
    (legalVector x hx j).val = Riffle.digit x j.val := by
  simp only [legalVector, dif_pos hj]

theorem legalVector_legal (x : Riffle.Word) (hx : Riffle.Legal D x) :
    TimeProfile.LegalPrefix (asProfile D) (legalVector x hx) x.length := by
  intro j hj
  rw [asProfile_prob, legalVector_digit x hx j hj]
  exact_mod_cast (Riffle.prob_pos_iff D j.val (Riffle.digit x j.val)).mpr
    (hx.2 j.val hj).2

theorem cL_prefix_eq (A : Riffle.Setup D) (x : Riffle.Word) (hx : Riffle.Legal D x)
    (u : Riffle.Word) (hux : u <+: x) :
    Riffle.cL A u = TimeProfile.cL D.N (asProfile D) (legalVector x hx)
      A.b A.w.length u.length := by
  classical
  have huK : u.length ≤ D.K := hux.length_le.trans hx.1
  have hs :
      (∑ j ∈ TimeProfile.positions D.K A.w.length u.length,
        TimeProfile.digitCost (TimeProfile.prob (asProfile D j) (legalVector x hx j))) =
      ∑ i ∈ Finset.Ico A.w.length u.length,
        Real.log ((D.N : ℝ) / (D.n i (Riffle.digit u i) : ℝ)) := by
    apply Finset.sum_bij (fun j _ => j.val)
    · intro j hj
      exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hj).2
    · intro j _ j' _ heq
      exact Fin.ext heq
    · intro i hi
      have hiK : i < D.K := (Finset.mem_Ico.mp hi).2.trans_le huK
      refine ⟨⟨i, hiK⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_Ico.mp hi⟩
    · intro j hj
      have hju : j.val < u.length := (Finset.mem_filter.mp hj).2.2
      have hjx := hju.trans_le hux.length_le
      rw [asProfile_prob, legalVector_digit x hx j hjx, ← Riffle.digit_prefix hux hju]
      simp [TimeProfile.digitCost, Riffle.prob]
  simp only [Riffle.cL, TimeProfile.cL, TimeProfile.logScale, hs]

theorem cL_parent_eq (A : Riffle.Setup D) (x : Riffle.Word) (hx : Riffle.Legal D x) :
    Riffle.cL A (Riffle.parent x) =
      TimeProfile.cL D.N (asProfile D) (legalVector x hx)
        A.b A.w.length (x.length - 1) := by
  simpa only [Riffle.parent_length] using
    cL_prefix_eq A x hx (Riffle.parent x) (Riffle.parent_prefix x)

theorem sampleRow_full (D : Riffle.Model)
    (sample : TimeProfile.ShuffleSample (asCuts D)) (i : Fin D.N) :
    Riffle.Full D (Riffle.fullList (D := D) (TimeProfile.sampleRow sample i)) := by
  refine ⟨⟨?_, ?_⟩, Riffle.fullList_length _⟩
  · exact (Riffle.fullList_length _).le
  · intro j hj
    have hjK : j < D.K := by simpa only [Riffle.fullList_length] using hj
    rw [Riffle.fullList_digit _ hjK]
    refine ⟨(TimeProfile.sampleRow sample i ⟨j, hjK⟩).isLt, ?_⟩
    exact TimeProfile.sample_entry_count_pos sample i ⟨j, hjK⟩

theorem expectedCount_eq_integral (D : Riffle.Model) (E : Set Riffle.Word) :
    (Riffle.expectedCount D E : ℝ) =
      ∫ sample : TimeProfile.ShuffleSample (asCuts D),
        (TimeProfile.rowCount (TimeProfile.sampleRow sample)
          (fun row => Riffle.fullList (D := D) row ∈ E) : ℝ)
        ∂TimeProfile.fixedCountMeasure (asCuts D) := by
  classical
  let B (ω : Riffle.FullIndex D) (sample : TimeProfile.ShuffleSample (asCuts D)) : ℝ :=
    (TimeProfile.boxRows (fun j => {ω j}) sample).card
  have hB (ω : Riffle.FullIndex D) (sample : TimeProfile.ShuffleSample (asCuts D)) :
      B ω sample = ∑ i : Fin D.N, if TimeProfile.sampleRow sample i = ω then (1 : ℝ) else 0 := by
    dsimp only [B, TimeProfile.boxRows, TimeProfile.rowsSatisfying]
    rw [Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.mem_singleton]
    by_cases heq : TimeProfile.sampleRow sample i = ω
    · simp [heq]
    · have hn : ¬∀ j, TimeProfile.sampleRow sample i j = ω j := fun h => heq (funext h)
      simp only [if_neg heq, if_neg hn]
  have hcount (sample : TimeProfile.ShuffleSample (asCuts D)) :
      (TimeProfile.rowCount (TimeProfile.sampleRow sample)
        (fun row => Riffle.fullList (D := D) row ∈ E) : ℝ) =
      ∑ ω : Riffle.FullIndex D,
        if Riffle.fullList ω ∈ E then B ω sample else 0 := by
    dsimp only [TimeProfile.rowCount, TimeProfile.rowsSatisfying]
    rw [Finset.natCast_card_filter]
    simp_rw [hB]
    have hsplit (ω : Riffle.FullIndex D) :
        (if Riffle.fullList ω ∈ E then
          ∑ i : Fin D.N, if TimeProfile.sampleRow sample i = ω then (1 : ℝ) else 0
        else 0) = ∑ i : Fin D.N,
          if TimeProfile.sampleRow sample i = ω ∧ Riffle.fullList ω ∈ E then (1 : ℝ) else 0 := by
      by_cases hω : Riffle.fullList ω ∈ E <;> simp [hω]
    simp_rw [hsplit]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ite_and]
    simp
  have hexpected (ω : Riffle.FullIndex D) :
      (∫ sample, B ω sample ∂TimeProfile.fixedCountMeasure (asCuts D)) =
      (D.N : ℝ) * (Riffle.weight D ω : ℝ) := by
    calc
      _ = (D.N : ℝ) * ∏ j, TimeProfile.prob (asProfile D j) (ω j) := by
        simpa only [B, Finset.sum_singleton, asProfile] using
          TimeProfile.expected_box_count (asCuts D)
            (lt_trans Nat.zero_lt_one D.one_lt_N) (fun j => {ω j})
      _ = _ := by simp [Riffle.weight, asProfile_prob]
  symm
  calc
    _ = ∫ sample, ∑ ω : Riffle.FullIndex D,
        if Riffle.fullList ω ∈ E then B ω sample else 0
        ∂TimeProfile.fixedCountMeasure (asCuts D) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hcount
    _ = ∑ ω : Riffle.FullIndex D, ∫ sample,
        (if Riffle.fullList ω ∈ E then B ω sample else 0)
        ∂TimeProfile.fixedCountMeasure (asCuts D) := by
      apply integral_finsetSum
      intro ω _
      exact TimeProfile.fixedCount_integrable (asCuts D) _
    _ = ∑ ω : Riffle.FullIndex D,
        if Riffle.fullList ω ∈ E then (D.N : ℝ) * (Riffle.weight D ω : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : Riffle.fullList ω ∈ E
      · simp only [if_pos hω, hexpected]
      · simp [hω]
    _ = _ := by
      simp [Riffle.expectedCount, Finset.mul_sum, mul_ite]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : Riffle.fullList ω ∈ E <;> simp [hω]

theorem expectedCount_cylinder_eq (x : Riffle.Word) (hx : Riffle.Legal D x)
    (u : Riffle.Word) (hux : u <+: x) :
    (Riffle.expectedCount D (Riffle.Cylinder D u) : ℝ) =
      TimeProfile.prefixMass D.N (asProfile D) (legalVector x hx) u.length := by
  classical
  have huK : u.length ≤ D.K := hux.length_le.trans hx.1
  have hprefix (ω : Riffle.FullIndex D) :
      u <+: Riffle.fullList (D := D) ω ↔
        ∀ j : Fin D.K, j.val < u.length → ω j = legalVector x hx j := by
    constructor
    · intro h j hj
      apply Fin.ext
      rw [legalVector_digit x hx j (hj.trans_le hux.length_le)]
      calc
        (ω j).val = Riffle.digit (Riffle.fullList (D := D) ω) j.val :=
          (Riffle.fullList_digit ω j.isLt).symm
        _ = Riffle.digit u j.val := (Riffle.digit_prefix h hj).symm
        _ = Riffle.digit x j.val := Riffle.digit_prefix hux hj
    · intro h
      have hlen : u.length ≤ (Riffle.fullList (D := D) ω).length := by
        simpa only [Riffle.fullList_length] using huK
      apply List.prefix_iff_getElem.mpr
      refine ⟨hlen, ?_⟩
      intro i hi
      have hiK : i < D.K := hi.trans_le huK
      have hiω : i < (Riffle.fullList (D := D) ω).length := hi.trans_le hlen
      have heq := congrArg Fin.val (h ⟨i, hiK⟩ hi)
      rw [legalVector_digit x hx ⟨i, hiK⟩ (hi.trans_le hux.length_le)] at heq
      have hdigit : Riffle.digit u i = Riffle.digit (Riffle.fullList (D := D) ω) i := by
        rw [Riffle.digit_prefix hux hi, Riffle.fullList_digit ω hiK]
        exact heq.symm
      simpa only [Riffle.digit, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hiω, Option.getD_some] using hdigit
  have hrows (sample : TimeProfile.ShuffleSample (asCuts D)) :
      TimeProfile.rowsSatisfying (TimeProfile.sampleRow sample)
          (fun row => Riffle.fullList (D := D) row ∈ Riffle.Cylinder D u) =
        TimeProfile.prefixRows (legalVector x hx) u.length sample := by
    ext i
    simp only [TimeProfile.rowsSatisfying, TimeProfile.prefixRows,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact (hprefix (TimeProfile.sampleRow sample i)).mp hi.2
    · intro hi
      exact ⟨sampleRow_full D sample i, (hprefix (TimeProfile.sampleRow sample i)).mpr hi⟩
  rw [expectedCount_eq_integral]
  simp_rw [TimeProfile.rowCount, hrows]
  simpa only [asProfile] using TimeProfile.expected_prefix_count (asCuts D)
    (lt_trans Nat.zero_lt_one D.one_lt_N) (legalVector x hx) u.length huK

theorem expectedCount_piece_eq (A : Riffle.Setup D) (s : Riffle.Side) (x : Riffle.Word)
    (hx : x ∈ Riffle.Desc D A.w) (j : Fin D.K)
    (hwj : A.w.length ≤ j.val) (hjx : j.val < x.length) :
    (Riffle.expectedCount D (Riffle.PieceEvent A s x j.val) : ℝ) =
      TimeProfile.sideMass D.N (asProfile D) (legalVector x hx.1)
        A.w.length (sideProbability s) j := by
  classical
  let X := legalVector x hx.1
  have htake (ω : Riffle.FullIndex D) :
      (Riffle.fullList (D := D) ω).take j.val = x.take j.val ↔
        ∀ h : Fin D.K, h.val < j.val → ω h = X h := by
    constructor
    · intro h h' hh'
      have hd := congrArg (fun u => Riffle.digit u h'.val) h
      rw [Riffle.digit_take hh', Riffle.digit_take hh',
        Riffle.fullList_digit ω h'.isLt] at hd
      apply Fin.ext
      change (ω h').val = (legalVector x hx.1 h').val
      rw [legalVector_digit x hx.1 h' (hh'.trans hjx)]
      exact hd
    · intro h
      have hjω : j.val ≤ (Riffle.fullList (D := D) ω).length := by
        simpa only [Riffle.fullList_length] using j.isLt.le
      have hlen : ((Riffle.fullList (D := D) ω).take j.val).length =
          (x.take j.val).length := by
        rw [List.length_take_of_le hjω, List.length_take_of_le hjx.le]
      apply List.ext_getElem hlen
      intro i hi hi'
      have hij : i < j.val := by simpa only [List.length_take_of_le hjω] using hi
      have hiK : i < D.K := hij.trans j.isLt
      have heq := congrArg Fin.val (h ⟨i, hiK⟩ hij)
      change (ω ⟨i, hiK⟩).val = (legalVector x hx.1 ⟨i, hiK⟩).val at heq
      rw [legalVector_digit x hx.1 ⟨i, hiK⟩ (hij.trans hjx)] at heq
      have hdigit : Riffle.digit ((Riffle.fullList (D := D) ω).take j.val) i =
          Riffle.digit (x.take j.val) i := by
        rw [Riffle.digit_take hij, Riffle.digit_take hij, Riffle.fullList_digit ω hiK]
        exact heq
      simpa only [Riffle.digit, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem hi', Option.getD_some] using hdigit
  have hambient (ω : Riffle.FullIndex D)
      (h : ∀ h : Fin D.K, h.val < j.val → ω h = X h) :
      A.w <+: Riffle.fullList (D := D) ω := by
    have hp : A.w <+: x.take j.val := List.prefix_of_prefix_length_le hx.2
      (List.take_prefix j.val x) (by simpa only [List.length_take_of_le hjx.le] using hwj)
    rw [← (htake ω).mpr h] at hp
    exact hp.trans (List.take_prefix j.val _)
  have hevent (sample : TimeProfile.ShuffleSample (asCuts D)) (i : Fin D.N) :
      Riffle.fullList (D := D) (TimeProfile.sampleRow sample i) ∈ Riffle.PieceEvent A s x j.val ↔
        (∀ h : Fin D.K, h.val < j.val → TimeProfile.sampleRow sample i h = X h) ∧
          (match s with
          | .left => TimeProfile.sampleRow sample i j < X j
          | .right => X j < TimeProfile.sampleRow sample i j) := by
    rw [Riffle.pieceEvent_iff s hx hwj hjx]
    constructor
    · rintro ⟨_, ht, hd⟩
      refine ⟨(htake _).mp ht, ?_⟩
      cases s <;> simpa only [X, Fin.lt_def,
        Riffle.fullList_digit (D := D) (TimeProfile.sampleRow sample i) j.isLt,
        legalVector_digit x hx.1 j hjx] using hd
    · rintro ⟨ht, hd⟩
      refine ⟨⟨sampleRow_full D sample i, hambient _ ht⟩, (htake _).mpr ht, ?_⟩
      cases s <;> simpa only [X, Fin.lt_def,
        Riffle.fullList_digit (D := D) (TimeProfile.sampleRow sample i) j.isLt,
        legalVector_digit x hx.1 j hjx] using hd
  let rows (sample : TimeProfile.ShuffleSample (asCuts D)) : Finset (Fin D.N) :=
    match s with
    | .left => TimeProfile.leftSideRows X j sample
    | .right => TimeProfile.rightSideRows X j sample
  have hrows (sample : TimeProfile.ShuffleSample (asCuts D)) :
      TimeProfile.rowsSatisfying (TimeProfile.sampleRow sample)
        (fun row => Riffle.fullList (D := D) row ∈ Riffle.PieceEvent A s x j.val) =
      rows sample := by
    cases s <;> ext i <;>
      simp only [rows, TimeProfile.rowsSatisfying, TimeProfile.leftSideRows,
        TimeProfile.rightSideRows, Finset.mem_filter, Finset.mem_univ, true_and] <;>
      exact hevent sample i
  rw [expectedCount_eq_integral]
  simp_rw [TimeProfile.rowCount, hrows]
  cases s
  · simpa only [rows, sideProbability, asProfile, X] using
      TimeProfile.expected_left_side_count (asCuts D)
        (lt_trans Nat.zero_lt_one D.one_lt_N) X j A.w.length hwj
  · simpa only [rows, sideProbability, asProfile, X] using
      TimeProfile.expected_right_side_count (asCuts D)
        (lt_trans Nat.zero_lt_one D.one_lt_N) X j A.w.length hwj

theorem sideMaximum_eq (A : Riffle.Setup D) (s : Riffle.Side) (v x : Riffle.Word)
    (hx : x ∈ Riffle.Desc D A.w) (hvx : v <+: x) :
    (Riffle.sideMaximum A s v x : ℝ) =
      TimeProfile.sideMaximum D.N (asProfile D) (legalVector x hx.1)
        A.w.length v.length (sideProbability s) := by
  classical
  have hterm (j : Fin D.K) (hwj : A.w.length ≤ j.val) (hjv : j.val < v.length) :
      Real.toNNReal (TimeProfile.sideMass D.N (asProfile D) (legalVector x hx.1)
        A.w.length (sideProbability s) j) =
      Riffle.expectedCount D (Riffle.PieceEvent A s x j.val) := by
    rw [← expectedCount_piece_eq A s x hx j hwj (hjv.trans_le hvx.length_le)]
    simp
  unfold Riffle.sideMaximum TimeProfile.sideMaximum
  apply congrArg (fun z : NNReal => (z : ℝ))
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hb := Finset.mem_Ico.mp hi
    have hiK : i < D.K := hb.2.trans_le (hvx.length_le.trans hx.1.1)
    let j : Fin D.K := ⟨i, hiK⟩
    have hj : j ∈ TimeProfile.positions D.K A.w.length v.length :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
    rw [← hterm j hb.1 hb.2]
    exact Finset.le_sup (f := fun h : Fin D.K =>
      Real.toNNReal (TimeProfile.sideMass D.N (asProfile D) (legalVector x hx.1)
        A.w.length (sideProbability s) h)) hj
  · apply Finset.sup_le
    intro j hj
    have hb := (Finset.mem_filter.mp hj).2
    rw [hterm j hb.1 hb.2]
    exact Finset.le_sup (f := fun i : ℕ =>
      Riffle.expectedCount D (Riffle.PieceEvent A s x i)) (Finset.mem_Ico.mpr hb)

theorem cFAt_eq (A : Riffle.Setup D) (v x : Riffle.Word)
    (hx : x ∈ Riffle.Desc D A.w) (hvx : v <+: x) :
    Riffle.cFAt A v x =
      TimeProfile.cF D.N (asProfile D) (legalVector x hx.1) A.w.length v.length := by
  unfold Riffle.cFAt Riffle.sideFluctuation
  rw [sideMaximum_eq A .left v x hx hvx, sideMaximum_eq A .right v x hx hvx]
  rfl

theorem cF_eq (A : Riffle.Setup D) (y z x : Riffle.Word)
    (hp : Riffle.RawPair A y z) (hx : x ∈ Riffle.Desc D (Riffle.join y z)) :
    Riffle.cF A y z = TimeProfile.cF D.N (asProfile D) (legalVector x hx.1)
      A.w.length (Riffle.join y z).length := by
  have hxA : x ∈ Riffle.Desc D A.w :=
    ⟨hx.1, (Riffle.rawPair_join_desc hp).2.trans hx.2⟩
  calc
    Riffle.cF A y z = Riffle.cFAt A (Riffle.join y z) x :=
      (Riffle.cFAt_continuation hxA hx.2).symm
    _ = _ := cFAt_eq A (Riffle.join y z) x hxA hx.2

theorem rawPair_crossings (A : Riffle.Setup D) (y z x : Riffle.Word)
    (hp : Riffle.RawPair A y z) (hnt : ¬Riffle.Terminal D y z)
    (hx : x ∈ Riffle.Desc D (Riffle.join y z)) :
    TimeProfile.Crossings (asProfile D) (legalVector x hx.1)
      A.w.length (Riffle.join y z).length A.chi := by
  classical
  have hyK : y.length ≠ D.K := fun h => hnt (Or.inl h)
  have hzK : z.length ≠ D.K := fun h => hnt (Or.inr h)
  have hy := Riffle.boundary_nonterminal hp.1 hyK
  have hz := Riffle.boundary_nonterminal hp.2.1 hzK
  have hprefix := Riffle.rawPair_prefix_join hp
  have hyx : y <+: x := hprefix.1.trans hx.2
  have hzx : z <+: x := hprefix.2.trans hx.2
  constructor
  · have hybounds : A.w.length ≤ y.length - 1 ∧ y.length - 1 < y.length := by
      have h := hy.1
      omega
    have hiK : y.length - 1 < D.K :=
      hybounds.2.trans_le (Riffle.boundary_mem_desc hp.1).1.1
    let j : Fin D.K := ⟨y.length - 1, hiK⟩
    have hjx : j.val < x.length := hybounds.2.trans_le hyx.length_le
    let l : Fin D.k := ⟨Riffle.leftIndex A j.val, (Riffle.leftIndex_legal A j.val j.isLt).1⟩
    have hlmass : A.chi ≤ TimeProfile.prob (asProfile D j) l := by
      rw [asProfile_prob]
      exact (Finset.mem_filter.mp (Riffle.leftIndex_mem A j.val j.isLt)).2
    have hlt : l < legalVector x hx.1 j := by
      change Riffle.leftIndex A j.val < (legalVector x hx.1 j).val
      rw [legalVector_digit x hx.1 j hjx, ← Riffle.digit_prefix hyx hybounds.2]
      exact hy.2.1
    refine ⟨j, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hybounds.1,
        hybounds.2.trans_le hprefix.1.length_le⟩
    · exact hlmass.trans (Finset.single_le_sum
        (fun a _ => TimeProfile.prob_nonneg (asProfile D j) a)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))
  · have hzbounds : A.w.length ≤ z.length - 1 ∧ z.length - 1 < z.length := by
      have h := hz.1
      omega
    have hiK : z.length - 1 < D.K :=
      hzbounds.2.trans_le (Riffle.boundary_mem_desc hp.2.1).1.1
    let j : Fin D.K := ⟨z.length - 1, hiK⟩
    have hjx : j.val < x.length := hzbounds.2.trans_le hzx.length_le
    let l : Fin D.k := ⟨Riffle.rightIndex A j.val, (Riffle.rightIndex_legal A j.val j.isLt).1⟩
    have hlmass : A.chi ≤ TimeProfile.prob (asProfile D j) l := by
      rw [asProfile_prob]
      exact (Finset.mem_filter.mp (Riffle.rightIndex_mem A j.val j.isLt)).2
    have hlt : legalVector x hx.1 j < l := by
      change (legalVector x hx.1 j).val < Riffle.rightIndex A j.val
      rw [legalVector_digit x hx.1 j hjx, ← Riffle.digit_prefix hzx hzbounds.2]
      exact hz.2.1
    refine ⟨j, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzbounds.1,
        hzbounds.2.trans_le hprefix.2.length_le⟩
    · exact hlmass.trans (Finset.single_le_sum
        (fun a _ => TimeProfile.prob_nonneg (asProfile D j) a)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))

theorem stop_stableAt (A : Riffle.Setup D) (y z x : Riffle.Word)
    (hx : Riffle.Legal D x) (F : ℝ) (hF : Riffle.cF A y z = (F : WithBot ℝ))
    (hstop : Riffle.Stop A y z x) :
    TimeProfile.StableAt D.N (asProfile D) (legalVector x hx)
      A.b A.w.length x.length F A.delta := by
  unfold TimeProfile.StableAt
  rw [← cL_prefix_eq A x hx x List.prefix_rfl]
  exact ((Riffle.stop_iff_sub_lt hF).mp hstop).le

theorem gamma_parentCrossing (A : Riffle.Setup D) (y z x : Riffle.Word)
    (hp : Riffle.RawPair A y z) (hroot : ¬Riffle.Stop A y z (Riffle.join y z))
    (hx : x ∈ Riffle.Gamma A y z) (F : ℝ) (hF : Riffle.cF A y z = (F : WithBot ℝ)) :
    TimeProfile.ParentCrossing D.N (asProfile D) (legalVector x hx.1.1.1)
      A.b A.w.length (Riffle.join y z).length x.length F A.delta := by
  have h := Riffle.gamma_first_crossing hp hroot hx
  have hlen := h.1
  refine ⟨by omega, by omega, ?_⟩
  rw [← cL_parent_eq A x hx.1.1.1]
  exact (Riffle.not_stop_iff_sub_ge hF).mp h.2.2.1

theorem ambientApproximation_iff (A : Riffle.Setup D) (x : Riffle.Word)
    (hx : x ∈ Riffle.Desc D A.w) (r er eb : ℝ) :
    TimeProfile.AmbientApproximation D.N (asProfile D) (legalVector x hx.1)
        A.w.length r A.b er eb ↔
      |(A.w.length : ℝ) / Real.log (D.N : ℝ) - r| ≤ er ∧
      |Real.log (Riffle.expectedCount D (Riffle.Cylinder D A.w) : ℝ) /
          Real.log (D.N : ℝ) - A.b| ≤ eb := by
  rw [expectedCount_cylinder_eq x hx.1 A.w hx.2]
  rfl

end

end InhomogeneousShuffle.FirstMoment.Model
