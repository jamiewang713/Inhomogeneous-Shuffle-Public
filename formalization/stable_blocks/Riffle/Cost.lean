import Riffle.Model
import Riffle.Words

namespace Riffle

/-- S01: legal pile costs are nonnegative, including probability-one columns. -/
theorem legal_cost_nonneg {D : Model} {x : Word} (hx : Legal D x) {i : ℕ}
    (hi : i < x.length) : 0 ≤ Real.log ((D.N : ℝ) / (D.n i (digit x i) : ℝ)) := by
  have hp : (0 : ℝ) < D.n i (digit x i) := by exact_mod_cast (hx.2 i hi).2
  have hle : (D.n i (digit x i) : ℝ) ≤ D.N := by
    exact_mod_cast count_le D i (digit x i) (hi.trans_le hx.1) (hx.2 i hi).1
  exact Real.log_nonneg ((one_le_div hp).mpr hle)

theorem cL_antitone {D : Model} {A : Setup D} {x u : Word}
    (_hx : x ∈ Desc D A.w) (hu : u ∈ Desc D A.w) (hxu : x <+: u) :
    cL A u ≤ cL A x := by
  have hn : (0 : ℝ) < Real.log (D.N : ℝ) := Real.log_pos (by exact_mod_cast D.one_lt_N)
  have hsub : Finset.Ico A.w.length x.length ⊆ Finset.Ico A.w.length u.length := by
    intro i hi
    exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hi).1,
      (Finset.mem_Ico.mp hi).2.trans_le hxu.length_le⟩
  have hs : (∑ i ∈ Finset.Ico A.w.length x.length,
      Real.log ((D.N : ℝ) / (D.n i (digit x i) : ℝ))) ≤
      ∑ i ∈ Finset.Ico A.w.length u.length,
      Real.log ((D.N : ℝ) / (D.n i (digit u i) : ℝ)) := by
    calc
      _ = ∑ i ∈ Finset.Ico A.w.length x.length,
          Real.log ((D.N : ℝ) / (D.n i (digit u i) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [digit_prefix hxu (Finset.mem_Ico.mp hi).2]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun i hi _ => legal_cost_nonneg hu.1 (Finset.mem_Ico.mp hi).2)
  exact sub_le_sub_left (div_le_div_of_nonneg_right hs hn.le) A.b

theorem stop_persistent {D : Model} {A : Setup D} {y z x u : Word}
    (hx : x ∈ Desc D A.w) (hu : u ∈ Desc D A.w) (hxu : x <+: u)
    (hs : Stop A y z x) : Stop A y z u := by
  exact lt_of_le_of_lt (WithBot.coe_le_coe.mpr (cL_antitone hx hu hxu)) hs

/-- F05: the encoding preserves the source's real strict inequality. -/
theorem stop_iff_sub_lt {D : Model} {A : Setup D} {y z x : Word} {f : ℝ}
    (hf : cF A y z = (f : WithBot ℝ)) :
    Stop A y z x ↔ cL A x - f < A.delta := by
  simp only [Stop, hf, ← WithBot.coe_add, WithBot.coe_lt_coe]
  constructor <;> intro h <;> linarith

theorem not_stop_iff_sub_ge {D : Model} {A : Setup D} {y z x : Word} {f : ℝ}
    (hf : cF A y z = (f : WithBot ℝ)) :
    ¬Stop A y z x ↔ A.delta ≤ cL A x - f := by
  rw [stop_iff_sub_lt hf, not_lt]

theorem not_stop_of_bottom {D : Model} {A : Setup D} {y z x : Word}
    (hf : cF A y z = ⊥) : ¬Stop A y z x := by
  simp [Stop, hf]

theorem extendedLog_zero (D : Model) : extendedLog D 0 = ⊥ := by
  simp [extendedLog]

theorem extendedLog_of_pos (D : Model) {q : ℝ} (hq : 0 < q) :
    extendedLog D q = ((Real.log q / Real.log (D.N : ℝ) : ℝ) : WithBot ℝ) := by
  simp [extendedLog, ne_of_gt hq]

end Riffle
