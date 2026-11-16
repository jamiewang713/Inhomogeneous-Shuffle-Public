import RiffleUpperV2.Localization.EdgeMoments
import RiffleUpperV2.GraphOverlap.FactorialTail

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace RiffleUpperV2.Localization
open TimeProfile RiffleLowerV2.Factorial

def restrictedWordCount {k n d : ℕ} {cuts : Cuts k n d}
    (R : Finset (Fin n)) (w : Word k d) (ω : Sample cuts) : ℕ :=
  (R.filter (fun r => rowWord ω r = w)).card

private def restrictedEmbeddingEquiv {A : Type*} (P : A → Prop) (q : ℕ) :
    {e : Fin q ↪ A // ∀ i, P (e i)} ≃ (Fin q ↪ {a : A // P a}) where
  toFun e := ⟨fun i => ⟨e.val i,e.property i⟩,fun i j h => e.val.injective (congrArg Subtype.val h)⟩
  invFun e := ⟨⟨fun i => (e i).val,fun i j h => e.injective (Subtype.ext h)⟩,fun i => (e i).property⟩
  left_inv e := by apply Subtype.ext; apply Function.Embedding.ext; intro i; rfl
  right_inv e := by apply Function.Embedding.ext; intro i; rfl

theorem embedding_indicator_sum {A : Type*} [Fintype A] (P : A → Prop) (q : ℕ) :
    (∑ e : Fin q ↪ A, if ∀ i, P (e i) then (1:ℝ) else 0) =
      RiffleLowerV2.falling (Fintype.card {a : A // P a}) q := by
  have h := Fintype.card_congr (restrictedEmbeddingEquiv P q)
  rw [Fintype.card_subtype,Fintype.card_embedding_eq,Fintype.card_fin] at h
  have hh := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    RiffleLowerV2.falling] using hh

theorem constantColumnRequest {k n d q : ℕ} (cuts : Cuts k n d) (j : Fin d)
    (a : Fin k) (e : Fin q ↪ Fin n) :
    RiffleLowerV2.expect (columnPMF cuts j)
      (fun c => if ∀ i, c.val (e i)=a then 1 else 0) =
      RiffleLowerV2.falling (cuts.count j a) q / RiffleLowerV2.falling n q := by
  have h := column_request_probability cuts j (fun _ : Fin q => a) e
  have hp : (∏ b : Fin k, RiffleLowerV2.falling (cuts.count j b)
      (Nat.card {i : Fin q // a = b})) = RiffleLowerV2.falling (cuts.count j a) q := by
    rw [Finset.prod_eq_single a]
    · simp [Nat.card_eq_fintype_card,Fintype.card_subtype]
    · intro b _ hab
      have hab' : a ≠ b := Ne.symm hab
      simp [hab',Nat.card_eq_fintype_card,Fintype.card_subtype,RiffleLowerV2.falling]
    · simp
  rw [hp,Fintype.card_fin] at h
  convert h using 1
  congr 1
  funext c
  split_ifs <;> rfl

theorem constantWordRequest {k n d q : ℕ} (cuts : Cuts k n d)
    (w : Word k d) (e : Fin q ↪ Fin n) :
    probability (fixedCountPMF cuts) (fun ω => ∀ i, rowWord ω (e i)=w) =
      ∏ j : Fin d, RiffleLowerV2.falling (cuts.count j (w.get j)) q / RiffleLowerV2.falling n q := by
  let f : ∀ j, ColumnAssignments cuts j → ℝ := fun j c => if ∀ i, c.val (e i)=w.get j then 1 else 0
  have he (ω : Sample cuts) : (∀ i, rowWord ω (e i)=w) ↔ ∀ j, ∀ i, (ω j).val (e i)=w.get j := by
    constructor
    · intro h j i
      exact (RiffleLowerV2.rowWord_get ω (e i) j).symm.trans (congrArg (fun v : Word k d => v.get j) (h i))
    · intro h i
      apply List.Vector.ext
      intro j
      exact (RiffleLowerV2.rowWord_get ω (e i) j).trans (h j i)
  have hf (ω : Sample cuts) : (if ∀ i, rowWord ω (e i)=w then (1:ℝ) else 0) = ∏ j, f j (ω j) := by
    by_cases h : ∀ j, ∀ i, (ω j).val (e i)=w.get j
    · simp [he,h,f]
    · rw [if_neg (fun hh => h ((he ω).mp hh))]
      obtain ⟨j,hj⟩ := not_forall.mp h
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  have hh : RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
      (fun ω => ∏ j, f j (ω j)) = _ := request_column_product cuts f
  calc
    _ = RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
        (fun ω => ∏ j, f j (ω j)) := by
      unfold RiffleUpperV2.probability RiffleLowerV2.probability
      congr 1
      funext ω
      convert hf ω using 1
      split_ifs <;> rfl
    _ = _ := hh
    _ = _ := Finset.prod_congr rfl (fun j _ => constantColumnRequest cuts j (w.get j) e)

theorem restrictedWordFactorialMoment {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (w : Word k d) (q : ℕ) :
    expect (fixedCountPMF cuts) (fun ω => RiffleLowerV2.falling (restrictedWordCount R w ω) q) =
      RiffleLowerV2.falling R.card q *
        ∏ j : Fin d, RiffleLowerV2.falling (cuts.count j (w.get j)) q / RiffleLowerV2.falling n q := by
  have hc (ω : Sample cuts) : Fintype.card {r : R // rowWord ω r.val = w} = restrictedWordCount R w ω := by
    simp only [Fintype.card_subtype,restrictedWordCount]
    apply Finset.card_bij (fun r _ => r.val)
    · intro r hr
      exact Finset.mem_filter.mpr ⟨r.property,(Finset.mem_filter.mp hr).2⟩
    · intro r hr s hs h
      exact Subtype.ext h
    · intro r hr
      refine ⟨⟨r,(Finset.mem_filter.mp hr).1⟩,?_,rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hr).2⟩
  have hpoint (ω : Sample cuts) : RiffleLowerV2.falling (restrictedWordCount R w ω) q =
      ∑ e : Fin q ↪ R, if ∀ i, rowWord ω (e i).val = w then (1:ℝ) else 0 := by
    have h := embedding_indicator_sum (A := R) (fun r => rowWord ω r.val=w) q
    rw [← hc ω]
    convert h.symm using 1
    · congr 1
      simp only [← Nat.card_eq_fintype_card]
    · apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> rfl
  change RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts) _ = _
  simp_rw [hpoint]
  rw [RiffleLowerV2.Factorial.expect_sum]
  have hp (e : Fin q ↪ R) :
      RiffleLowerV2.expect (TimeProfile.fixedCountPMF cuts)
        (fun ω => if ∀ i, rowWord ω (e i).val=w then (1:ℝ) else 0) =
      ∏ j : Fin d, RiffleLowerV2.falling (cuts.count j (w.get j)) q / RiffleLowerV2.falling n q :=
by
    have h := constantWordRequest cuts w (e.trans (Function.Embedding.subtype (fun r => r ∈ R)))
    simpa only [RiffleUpperV2.probability,RiffleLowerV2.probability, Function.Embedding.trans_apply,
      Function.Embedding.subtype_apply] using h
  simp_rw [hp]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_embedding_eq,Fintype.card_fin,Fintype.card_coe,RiffleLowerV2.falling]

theorem restrictedWordFactorialMoment_le {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (w : Word k d) (q : ℕ) :
    expect (fixedCountPMF cuts) (fun ω => RiffleLowerV2.falling (restrictedWordCount R w ω) q) ≤
      RiffleLowerV2.falling R.card q * RiffleLowerV2.wordMass cuts w ^ q := by
  rw [restrictedWordFactorialMoment, GraphOverlap.wordMass_eq_prod, ← Finset.prod_pow]
  apply mul_le_mul_of_nonneg_left _ (falling_nonneg _ _)
  apply Finset.prod_le_prod (fun _ _ => by apply div_nonneg <;> exact falling_nonneg _ _)
  intro j _
  exact GraphOverlap.descFactorial_ratio_le_pow (GraphOverlap.count_le_population cuts j (w.get j)) q

theorem restrictedWordBinomialMoment_le {k n d : ℕ} (cuts : Cuts k n d)
    (R : Finset (Fin n)) (w : Word k d) (q : ℕ) :
    expect (fixedCountPMF cuts) (fun ω => ((restrictedWordCount R w ω).choose q : ℝ)) ≤
      (R.card.choose q : ℝ) * RiffleLowerV2.wordMass cuts w ^ q := by
  simp_rw [choose_eq_falling_div]
  change RiffleLowerV2.expect _ _ ≤ _
  rw [expect_div]
  have h := div_le_div_of_nonneg_right (restrictedWordFactorialMoment_le cuts R w q)
    (Nat.cast_nonneg q.factorial)
  calc
    _ ≤ (RiffleLowerV2.falling R.card q * RiffleLowerV2.wordMass cuts w ^ q) / q.factorial := h
    _ = _ := by ring

end RiffleUpperV2.Localization
