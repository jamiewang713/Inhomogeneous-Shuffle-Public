import Shuffle.Conditioning
import Mathlib.Logic.Equiv.Set

/-! Uniform fixed-histogram columns and conditioning on prescribed labelled rows.
The definitions and conclusions implement D6 and C2 of the frozen contract. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Shuffle

def digitCount {V : Type*} [Fintype V] {k : ℕ} (f : V → Fin k) (a : Fin k) : ℕ :=
  Fintype.card {v : V // f v = a}

theorem sum_digitCount {V : Type*} [Fintype V] {k : ℕ} (f : V → Fin k) :
    ∑ a, digitCount f a = Fintype.card V := by
  unfold digitCount
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f)

structure Histogram (V : Type*) [Fintype V] (k : ℕ) where
  count : Fin k → ℕ
  total : ∑ a, count a = Fintype.card V

abbrev FixedColumn {V : Type*} [Fintype V] {k : ℕ} (h : Histogram V k) :=
  {f : V → Fin k // ∀ a, digitCount f a = h.count a}

noncomputable instance (priority := 2000) fixedColumnFintype
    {V : Type*} [Fintype V] {k : ℕ} (h : Histogram V k) : Fintype (FixedColumn h) :=
  Fintype.ofFinite _

private def sigmaFstFiberEquiv {k : ℕ} (n : Fin k → ℕ) (a : Fin k) :
    {x : (Σ b : Fin k, Fin (n b)) // x.fst = a} ≃ Fin (n a) where
  toFun := fun x => by
    rcases x with ⟨⟨b, y⟩, hb⟩
    dsimp only at hb
    subst b
    exact y
  invFun := fun y => ⟨⟨a, y⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨b, y⟩, hb⟩
    dsimp only at hb
    subst b
    rfl
  right_inv := by intro y; rfl

theorem fixedColumn_nonempty {V : Type*} [Fintype V] {k : ℕ} (h : Histogram V k) :
    Nonempty (FixedColumn h) := by
  have hcard : Fintype.card V = Fintype.card (Σ a : Fin k, Fin (h.count a)) := by
    rw [Fintype.card_sigma]
    simpa using h.total.symm
  let e := Fintype.equivOfCardEq hcard
  let f : V → Fin k := fun v => (e v).fst
  refine ⟨⟨f, ?_⟩⟩
  intro a
  let ef : {v : V // f v = a} ≃ {x : (Σ b : Fin k, Fin (h.count b)) // x.fst = a} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  unfold digitCount
  rw [Fintype.card_congr (ef.trans (sigmaFstFiberEquiv h.count a)), Fintype.card_fin]

instance fixedColumnNonempty {V : Type*} [Fintype V] {k : ℕ} (h : Histogram V k) :
    Nonempty (FixedColumn h) := fixedColumn_nonempty h

def columnLaw {V : Type*} [Fintype V] {k : ℕ} (h : Histogram V k) :
    FiniteLaw (FixedColumn h) := FiniteLaw.uniform _

theorem histogram_no_digits {V : Type*} [Fintype V] (h : Histogram V 0) :
    Fintype.card V = 0 := by
  rw [← h.total]
  simp

namespace Histogram

variable {V : Type*} [Fintype V] {k : ℕ}

private def splitDigitFiber (R : Set V) (f : V → Fin k) (a : Fin k) :
    {v : V // f v = a} ≃
      {v : R // f v.val = a} ⊕ {v : (Rᶜ : Set V) // f v.val = a} where
  toFun := fun v => if hv : v.val ∈ R then
    Sum.inl ⟨⟨v.val, hv⟩, v.property⟩ else Sum.inr ⟨⟨v.val, hv⟩, v.property⟩
  invFun := fun v => match v with
    | Sum.inl x => ⟨x.val.val, x.property⟩
    | Sum.inr x => ⟨x.val.val, x.property⟩
  left_inv := by
    intro v
    by_cases hv : v.val ∈ R <;> simp [hv]
  right_inv := by
    rintro (⟨⟨v, hv⟩, hval⟩ | ⟨⟨v, hv⟩, hval⟩)
    · simp [hv]
    · have hv' : v ∉ R := hv
      simp [hv']

theorem digitCount_split (R : Set V) (f : V → Fin k) (a : Fin k) :
    digitCount f a = digitCount (fun v : R => f v.val) a +
      digitCount (fun v : (Rᶜ : Set V) => f v.val) a := by
  unfold digitCount
  rw [Fintype.card_congr (splitDigitFiber R f a), Fintype.card_sum]

def Prescribed (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (f : FixedColumn h) : Prop := ∀ v : R, f.val v.val = b v

def Admissible (h : Histogram V k) (R : Set V) (b : R → Fin k) : Prop :=
  ∀ a, digitCount b a ≤ h.count a

def residual (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (hb : h.Admissible R b) : Histogram (Rᶜ : Set V) k where
  count a := h.count a - digitCount b a
  total := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun a _ => hb a), h.total, sum_digitCount]
    exact (Fintype.card_subtype_compl (fun v : V => v ∈ R)).symm

private def glue (R : Set V) (b : R → Fin k) (g : (Rᶜ : Set V) → Fin k) : V → Fin k :=
  fun v => if hv : v ∈ R then b ⟨v, hv⟩ else g ⟨v, hv⟩

omit [Fintype V] in
private theorem glue_restrict_left (R : Set V) (b : R → Fin k)
    (g : (Rᶜ : Set V) → Fin k) :
    (fun v : R => glue R b g v.val) = b := by
  funext v
  simp [glue, v.property]

omit [Fintype V] in
private theorem glue_restrict_right (R : Set V) (b : R → Fin k)
    (g : (Rᶜ : Set V) → Fin k) :
    (fun v : (Rᶜ : Set V) => glue R b g v.val) = g := by
  funext v
  have hv : v.val ∉ R := v.property
  simp [glue, hv]

def glueColumn (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (hb : h.Admissible R b) (g : FixedColumn (h.residual R b hb)) : FixedColumn h :=
  ⟨glue R b g.val, by
    intro a
    rw [digitCount_split R, glue_restrict_left, glue_restrict_right, g.property]
    exact Nat.add_sub_of_le (hb a)⟩

theorem glueColumn_prescribed (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (hb : h.Admissible R b) (g : FixedColumn (h.residual R b hb)) :
    h.Prescribed R b (h.glueColumn R b hb g) := by
  intro v
  exact congrFun (glue_restrict_left R b g.val) v

theorem prescribed_admissible (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (f : FixedColumn h) (hf : h.Prescribed R b f) : h.Admissible R b := by
  intro a
  have heq := digitCount_split R f.val a
  have hleft : (fun v : R => f.val v.val) = b := funext hf
  rw [f.property, hleft] at heq
  omega

def restrictColumn (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (hb : h.Admissible R b) (f : FixedColumn h) (hf : h.Prescribed R b f) :
    FixedColumn (h.residual R b hb) :=
  ⟨(fun v : (Rᶜ : Set V) => f.val v.val), by
    intro a
    have heq := digitCount_split R f.val a
    have hleft : (fun v : R => f.val v.val) = b := funext hf
    rw [f.property, hleft] at heq
    change digitCount (fun v : (Rᶜ : Set V) => f.val v.val) a = h.count a - digitCount b a
    omega⟩

/-- The complete positive prescription fibre is in bijection with legal
assignments of the exact residual histogram. -/
def prescriptionFiberEquiv (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (hb : h.Admissible R b) :
    {f : FixedColumn h // h.Prescribed R b f} ≃ FixedColumn (h.residual R b hb) where
  toFun f := h.restrictColumn R b hb f.val f.property
  invFun g := ⟨h.glueColumn R b hb g, h.glueColumn_prescribed R b hb g⟩
  left_inv := by
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ R
    · change glue R b (fun v : (Rᶜ : Set V) => f.val.val v.val) v = f.val.val v
      rw [glue, dif_pos hv]
      exact (f.property ⟨v, hv⟩).symm
    · change glue R b (fun v : (Rᶜ : Set V) => f.val.val v.val) v = f.val.val v
      simp [glue, hv]
  right_inv := by
    intro g
    apply Subtype.ext
    exact glue_restrict_right R b g.val

theorem exists_prescribed_iff (h : Histogram V k) (R : Set V) (b : R → Fin k) :
    (∃ f : FixedColumn h, h.Prescribed R b f) ↔ h.Admissible R b := by
  constructor
  · rintro ⟨f, hf⟩
    exact h.prescribed_admissible R b f hf
  · intro hb
    obtain ⟨g⟩ := fixedColumn_nonempty (h.residual R b hb)
    exact ⟨h.glueColumn R b hb g, h.glueColumn_prescribed R b hb g⟩

/-- C2: positivity is exactly the per-digit admissibility condition. -/
theorem prescription_prob_pos_iff (h : Histogram V k) (R : Set V) (b : R → Fin k) :
    0 < (columnLaw h).prob (h.Prescribed R b) ↔ h.Admissible R b := by
  rw [columnLaw, FiniteLaw.uniform_prob_pos_iff, h.exists_prescribed_iff]

/-- Every legal residual assignment has exactly its uniform conditional mass. -/
theorem conditional_residual_point (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (hb : h.Admissible R b) (g : FixedColumn (h.residual R b hb)) :
    (columnLaw h).conditionalProb (h.Prescribed R b)
      (fun f => (fun v : (Rᶜ : Set V) => f.val v.val) = g.val) =
        (columnLaw (h.residual R b hb)).mass g := by
  have hsingle : ∃ f : {f : FixedColumn h //
      (fun v : (Rᶜ : Set V) => f.val v.val) = g.val ∧ h.Prescribed R b f},
      ∀ f', f' = f := by
    refine ⟨⟨h.glueColumn R b hb g,
      ⟨glue_restrict_right R b g.val, h.glueColumn_prescribed R b hb g⟩⟩, ?_⟩
    intro f
    apply Subtype.ext
    apply Subtype.ext
    funext v
    change f.val.val v = glue R b g.val v
    by_cases hv : v ∈ R
    · rw [glue, dif_pos hv]
      exact f.property.2 ⟨v, hv⟩
    · rw [glue, dif_neg hv]
      exact congrFun f.property.1 ⟨v, hv⟩
  change (FiniteLaw.uniform (FixedColumn h)).conditionalProb _ _ = _
  rw [FiniteLaw.uniform_conditionalProb]
  change _ = 1 / (Fintype.card (FixedColumn (h.residual R b hb)) : ℝ)
  congr 1
  · trans ((1 : ℕ) : ℝ)
    · apply congrArg (fun n : ℕ => (n : ℝ))
      have hcard := Fintype.card_eq_one_iff.mpr hsingle
      simpa only [Fintype.card_eq_nat_card] using hcard
    · exact Nat.cast_one
  · apply congrArg (fun n : ℕ => (n : ℝ))
    exact Fintype.card_congr (h.prescriptionFiberEquiv R b hb)

/-- C2 as an equality of laws on actual residual row assignments. The map is
literal restriction, including away from the conditioning event. -/
theorem conditional_residual_law (h : Histogram V k) (R : Set V) (b : R → Fin k)
    (hb : h.Admissible R b) :
    ((columnLaw h).condition (h.Prescribed R b)
        ((h.prescription_prob_pos_iff R b).mpr hb)).map
      (fun f => fun v : (Rᶜ : Set V) => f.val v.val) =
    (columnLaw (h.residual R b hb)).map Subtype.val := by
  apply FiniteLaw.ext_mass
  intro g
  change (((columnLaw h).condition (h.Prescribed R b)
      ((h.prescription_prob_pos_iff R b).mpr hb)).prob
      (fun f => (fun v : (Rᶜ : Set V) => f.val v.val) = g)) =
    (columnLaw (h.residual R b hb)).prob (fun f => f.val = g)
  rw [FiniteLaw.condition_prob]
  by_cases hg : ∀ a, digitCount g a = (h.residual R b hb).count a
  · let G : FixedColumn (h.residual R b hb) := ⟨g, hg⟩
    have hpoint : (columnLaw (h.residual R b hb)).prob (fun f => f.val = g) =
        (columnLaw (h.residual R b hb)).mass G := by
      change (columnLaw (h.residual R b hb)).prob (fun f => f.val = G.val) = _
      simp only [FiniteLaw.prob, ← Subtype.ext_iff, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [hpoint]
    exact h.conditional_residual_point R b hb G
  · have hempty : (fun f : FixedColumn h =>
        (fun v : (Rᶜ : Set V) => f.val v.val) = g ∧ h.Prescribed R b f) =
        (fun _ => False) := by
      funext f
      apply propext
      constructor
      · rintro ⟨hfg, hf⟩
        apply hg
        intro a
        have heq := (h.restrictColumn R b hb f hf).property a
        change digitCount (fun v : (Rᶜ : Set V) => f.val v.val) a = _ at heq
        rwa [hfg] at heq
      · exact False.elim
    have hempty' : (fun f : FixedColumn (h.residual R b hb) => f.val = g) =
        (fun _ => False) := by
      funext f
      apply propext
      constructor
      · intro hfg
        exact hg (hfg ▸ f.property)
      · exact False.elim
    rw [FiniteLaw.conditionalProb, hempty, hempty', FiniteLaw.prob_false]
    simp

end Histogram

/-- D6: independent uniform columns with their prescribed feasible histograms. -/
def fixedMatrixLaw {ι V : Type*} [Fintype ι] [Fintype V] {k : ℕ}
    (h : ι → Histogram V k) : FiniteLaw (∀ i, FixedColumn (h i)) :=
  FiniteLaw.product (fun i => columnLaw (h i))

private theorem map_product_coordinates {ι : Type*} [Fintype ι]
    {X Y : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    (p : ∀ i, FiniteLaw (X i)) (f : ∀ i, X i → Y i) :
    (FiniteLaw.product p).map (fun x i => f i (x i)) =
      FiniteLaw.product (fun i => (p i).map (f i)) := by
  apply FiniteLaw.ext_mass
  intro y
  change (FiniteLaw.product p).prob (fun x => (fun i => f i (x i)) = y) =
    ∏ i, (p i).prob (fun x => f i x = y i)
  have heq : (fun x : ∀ i, X i => (fun i => f i (x i)) = y) =
      (fun x : ∀ i, X i => ∀ i, f i (x i) = y i) := by
    funext x
    exact propext ⟨congrFun, funext⟩
  rw [heq]
  exact FiniteLaw.product_prob_rectangle p (fun i x => f i x = y i)

/-- C2: independent columns conditioned on separate admissible prescriptions
retain the product of their residual uniform laws. The index set may be empty. -/
theorem conditional_fixedMatrix_residual_law {ι V : Type*} [Fintype ι] [Fintype V]
    {k : ℕ} (h : ι → Histogram V k) (R : ι → Set V) (b : ∀ i, R i → Fin k)
    (hb : ∀ i, (h i).Admissible (R i) (b i)) :
    ((fixedMatrixLaw h).condition
      (fun x => ∀ i, (h i).Prescribed (R i) (b i) (x i))
      (FiniteLaw.product_prob_rectangle_pos (fun i => columnLaw (h i))
        (fun i => (h i).Prescribed (R i) (b i))
        (fun i => ((h i).prescription_prob_pos_iff (R i) (b i)).mpr (hb i)))).map
      (fun x i => fun v : ((R i)ᶜ : Set V) => (x i).val v.val) =
      FiniteLaw.product (fun i =>
        (columnLaw ((h i).residual (R i) (b i) (hb i))).map Subtype.val) := by
  unfold fixedMatrixLaw
  rw [FiniteLaw.condition_product_rectangle]
  rw [map_product_coordinates
    (fun i => (columnLaw (h i)).condition ((h i).Prescribed (R i) (b i))
      (((h i).prescription_prob_pos_iff (R i) (b i)).mpr (hb i)))
    (fun i f => fun v : ((R i)ᶜ : Set V) => f.val v.val)]
  congr 1
  funext i
  exact (h i).conditional_residual_law (R i) (b i) (hb i)

end Shuffle
