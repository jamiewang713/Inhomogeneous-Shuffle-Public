import EdgeLocalization.Collision.Column

/-! Frozen additive definitions C.D06–C.D08 and C.D13–C.D14.
The matrix law is the product of the actual uniform fixed-column laws. -/

noncomputable section

namespace EdgeLocalization

open scoped Classical

def FixedMatrix (N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ) : Type :=
  ∀ j : Fin K, FixedColumn N k (n j)

instance fixedMatrixFintype (N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ) :
    Fintype (FixedMatrix N n) := by
  unfold FixedMatrix
  exact @Pi.instFintype (Fin K) (fun j => FixedColumn N k (n j))
    (Classical.typeDecidableEq _) inferInstance (fun j => fixedColumnFintype N k (n j))

def matrixLaw {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (hn : ∀ j, ∑ a, n j a = N) : FiniteLaw (FixedMatrix N n) :=
  FiniteLaw.pi (Ω := fun j : Fin K => FixedColumn N k (n j))
    (fun j => columnLaw (n j) (hn j))

def prefixWord {M k : ℕ} (x : Fin M → Fin k) : List ℕ :=
  List.ofFn (fun t => (x t).val)

def rawRow {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (ω : FixedMatrix N n) (i : Fin N) : List ℕ :=
  List.ofFn (fun j : Fin K => ((ω j).val i).val)

def rowsOfLabels {N : ℕ} (R : Fin N → List ℕ) : ℕ → List ℕ :=
  fun i => if hi : i < N then R ⟨i, hi⟩ else []

def rawRows {N K k : ℕ} (n : Fin K → Fin k → ℕ)
    (ω : FixedMatrix N n) : ℕ → List ℕ :=
  rowsOfLabels (rawRow n ω)

def prefixMass (N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : M ≤ K) (x : Fin M → Fin k) : ℝ :=
  ∏ t : Fin M, singleFactor N (n (Fin.castLE hM t)) (x t)

def prefixPairFactor (N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : M ≤ K) (x : Fin M → Fin k) : ℝ :=
  ∏ t : Fin M, pairFactor N (n (Fin.castLE hM t)) (x t) (x t)

def tailCollisionFactor (N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)
    (M : ℕ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin K => M ≤ j.val), coincidenceFactor N (n j)

def tailSquareFactor (N : ℕ) {K k : ℕ} (n : Fin K → Fin k → ℕ)
    (M : ℕ) : ℝ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin K => M ≤ j.val),
    ∑ a : Fin k, (singleFactor N (n j) a) ^ 2

def prefixMean (N : ℕ) {K k M : ℕ} (n : Fin K → Fin k → ℕ)
    (hM : M ≤ K) (x : Fin M → Fin k) : ℝ :=
  (N : ℝ) * prefixMass N n hM x

end EdgeLocalization
