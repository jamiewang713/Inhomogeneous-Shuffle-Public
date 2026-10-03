import RiffleUpperV2.Anchor.Definitions
import RiffleUpperV2.Localization.Prefixes
import RiffleUpperV2.Localization.Scalars

noncomputable section
namespace RiffleUpperV2.Localization
open Anchor

/-- Scalar exponent of the conditional anchored mean, at the original scale N. -/
def meanExponent {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (R : Finset (Fin n))
    (x : Prefix k d) : ℝ := normalizedExponent N (anchoredMean cuts R x)

def boundaryFluctuation {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d)
    (R : Finset (Fin n)) (v : Prefix k d) : ℝ := fluctuation N (sideScale cuts R v)

/-- The join v fixes the fluctuation throughout its descendants. -/
def Stops {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) (δ : ℝ) (x : Prefix k d) : Prop :=
  meanExponent N cuts R x - boundaryFluctuation N cuts R v < δ

/-- The first successful test, with a full-depth fallback if none succeeds.
The test is made at the join itself, so an immediate stop is included. -/
def FirstCut {k d : ℕ} (v : Prefix k d) (Q : Prefix k d → Prop)
    (x : Prefix k d) : Prop :=
  IsPrefix v x ∧ (Q x ∨ x.1.val = d) ∧
  ∀ u : Prefix k d, IsPrefix v u → IsPrefix u x → u.1.val < x.1.val → ¬ Q u

def Stable {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) (δ : ℝ) (x : Prefix k d) : Prop :=
  Legal cuts R x ∧ FirstCut v (Stops N cuts R v δ) x

def ProperStable {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) (δ : ℝ) (x : Prefix k d) : Prop :=
  Stable N cuts R v δ x ∧ v.1.val < x.1.val ∧ Stops N cuts R v δ x

def TerminalFallback {k n d : ℕ} (N : ℕ) (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) (δ : ℝ) (x : Prefix k d) : Prop :=
  Stable N cuts R v δ x ∧ ¬ Stops N cuts R v δ x

def FullCylinder {k n d : ℕ} (cuts : Cuts k n d) (R : Finset (Fin n))
    (v : Prefix k d) : Set (Prefix k d) :=
  {w | Legal cuts R w ∧ w.1.val = d ∧ IsPrefix v w}

theorem anchoredMean_antitone {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {x y : Prefix k d} (hxy : IsPrefix x y) :
    anchoredMean cuts R y ≤ anchoredMean cuts R x := by
  exact mul_le_mul_of_nonneg_left (prefixMass_antitone cuts hn hxy) (Nat.cast_nonneg _)

theorem legal_prefix {k n d : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (R : Finset (Fin n)) {x y : Prefix k d} (hy : Legal cuts R y) (hxy : IsPrefix x y) :
    Legal cuts R x := lt_of_lt_of_le hy (anchoredMean_antitone cuts hn R hxy)

theorem meanExponent_antitone {k n d : ℕ} (N : ℕ) (hN : 1 < N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Finset (Fin n)) {x y : Prefix k d}
    (hy : Legal cuts R y) (hxy : IsPrefix x y) :
    meanExponent N cuts R y ≤ meanExponent N cuts R x := by
  apply div_le_div_of_nonneg_right
  · exact Real.log_le_log hy (anchoredMean_antitone cuts hn R hxy)
  · exact le_of_lt (Real.log_pos (by exact_mod_cast hN))

end RiffleUpperV2.Localization
